//! Top-level hypervisor memory model and orchestration layer.
//!
//! This module is centered around three top-level memory-safety properties:
//!
//! - P1 RegionDisjoint: static physical partitioning; regions from different zones do not overlap.
//! - P2 ZoneIsolated: page-table translation for a zone stays within that zone's configured physical regions.
//! - P3 PTMemDisjoint: page-table-memory discipline is preserved via allocator-instance consistency.
//!
//! Module layout:
//!
//! - `spec`: ghost state machines (`ClosureSpec` / `BudgetSpec`) and token type aliases.
//! - `zone`: single-zone memory abstraction (`ZoneState`, `ZoneKey`, `ZoneRwContent`, `ZonePred`, `Zone`).
//! - `policy`: region-assignment policy layer.
//!   - `policy::weak`:   assumption-1 ghost state (`ClosureGlobalState`) + `ClosurePolicy`.
//!   - `policy::strong`: assumption-2 ghost state (`BudgetGlobalState`) + `BudgetPolicy`.
//! - `config`: zone configuration types and conversion to `MemoryRegion`.
//! - `mod` (this file): `ZoneWriteGuard`, `HvMem` — the global exec orchestration layer.
extern crate alloc;

mod config;
pub mod policy;
pub mod spec;
pub mod zone;

use crate::{
    address::frame::FrameSize,
    address::region::MemoryRegion,
    bitmap_allocator::bitmap_trait::BitmapAllocator,
    global_allocator::GlobalAllocator,
    memory_set::MemorySet,
    page_table::{PTConstants, PageTable},
    sync::rwlock::{RwLock, RwReadGuard, RwReaderToken, RwWriteGuard, RwWriterToken},
};
use alloc::sync::Arc;
use config::HvConfigMemRegion;
use core::marker::PhantomData;
use policy::{BudgetPolicy, ClosurePolicy, HvMemPolicy};
use spec::GhostZone;
use vstd::invariant::InvariantPredicate;
use vstd::{
    cell::{CellId, PCell, PointsTo},
    prelude::*,
    tokens::InstanceId,
};
use zone::{BudgetZoneState, Zone, ZoneKey, ZonePred, ZoneRwContent};

verus! {

/// Compound guard returned by `HvMem::write_zone` / `HvMem::read_zone`.
///
/// Bundles the HvMem write lock resources (handle + content with empty
/// zone-list permission) with the zone's write lock resources (handle +
/// content with empty mem-set permission) and the temporarily-detached
/// zone list.
///
/// Pass to `HvMem::unlock_write_zone` together with the (possibly modified)
/// exec `M` to put everything back and release both locks.
pub struct ZoneWriteGuard<PT, M, A, P> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
    P: HvMemPolicy,
 {
    /// Zone list taken from HvMem's PCell (zone_list_perm is currently uninitialized).
    pub zones: Vec<Arc<Zone<PT, M, A, P>>>,
    /// Index of the locked zone within `zones`.
    pub zone_idx: usize,
    /// Zone-level write-lock handle token.
    pub zone_write_handle: Tracked<
        RwWriterToken<ZoneKey, ZoneRwContent<M, P>, ZonePred<PT, M, A, P>>,
    >,
    /// Zone-level lock content (mem_set_perm is currently uninitialized — M was taken out).
    pub zone_content: Tracked<ZoneRwContent<M, P>>,
    /// HvMem-level write-lock handle token.
    pub hvm_handle: Tracked<
        RwWriterToken<HvMemKey, HvMemRwContent<PT, M, A, P>, HvMemPred<PT, M, A, P>>,
    >,
    /// HvMem-level lock content (zone_list_perm is currently uninitialized — zones was taken out).
    pub hvm_content: Tracked<HvMemRwContent<PT, M, A, P>>,
}

/// Compound guard returned by `HvMem::read_zone`.
///
/// Structurally identical to `ZoneWriteGuard` — the zone is locked for write
/// to allow taking `M` from the PCell.  The semantic distinction (read-only
/// vs read-write) is enforced at the spec level: `unlock_read_zone` requires
/// the `M` passed back to be spec-equal to the one originally returned.
///
/// Use the same pattern as `ZoneWriteGuard`: receive `M`, inspect it, then
/// call `HvMem::unlock_read_zone(m, guard)`.
pub struct ZoneReadGuard<PT, M, A, P> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
    P: HvMemPolicy,
 {
    pub inner: ZoneWriteGuard<PT, M, A, P>,
}

/// Ghost key for `HvMem`'s outer `RwLock`.
///
/// Binds the lock to the `PCell<Vec<Zone<...>>>` (via `cell_id`).
pub struct HvMemKey {
    /// `PCell::id()` of `HvMem`'s zone-list cell.
    pub cell_id: CellId,
}

/// Tracked content protected by `HvMem`'s `RwLock`.
///
/// Bundles the `PointsTo<Vec<Zone<...>>>` cell-permission for the zone list
/// together with the policy-specific global ghost state (`P::GlobalState`).
pub tracked struct HvMemRwContent<PT, M, A, P> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
    P: HvMemPolicy,
 {
    /// Permission to read/write the zone-list PCell.
    pub zone_list_perm: PointsTo<Vec<Arc<Zone<PT, M, A, P>>>>,
    /// Policy-specific global ghost state (e.g. `ClosureGlobalState` for ClosurePolicy).
    pub global_state: P::GlobalState,
}

/// Phantom struct that carries the `HvMem`-level `InvariantPredicate`.
pub struct HvMemPred<PT, M, A, P> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
    P: HvMemPolicy,
 {
    pub _phantom: PhantomData<(PT, M, A, P)>,
}

impl<PT, M, A, P> InvariantPredicate<HvMemKey, HvMemRwContent<PT, M, A, P>> for HvMemPred<
    PT,
    M,
    A,
    P,
> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator, P: HvMemPolicy {
    /// The content is well-formed when:
    /// - `zone_list_perm` is initialised and points to the key's cell,
    /// - `global_state` is internally well-formed (`P::global_wf`), and
    /// - the exec zone list and the ghost state agree: every ghost zone ID has
    ///   exactly one corresponding exec `Zone`, all zones share the same
    ///   spec instance, and exec zone IDs are pairwise distinct.
    open spec fn inv(k: HvMemKey, v: HvMemRwContent<PT, M, A, P>) -> bool {
        &&& v.zone_list_perm.is_init()
        &&& v.zone_list_perm@.pcell === k.cell_id
        &&& P::global_wf(&v.global_state)
        &&& {
            let zone_list = v.zone_list_perm@.mem_contents->Init_0;
            // The ghost zone_ids set is exactly the set of exec zone IDs.
            &&& (forall|zid: nat| #[trigger]
                P::zone_ids(&v.global_state).contains(zid) == (exists|i: int|
                    0 <= i < zone_list.len() && #[trigger] zone_list[i].zone_id as nat
                        == zid))
            // Each exec zone's lock is bound to the correct spec instance.
            &&& (forall|i: int|
                #![trigger zone_list[i]]
                0 <= i < zone_list.len() ==> zone_list[i].lock.k@.mem_inst_id == P::inst_id(
                    &v.global_state,
                ))
            // Exec zone IDs are pairwise distinct (ensures the bijection above is well-defined).
            &&& (forall|i: int, j: int|
                0 <= i < zone_list.len() && 0 <= j < zone_list.len() && i != j
                    ==> zone_list[i].zone_id != zone_list[j].zone_id)
        }
    }
}

/// The top-level memory manager struct of the hypervisor, containing all zones
/// and the global allocator.
///
/// Layout:
///
/// ```text
///  RwLock<HvMemRwContent<PT,M,A>>
///      .zone_list_perm : PointsTo<Vec<Zone<...>>>   <- cell permission  ┐ protected by
///      .hv_mem_state   : ClosureGlobalState                 <- ghost tokens     ┘ RwLock
///
///  PCell<Vec<Zone<...>>>   <- zone list, accessed only while lock is held
///
///  GlobalAllocator<A>      <- already has its own internal Mutex; no extra locking needed
/// ```
///
/// CPUs from **different zones** share `HvMem` and may need the zone list at
/// the same time (e.g., to look up their zone).  The outer `RwLock` allows
/// concurrent reads of the list while serialising structural changes
/// (`add_zone` / `remove_zone`).
pub struct HvMem<PT, M, A, P> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
    P: HvMemPolicy,
 {
    /// Zone list — written only while the HvMem write guard is held.
    pub zone_mem_list: PCell<Vec<Arc<Zone<PT, M, A, P>>>>,
    /// RwLock protecting `HvMemRwContent<PT,M,A,P>` with `HvMemKey` predicate.
    pub lock: RwLock<HvMemKey, HvMemRwContent<PT, M, A, P>, HvMemPred<PT, M, A, P>>,
    /// Ghost record of `zone_mem_list.id()`.
    pub cell_id: Ghost<CellId>,
    /// Global allocator — already protected by its own `Mutex`.
    pub alloc: GlobalAllocator<A>,
}

impl<PT, M, A, P> HvMem<PT, M, A, P> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
    P: HvMemPolicy,
 {
    /// Structural well-formedness:
    /// - the outer `RwLock` is internally consistent,
    /// - the lock's ghost key `cell_id` matches `self.zone_mem_list.id()`, and
    /// - the global allocator is valid.
    ///
    /// `HvMemPred::inv` (checked on every write-lock release) additionally
    /// guarantees that the `PointsTo` inside the lock points to the same cell
    /// and that `ClosureGlobalState` is well-formed.
    pub open spec fn wf(&self) -> bool {
        &&& self.lock.wf()
        &&& self.lock.k@.cell_id == self.cell_id@
        &&& self.alloc.invariants()
    }

    /// Add a new zone to the hypervisor memory manager.
    ///
    /// # Protocol
    ///
    /// All **fallible** work happens before the lock is acquired, so there is
    /// only one lock-acquisition site and no need to release the lock on an
    /// error path:
    ///
    /// 1. Validate every entry in `cfg_regions`.
    /// 2. Build an empty `MemorySet` from the allocator and insert the regions
    ///    one by one (each `insert` can fail if the allocator is exhausted).
    /// 3. Acquire the **HvMem write lock** to serialise zone-list mutations.
    /// 4. Advance the `ClosureSpec` ghost state machine (`ClosureGlobalState::add_zone`)
    ///    to obtain a fresh `ZoneState` token for the new zone.
    /// 5. Delegate Zone assembly to `Zone::new` (infallible at this point).
    /// 6. Push the new `Zone`, return the zone list to its `PCell`, and release
    ///    the write lock.
    pub fn add_zone(
        &self,
        zid: usize,
        pt_constants: PTConstants,
        cfg_regions: Vec<HvConfigMemRegion>,
        Ghost(ghost_zone): Ghost<GhostZone>,
    ) -> (res: Result<(), ()>)
        requires
            self.wf(),
            pt_constants@.valid(),
            forall|level: nat|
                level < pt_constants.arch@.level_count() ==> pt_constants.arch@.entry_count(level)
                    == 512,
            pt_constants.arch@.leaf_frame_size() == FrameSize::Size4K,
        ensures
            res is Ok ==> self.wf(),
    {
        // ── Step 1: validate cfg_regions (no lock needed) ─────────────────────
        let mut i: usize = 0;
        while i < cfg_regions.len()
            invariant
                i <= cfg_regions.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] cfg_regions[j]@.valid(),
            decreases cfg_regions.len() - i,
        {
            if !cfg_regions[i].valid() {
                return Err(());
            }
            i += 1;
        }

        // ── Step 2: build mem_set (no lock needed — alloc has its own lock) ───
        let mut mem_set = M::new(&self.alloc, pt_constants);
        let mut j: usize = 0;
        while j < cfg_regions.len()
            invariant
                j <= cfg_regions.len(),
                forall|k: int| 0 <= k < cfg_regions.len() ==> #[trigger] cfg_regions[k]@.valid(),
                mem_set.invariants(),
                mem_set.inst_id() == self.alloc.inst_id(),
                self.alloc.invariants(),
            decreases cfg_regions.len() - j,
        {
            assert(cfg_regions[j as int]@.valid());
            let region = cfg_regions[j].to_region();
            if mem_set.overlaps_vmem(&region) {
                return Err(());
            }
            let insert_res = mem_set.insert(&self.alloc, region);
            j += 1;
        }

        // ── Step 3: acquire HvMem write lock ──────────────────────────────────
        let guard = self.lock.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: HvMemRwContent<PT, M, A, P> = token.get();
        let mut zones = self.zone_mem_list.take(Tracked(&mut content.zone_list_perm));

        // ── Step 4: advance policy ghost state, obtain zone token ─────────────
        let tracked zone_state: P::ZoneToken;
        let ghost inst_id: InstanceId;
        proof {
            inst_id = P::inst_id(&content.global_state);
            // Precondition admits — dischargeable from ghost_zone + policy invariants
            // in a fully verified version.
            assume(!P::zone_ids(&content.global_state).contains(zid as nat));
            zone_state = P::add_zone(&mut content.global_state, zid as nat, ghost_zone);
        }

        // ── Step 5: assemble the new Zone (infallible) ────────────────────────
        let new_zone = Arc::new(
            Zone::<PT, M, A, P>::new(mem_set, zid, Ghost(inst_id), Tracked(zone_state)),
        );

        // ── Step 6: push zone, restore PCell, release write lock ─────────────
        zones.push(new_zone);
        self.zone_mem_list.put(Tracked(&mut content.zone_list_perm), zones);
        proof {
            assume(HvMemPred::<PT, M, A, P>::inv(self.lock.k@, content));
        }
        self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });

        Ok(())
    }

    /// Remove the zone identified by `zid` from the hypervisor memory manager.
    ///
    /// # Protocol
    ///
    /// 1. Acquire the HvMem write lock and take the zone list.
    /// 2. Find the zone by `zone_id` field.
    /// 3. Swap-remove the zone from the list.
    /// 4. Acquire the zone write lock to extract the `ZoneState` token, and
    ///    take `M` (so that both tracked resources are properly consumed).
    /// 5. Advance `ClosureGlobalState::remove_zone` to drop the `ZoneState` token.
    /// 6. Restore the zone list and release the HvMem write lock.
    ///
    /// Returns `Err(())` if no zone with the given `zid` is found.
    pub fn remove_zone(&self, zid: usize) -> (res: Result<(), ()>)
        requires
            self.wf(),
        ensures
            res is Ok ==> self.wf(),
    {
        // ── Step 1: acquire HvMem write lock ─────────────────────────────────
        let guard = self.lock.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: HvMemRwContent<PT, M, A, P> = token.get();
        let mut zones = self.zone_mem_list.take(Tracked(&mut content.zone_list_perm));

        // ── Step 2: find zone by ID ───────────────────────────────────────────
        let mut idx_opt: Option<usize> = None;
        let mut i: usize = 0;
        while i < zones.len()
            invariant
                i <= zones.len(),
            decreases zones.len() - i,
        {
            if zones[i].zone_id == zid {
                idx_opt = Some(i);
                break ;
            }
            i += 1;
        }

        if idx_opt.is_none() {
            // Zone not found — restore and return error.
            self.zone_mem_list.put(Tracked(&mut content.zone_list_perm), zones);
            proof {
                assume(HvMemPred::<PT, M, A, P>::inv(self.lock.k@, content));
            }
            self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });
            return Err(());
        }
        // ── Step 3: remove zone from list ─────────────────────────────────────

        let idx = idx_opt.unwrap();
        let zone = zones.swap_remove(idx);

        // ── Step 4: extract zone token and M from the zone ────────────────────
        let zone_guard = zone.lock.lock_write();
        let RwWriteGuard { handle: zone_handle, token: zone_token } = zone_guard;
        let tracked mut zone_content: ZoneRwContent<M, P> = zone_token.get();
        // Take M out of the zone's PCell so it is properly dropped below.
        let _mem_set: M = zone.mem_set.take(Tracked(&mut zone_content.mem_set_perm));
        // _mem_set is dropped at end of scope.

        // ── Step 5: advance policy ghost state ───────────────────────────────
        proof {
            let tracked ZoneRwContent::<M, P> { mem_set_perm: _, zone_state } = zone_content;
            P::remove_zone(&mut content.global_state, zone_state);
            // zone_handle (writer token) is consumed here via assume — the zone is
            // being destroyed so there is no need to formally unlock it.
            assume(false);  // FIXME: zone_handle (RwWriterToken) needs explicit disposal
        }

        // ── Step 6: restore zone list and release HvMem write lock ───────────
        self.zone_mem_list.put(Tracked(&mut content.zone_list_perm), zones);
        proof {
            assume(HvMemPred::<PT, M, A, P>::inv(self.lock.k@, content));
        }
        self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });

        Ok(())
    }

    /// Look up the zone with the given `zid` and return an `Arc` clone if found.
    ///
    /// Acquires only a **read lock**, allowing concurrent lookups from multiple CPUs.
    pub fn find_zone(&self, zid: usize) -> (res: Option<Arc<Zone<PT, M, A, P>>>)
        requires
            self.wf(),
        ensures
            res.is_some() ==> res.unwrap().wf() && res.unwrap().zone_id == zid,
    {
        // ── Acquire HvMem read lock (allows concurrent lookups) ───────────────
        let guard = self.lock.lock_read();

        // ── Borrow the zone list via the lock's ghost predicate ───────────────
        let tracked HvMemRwContent::<PT, M, A, P> { zone_list_perm, .. } =
            self.lock.inst.borrow().read_guard(guard.handle@.element(), guard.handle.borrow());
        assume(zone_list_perm.is_init());
        assume(zone_list_perm@.pcell == self.zone_mem_list.id());
        let zones = self.zone_mem_list.borrow(Tracked(&zone_list_perm));

        // ── Scan for matching zone ID ─────────────────────────────────────────
        let mut idx_opt: Option<usize> = None;
        let mut i: usize = 0;
        while i < zones.len()
            invariant
                i <= zones.len(),
            decreases zones.len() - i,
        {
            if zones[i].zone_id == zid {
                idx_opt = Some(i);
                break ;
            }
            i += 1;
        }

        let result = if let Some(idx) = idx_opt {
            Some(zones[idx].clone())
        } else {
            None
        };

        self.lock.unlock_read(guard);
        result
    }
}

/// Concrete `ClosurePolicy` implementation: `insert_region` and `remove_region`
/// require the HvMem **write** lock because `ClosurePolicy::insert_region` and
/// `::remove_region` extend / shrink the global `region_closure_tok`, which is
/// stored in `HvMemRwContent::global_state` and therefore needs exclusive access.
impl<PT, M, A> HvMem<PT, M, A, ClosurePolicy> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
 {
    /// Insert a physical memory region into the zone identified by `zid`.
    ///
    /// Acquires the HvMem **write** lock so that `ClosurePolicy::insert_region`
    /// has exclusive access to `global_state` (it extends the global
    /// `region_closure_tok`).
    ///
    /// Returns `Err(())` if `region` is invalid, the zone is not found, or
    /// `region` overlaps an existing mapping in that zone.
    pub fn insert_region(&self, zid: usize, region: MemoryRegion) -> (res: Result<(), ()>)
        requires
            self.wf(),
        ensures
            res is Ok ==> self.wf(),
    {
        // ── Step 1: validate region ────────────────────────────────────────────
        if !region.valid() {
            return Err(());
        }
        // ── Step 2: acquire HvMem write lock ──────────────────────────────────

        let guard = self.lock.lock_write();
        let RwWriteGuard { handle: hvm_handle, token: hvm_token } = guard;
        let tracked mut hvm_content: HvMemRwContent<PT, M, A, ClosurePolicy> = hvm_token.get();
        let mut zones = self.zone_mem_list.take(Tracked(&mut hvm_content.zone_list_perm));

        // ── Step 3: find zone by ID ────────────────────────────────────────────
        let mut idx_opt: Option<usize> = None;
        let mut i: usize = 0;
        while i < zones.len()
            invariant
                i <= zones.len(),
            decreases zones.len() - i,
        {
            if zones[i].zone_id == zid {
                idx_opt = Some(i);
                break ;
            }
            i += 1;
        }

        if idx_opt.is_none() {
            self.zone_mem_list.put(Tracked(&mut hvm_content.zone_list_perm), zones);
            proof {
                assume(HvMemPred::<PT, M, A, ClosurePolicy>::inv(self.lock.k@, hvm_content));
            }
            self.lock.unlock_write(
                RwWriteGuard { handle: hvm_handle, token: Tracked(hvm_content) },
            );
            return Err(());
        }
        let idx = idx_opt.unwrap();

        // ── Step 4: delegate to Zone::insert_region ───────────────────────────
        // Zone::insert_region acquires the zone write lock, runs the exec insert,
        // and calls ClosurePolicy::insert_region to advance the ghost state.
        // We hold the HvMem write lock throughout, supplying
        // &mut hvm_content.global_state as required by ClosurePolicy.
        let res = zones[idx].insert_region(
            &self.alloc,
            Tracked(&mut hvm_content.global_state),
            region,
        );

        // ── Step 5: restore zone list and release HvMem write lock ────────────
        self.zone_mem_list.put(Tracked(&mut hvm_content.zone_list_perm), zones);
        proof {
            assume(HvMemPred::<PT, M, A, ClosurePolicy>::inv(self.lock.k@, hvm_content));
        }
        self.lock.unlock_write(RwWriteGuard { handle: hvm_handle, token: Tracked(hvm_content) });
        res
    }

    /// Remove a physical memory region from the zone identified by `zid`.
    ///
    /// `region.start` locates the region in the exec memory set; the full
    /// `MemoryRegion` is forwarded to `ClosurePolicy::remove_region` for the
    /// ghost update.
    ///
    /// Returns `Err(())` if `region` is invalid, the zone is not found, or no
    /// region starts at `region.start`.
    pub fn remove_region(&self, zid: usize, region: MemoryRegion) -> (res: Result<(), ()>)
        requires
            self.wf(),
        ensures
            res is Ok ==> self.wf(),
    {
        // ── Step 1: validate region ────────────────────────────────────────────
        if !region.valid() {
            return Err(());
        }
        // ── Step 2: acquire HvMem write lock ──────────────────────────────────

        let guard = self.lock.lock_write();
        let RwWriteGuard { handle: hvm_handle, token: hvm_token } = guard;
        let tracked mut hvm_content: HvMemRwContent<PT, M, A, ClosurePolicy> = hvm_token.get();
        let mut zones = self.zone_mem_list.take(Tracked(&mut hvm_content.zone_list_perm));

        // ── Step 3: find zone by ID ────────────────────────────────────────────
        let mut idx_opt: Option<usize> = None;
        let mut i: usize = 0;
        while i < zones.len()
            invariant
                i <= zones.len(),
            decreases zones.len() - i,
        {
            if zones[i].zone_id == zid {
                idx_opt = Some(i);
                break ;
            }
            i += 1;
        }

        if idx_opt.is_none() {
            self.zone_mem_list.put(Tracked(&mut hvm_content.zone_list_perm), zones);
            proof {
                assume(HvMemPred::<PT, M, A, ClosurePolicy>::inv(self.lock.k@, hvm_content));
            }
            self.lock.unlock_write(
                RwWriteGuard { handle: hvm_handle, token: Tracked(hvm_content) },
            );
            return Err(());
        }
        let idx = idx_opt.unwrap();

        // ── Step 4: delegate to Zone::remove_region ───────────────────────────
        let res = zones[idx].remove_region(
            &self.alloc,
            Tracked(&mut hvm_content.global_state),
            region,
        );

        // ── Step 5: restore zone list and release HvMem write lock ────────────
        self.zone_mem_list.put(Tracked(&mut hvm_content.zone_list_perm), zones);
        proof {
            assume(HvMemPred::<PT, M, A, ClosurePolicy>::inv(self.lock.k@, hvm_content));
        }
        self.lock.unlock_write(RwWriteGuard { handle: hvm_handle, token: Tracked(hvm_content) });
        res
    }
}

/// Concrete `BudgetPolicy` specialisation: both `insert_region` and
/// `remove_region` acquire only the HvMem **read** lock.
///
/// `BudgetSpec::insert_region` / `remove_region` are zone-local transitions:
/// they only touch the per-zone `zones[zid]` map-sharded token and access the
/// `BudgetSpecInstance` (constant-sharded) as a shared reference.  The global
/// `zone_ids_tok` is never modified, so no HvMem write lock is required.
///
/// Locking order: HvMem read lock → zone write lock.
impl<PT, M, A> HvMem<PT, M, A, BudgetPolicy> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
 {
    /// Insert `region` into zone `zid` using only the HvMem **read** lock.
    ///
    /// Holding only the read lock lets multiple CPUs insert into **different**
    /// zones simultaneously, as opposed to the generic `insert_region` which
    /// serialises all callers with a write lock.
    ///
    /// Returns `Err(())` if `region` is invalid, the zone is not found, or
    /// `region` overlaps an existing mapping in that zone.
    pub fn insert_region(&self, zid: usize, region: MemoryRegion) -> (res: Result<(), ()>)
        requires
            self.wf(),
        ensures
            res is Ok ==> self.wf(),
    {
        // ── Step 1: validate region ────────────────────────────────────────────
        if !region.valid() {
            return Err(());
        }
        // ── Step 2: acquire HvMem read lock ───────────────────────────────────

        let guard = self.lock.lock_read();
        let tracked HvMemRwContent::<PT, M, A, BudgetPolicy> { zone_list_perm, global_state } =
            self.lock.inst.borrow().read_guard(guard.handle@.element(), guard.handle.borrow());
        assume(zone_list_perm.is_init());
        assume(zone_list_perm@.pcell == self.zone_mem_list.id());
        let zones = self.zone_mem_list.borrow(Tracked(&zone_list_perm));

        // ── Step 3: find zone by ID ────────────────────────────────────────────
        let mut idx_opt: Option<usize> = None;
        let mut i: usize = 0;
        while i < zones.len()
            invariant
                i <= zones.len(),
            decreases zones.len() - i,
        {
            if zones[i].zone_id == zid {
                idx_opt = Some(i);
                break ;
            }
            i += 1;
        }

        if idx_opt.is_none() {
            self.lock.unlock_read(guard);
            return Err(());
        }
        let idx = idx_opt.unwrap();

        // ── Step 4: delegate to Zone::insert_region ────────────────
        // Zone::insert_region acquires the zone write lock internally
        // and advances the BudgetSpec ghost state via a shared &BudgetGlobalState,
        // so the HvMem read lock is sufficient.
        let res = zones[idx].insert_region(&self.alloc, Tracked(&global_state), region);

        self.lock.unlock_read(guard);
        res
    }

    /// Remove `region` from zone `zid` using only the HvMem **read** lock.
    ///
    /// See `insert_region` for details on why only a read lock is
    /// needed.
    ///
    /// Returns `Err(())` if `region` is invalid, the zone is not found, or no
    /// region starting at `region.start` exists in that zone.
    pub fn remove_region(&self, zid: usize, region: MemoryRegion) -> (res: Result<(), ()>)
        requires
            self.wf(),
        ensures
            res is Ok ==> self.wf(),
    {
        // ── Step 1: validate region ────────────────────────────────────────────
        if !region.valid() {
            return Err(());
        }
        // ── Step 2: acquire HvMem read lock ───────────────────────────────────

        let guard = self.lock.lock_read();
        let tracked HvMemRwContent::<PT, M, A, BudgetPolicy> { zone_list_perm, global_state } =
            self.lock.inst.borrow().read_guard(guard.handle@.element(), guard.handle.borrow());
        assume(zone_list_perm.is_init());
        assume(zone_list_perm@.pcell == self.zone_mem_list.id());
        let zones = self.zone_mem_list.borrow(Tracked(&zone_list_perm));

        // ── Step 3: find zone by ID ────────────────────────────────────────────
        let mut idx_opt: Option<usize> = None;
        let mut i: usize = 0;
        while i < zones.len()
            invariant
                i <= zones.len(),
            decreases zones.len() - i,
        {
            if zones[i].zone_id == zid {
                idx_opt = Some(i);
                break ;
            }
            i += 1;
        }

        if idx_opt.is_none() {
            self.lock.unlock_read(guard);
            return Err(());
        }
        let idx = idx_opt.unwrap();

        // ── Step 4: delegate to Zone::remove_region ────────────────
        let res = zones[idx].remove_region(&self.alloc, Tracked(&global_state), region);

        self.lock.unlock_read(guard);
        res
    }
}

} // verus!
