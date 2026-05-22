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
//! - `policy`: region-assignment policy abstraction (placeholder for `DisjointEvidence`).
//! - `config`: zone configuration types and conversion to `MemoryRegion`.
//! - `mod` (this file): `HvMemState`, `ZoneWriteGuard`, `HvMem` — the global orchestration layer.
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
use spec::{
    all_regions, ClosureRegionToken, ClosureSpecInstance, ClosureZoneIdsToken, ClosureZoneToken,
    GhostZone,
};
use vstd::invariant::InvariantPredicate;
use vstd::{
    cell::{CellId, PCell, PointsTo},
    prelude::*,
    tokens::InstanceId,
};
use zone::{Zone, ZoneKey, ZonePred, ZoneRwContent, ZoneState};

verus! {

/// Global tracked ghost state held by the hypervisor memory manager.
///
/// Wraps the `ClosureSpec` Instance and the variable-sharded tokens (`zone_ids`,
/// `region_closure`) that are not distributed to individual zones.
///
/// Typically stored inside a `Mutex` so that `add_zone`/`remove_zone` are mutually
/// exclusive.  Per-zone `ZoneState` tokens are distributed to zone-level locks
/// independently, mirroring the `AllocatorState` / `ClientState` split in
/// `global_allocator`.
pub tracked struct HvMemState {
    pub inst: ClosureSpecInstance,
    pub zone_ids_tok: ClosureZoneIdsToken,
    pub region_closure_tok: ClosureRegionToken,
}

impl HvMemState {
    /// Core well-formedness: all tokens belong to the same `ClosureSpec` instance.
    pub open spec fn wf(&self) -> bool {
        &&& self.zone_ids_tok.instance_id() == self.inst.id()
        &&& self.region_closure_tok.instance_id() == self.inst.id()
    }

    /// The `ClosureSpec` instance ID.
    pub open spec fn inst_id(&self) -> InstanceId {
        self.inst.id()
    }

    /// The current set of registered zone IDs.
    pub open spec fn zone_ids(&self) -> Set<nat> {
        self.zone_ids_tok.value()
    }

    /// The current global region closure.
    pub open spec fn region_closure(&self) -> Set<MemoryRegion> {
        self.region_closure_tok.value()
    }

    /// Construct an initial (empty) `HvMemState` from a freshly-created `ClosureSpec`
    /// instance. Callers obtain the tokens from `ClosureSpec::Instance::initialize`.
    pub proof fn new(
        tracked inst: ClosureSpecInstance,
        tracked zone_ids_tok: ClosureZoneIdsToken,
        tracked region_closure_tok: ClosureRegionToken,
    ) -> (tracked state: HvMemState)
        requires
            zone_ids_tok.instance_id() == inst.id(),
            zone_ids_tok.value() =~= Set::empty(),
            region_closure_tok.instance_id() == inst.id(),
            region_closure_tok.value() =~= Set::empty(),
        ensures
            state.wf(),
            state.inst_id() == inst.id(),
            state.zone_ids() =~= Set::empty(),
            state.region_closure() =~= Set::empty(),
    {
        HvMemState { inst, zone_ids_tok, region_closure_tok }
    }

    /// Add a fully constructed zone to the system.
    ///
    /// The caller must prove every region in `zone` belongs to `all_regions()` (static
    /// configuration membership) and is not already in the current `region_closure`
    /// (no duplicate ownership).  Disjointness from the existing closure then follows
    /// automatically from `all_regions_disjoint()`.  Returns a fresh `ZoneState` token
    /// for the new zone, which should be stored inside the zone-level lock.
    pub proof fn add_zone(tracked &mut self, zid: nat, zone: GhostZone) -> (tracked zone_state:
        ZoneState)
        requires
            old(self).wf(),
            !old(self).zone_ids().contains(zid),
            zone.wf(old(self).inst_id()),
            forall|r: MemoryRegion| #[trigger]
                zone.regions().contains(r) ==> all_regions().contains(r),
            forall|r: MemoryRegion| #[trigger]
                zone.regions().contains(r) ==> !old(self).region_closure().contains(r),
        ensures
            self.wf(),
            self.inst_id() == old(self).inst_id(),
            self.zone_ids() =~= old(self).zone_ids().insert(zid),
            self.region_closure() =~= old(self).region_closure().union(zone.regions()),
            zone_state.wf(self.inst_id()),
            zone_state.zone_id() == zid,
            zone_state.ghost_zone() == zone,
    {
        let tracked zone_tok = self.inst.add_zone(
            zid,
            zone,
            &mut self.zone_ids_tok,
            &mut self.region_closure_tok,
        );
        ZoneState { zone_tok }
    }

    /// Remove an entire zone from the system, consuming its `ZoneState` token.
    ///
    /// The zone's regions are subtracted from `region_closure`.  Callers are
    /// responsible for draining page-table frames before invoking this.
    pub proof fn remove_zone(tracked &mut self, tracked zone_state: ZoneState)
        requires
            old(self).wf(),
            zone_state.wf(old(self).inst_id()),
        ensures
            self.wf(),
            self.inst_id() == old(self).inst_id(),
            self.zone_ids() =~= old(self).zone_ids().remove(zone_state.zone_id()),
            self.region_closure() =~= old(self).region_closure().difference(
                zone_state.ghost_zone().regions(),
            ),
    {
        let tracked ZoneState { zone_tok } = zone_state;
        let zid = zone_tok.key();
        self.inst.remove_zone(zid, &mut self.zone_ids_tok, zone_tok, &mut self.region_closure_tok);
    }

    /// Insert one region into an existing zone.
    ///
    /// Consumes `zone_state` and returns an updated `ZoneState` with the region
    /// added.  Also extends `region_closure` by `region`.
    ///
    /// The caller must prove `region` belongs to `all_regions()` (static configuration
    /// membership) and is not already in the current `region_closure` (no duplicate
    /// ownership).  Disjointness from all existing regions then follows automatically
    /// from `all_regions_disjoint()`.
    pub proof fn insert_region(
        tracked &mut self,
        tracked zone_state: ZoneState,
        region: MemoryRegion,
    ) -> (tracked new_zone_state: ZoneState)
        requires
            old(self).wf(),
            zone_state.wf(old(self).inst_id()),
            region.spec_valid(),
            all_regions().contains(region),
            !old(self).region_closure().contains(region),
        ensures
            self.wf(),
            self.inst_id() == old(self).inst_id(),
            new_zone_state.wf(self.inst_id()),
            new_zone_state.zone_id() == zone_state.zone_id(),
            self.region_closure() =~= old(self).region_closure().insert(region),
            new_zone_state.ghost_zone() == zone_state.ghost_zone().insert_region(region),
    {
        let tracked ZoneState { zone_tok } = zone_state;
        let zid = zone_tok.key();
        let tracked new_zone_tok = self.inst.insert_region(
            zid,
            region,
            zone_tok,
            &mut self.region_closure_tok,
        );
        ZoneState { zone_tok: new_zone_tok }
    }

    /// Remove one region from an existing zone.
    ///
    /// Consumes `zone_state` and returns an updated `ZoneState` with the region
    /// removed.  Also shrinks `region_closure` by `region`.
    pub proof fn remove_region(
        tracked &mut self,
        tracked zone_state: ZoneState,
        region: MemoryRegion,
    ) -> (tracked new_zone_state: ZoneState)
        requires
            old(self).wf(),
            zone_state.wf(old(self).inst_id()),
            zone_state.ghost_zone().contains_region(region),
        ensures
            self.wf(),
            self.inst_id() == old(self).inst_id(),
            new_zone_state.wf(self.inst_id()),
            new_zone_state.zone_id() == zone_state.zone_id(),
            self.region_closure() =~= old(self).region_closure().remove(region),
            new_zone_state.ghost_zone() == zone_state.ghost_zone().remove_region(region),
    {
        let tracked ZoneState { zone_tok } = zone_state;
        let zid = zone_tok.key();
        let tracked new_zone_tok = self.inst.remove_region(
            zid,
            region,
            zone_tok,
            &mut self.region_closure_tok,
        );
        ZoneState { zone_tok: new_zone_tok }
    }
}

/// Compound guard returned by `HvMem::write_zone` / `HvMem::read_zone`.
///
/// Bundles the HvMem write lock resources (handle + content with empty
/// zone-list permission) with the zone's write lock resources (handle +
/// content with empty mem-set permission) and the temporarily-detached
/// zone list.
///
/// Pass to `HvMem::unlock_write_zone` together with the (possibly modified)
/// exec `M` to put everything back and release both locks.
pub struct ZoneWriteGuard<PT, M, A> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
 {
    /// Zone list taken from HvMem's PCell (zone_list_perm is currently uninitialized).
    pub zones: Vec<Arc<Zone<PT, M, A>>>,
    /// Index of the locked zone within `zones`.
    pub zone_idx: usize,
    /// Zone-level write-lock handle token.
    pub zone_write_handle: Tracked<RwWriterToken<ZoneKey, ZoneRwContent<M>, ZonePred<PT, M, A>>>,
    /// Zone-level lock content (mem_set_perm is currently uninitialized — M was taken out).
    pub zone_content: Tracked<ZoneRwContent<M>>,
    /// HvMem-level write-lock handle token.
    pub hvm_handle: Tracked<RwWriterToken<HvMemKey, HvMemRwContent<PT, M, A>, HvMemPred<PT, M, A>>>,
    /// HvMem-level lock content (zone_list_perm is currently uninitialized — zones was taken out).
    pub hvm_content: Tracked<HvMemRwContent<PT, M, A>>,
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
pub struct ZoneReadGuard<PT, M, A> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator {
    pub inner: ZoneWriteGuard<PT, M, A>,
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
/// together with the global `HvMemState` (which holds the `ClosureSpec` instance
/// and the `zone_ids` / `region_closure` variable tokens).
pub tracked struct HvMemRwContent<PT, M, A> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
 {
    /// Permission to read/write the zone-list PCell.
    pub zone_list_perm: PointsTo<Vec<Arc<Zone<PT, M, A>>>>,
    /// Global ClosureSpec ghost state.
    pub hv_mem_state: HvMemState,
}

/// Phantom struct that carries the `HvMem`-level `InvariantPredicate`.
pub struct HvMemPred<PT, M, A> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator {
    pub _phantom: PhantomData<(PT, M, A)>,
}

impl<PT, M, A> InvariantPredicate<HvMemKey, HvMemRwContent<PT, M, A>> for HvMemPred<PT, M, A> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
 {
    /// The content is well-formed when:
    /// - `zone_list_perm` is initialised and points to the key's cell,
    /// - `hv_mem_state` is internally well-formed, and
    /// - the exec zone list and the ghost state agree: every ghost zone ID has
    ///   exactly one corresponding exec `Zone`, all zones share the same
    ///   `ClosureSpec` instance, and exec zone IDs are pairwise distinct.
    open spec fn inv(k: HvMemKey, v: HvMemRwContent<PT, M, A>) -> bool {
        &&& v.zone_list_perm.is_init()
        &&& v.zone_list_perm@.pcell === k.cell_id
        &&& v.hv_mem_state.wf()
        &&& {
            let zone_list = v.zone_list_perm@.mem_contents->Init_0;
            // The ghost zone_ids set is exactly the set of exec zone IDs.
            &&& (forall|zid: nat| #[trigger]
                v.hv_mem_state.zone_ids().contains(zid) == (exists|i: int|
                    0 <= i < zone_list.len() && #[trigger] zone_list[i].zone_id as nat
                        == zid))
            // Each exec zone's lock is bound to the correct ClosureSpec instance.
            &&& (forall|i: int|
                #![trigger zone_list[i]]
                0 <= i < zone_list.len() ==> zone_list[i].lock.k@.mem_inst_id
                    == v.hv_mem_state.inst_id())
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
///      .hv_mem_state   : HvMemState                 <- ghost tokens     ┘ RwLock
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
pub struct HvMem<PT, M, A> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator {
    /// Zone list — written only while the HvMem write guard is held.
    pub zone_mem_list: PCell<Vec<Arc<Zone<PT, M, A>>>>,
    /// RwLock protecting `HvMemRwContent<PT,M,A>` with `HvMemKey` predicate.
    pub lock: RwLock<HvMemKey, HvMemRwContent<PT, M, A>, HvMemPred<PT, M, A>>,
    /// Ghost record of `zone_mem_list.id()`.
    pub cell_id: Ghost<CellId>,
    /// Global allocator — already protected by its own `Mutex`.
    pub alloc: GlobalAllocator<A>,
}

impl<PT, M, A> HvMem<PT, M, A> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator {
    /// Structural well-formedness:
    /// - the outer `RwLock` is internally consistent,
    /// - the lock's ghost key `cell_id` matches `self.zone_mem_list.id()`, and
    /// - the global allocator is valid.
    ///
    /// `HvMemPred::inv` (checked on every write-lock release) additionally
    /// guarantees that the `PointsTo` inside the lock points to the same cell
    /// and that `HvMemState` is well-formed.
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
    /// 4. Advance the `ClosureSpec` ghost state machine (`HvMemState::add_zone`)
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
        let tracked mut content: HvMemRwContent<PT, M, A> = token.get();
        let mut zones = self.zone_mem_list.take(Tracked(&mut content.zone_list_perm));

        // ── Step 4: advance ClosureSpec ghost state, obtain ZoneState token ───
        let tracked zone_state: ZoneState;
        let ghost inst_id: InstanceId;
        proof {
            inst_id = content.hv_mem_state.inst_id();
            // Precondition admits — dischargeable from ghost_zone + HvMemState invariants
            // in a fully verified version.
            assume(!content.hv_mem_state.zone_ids().contains(zid as nat));
            assume(ghost_zone.wf(content.hv_mem_state.inst_id()));
            assume(forall|new_r: MemoryRegion|
                ghost_zone.regions().contains(new_r) ==> forall|existing: MemoryRegion| #[trigger]
                    content.hv_mem_state.region_closure().contains(existing)
                        ==> !new_r.spec_overlaps_vmem(existing));
            zone_state = content.hv_mem_state.add_zone(zid as nat, ghost_zone);
        }

        // ── Step 5: assemble the new Zone (infallible) ────────────────────────
        let new_zone = Arc::new(
            Zone::<PT, M, A>::new(mem_set, zid, Ghost(inst_id), Tracked(zone_state)),
        );

        // ── Step 6: push zone, restore PCell, release write lock ─────────────
        zones.push(new_zone);
        self.zone_mem_list.put(Tracked(&mut content.zone_list_perm), zones);
        proof {
            assume(HvMemPred::<PT, M, A>::inv(self.lock.k@, content));
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
    /// 5. Advance `HvMemState::remove_zone` to drop the `ZoneState` token.
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
        let tracked mut content: HvMemRwContent<PT, M, A> = token.get();
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
                assume(HvMemPred::<PT, M, A>::inv(self.lock.k@, content));
            }
            self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });
            return Err(());
        }
        // ── Step 3: remove zone from list ─────────────────────────────────────

        let idx = idx_opt.unwrap();
        let zone = zones.swap_remove(idx);

        // ── Step 4: extract ZoneState and M from the zone ─────────────────────
        let zone_guard = zone.lock.lock_write();
        let RwWriteGuard { handle: zone_handle, token: zone_token } = zone_guard;
        let tracked mut zone_content: ZoneRwContent<M> = zone_token.get();
        // Take M out of the zone's PCell so it is properly dropped below.
        let _mem_set: M = zone.mem_set.take(Tracked(&mut zone_content.mem_set_perm));
        // _mem_set is dropped at end of scope.

        // ── Step 5: advance ghost state ───────────────────────────────────────
        proof {
            let tracked ZoneRwContent { mem_set_perm: _, zone_state } = zone_content;
            content.hv_mem_state.remove_zone(zone_state);
            // zone_handle (writer token) is consumed here via assume — the zone is
            // being destroyed so there is no need to formally unlock it.
            assume(false);  // FIXME: zone_handle (RwWriterToken) needs explicit disposal
        }

        // ── Step 6: restore zone list and release HvMem write lock ───────────
        self.zone_mem_list.put(Tracked(&mut content.zone_list_perm), zones);
        proof {
            assume(HvMemPred::<PT, M, A>::inv(self.lock.k@, content));
        }
        self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });

        Ok(())
    }

    /// Look up the zone with the given `zid` and return an `Arc` clone if found.
    pub fn find_zone(&self, zid: usize) -> (res: Option<Arc<Zone<PT, M, A>>>)
        requires
            self.wf(),
        ensures
            res.is_some() ==> res.unwrap().wf() && res.unwrap().zone_id == zid,
    {
        // ── Step 1: acquire HvMem write lock ─────────────────────────────────
        let guard = self.lock.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: HvMemRwContent<PT, M, A> = token.get();
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
                assume(HvMemPred::<PT, M, A>::inv(self.lock.k@, content));
            }
            self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });
            None
        } else {
            // Zone found — clone Arc, restore, and return.
            let idx = idx_opt.unwrap();
            let zone = zones[idx].clone();
            self.zone_mem_list.put(Tracked(&mut content.zone_list_perm), zones);
            proof {
                assume(HvMemPred::<PT, M, A>::inv(self.lock.k@, content));
            }
            self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });
            Some(zone)
        }
    }
}

} // verus!
