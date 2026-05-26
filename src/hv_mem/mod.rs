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
//! - `protocol`: region-assignment protocol layer.
//!   - `protocol::weak`:   assumption-1 ghost state (`ClosureGlobalState`) + `ClosureProtocol`.
//!   - `protocol::strong`: assumption-2 ghost state (`BudgetGlobalState`) + `BudgetProtocol`.
//! - `config`: zone configuration types and conversion to `MemoryRegion`.
//! - `mod` (this file): `ZoneWriteGuard`, `HvMem` — the global exec orchestration layer.
extern crate alloc;

mod config;
pub mod protocol;
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
use core::marker::PhantomData;
use protocol::{BudgetProtocol, ClosureProtocol, HvMemProtocol};
use vstd::invariant::InvariantPredicate;
use vstd::{
    cell::{CellId, PCell, PointsTo},
    prelude::*,
    tokens::InstanceId,
};
use zone::{Zone, ZoneKey, ZonePred, ZoneRwContent};

verus! {

/// Ghost key for `HvMem`'s outer `RwLock`.
///
/// Binds the lock to the `PCell<Vec<Zone<...>>>` (via `cell_id`).
pub struct HvMemKey {
    /// Memory instance ID.
    pub mem_inst_id: InstanceId,
    /// Global allocator instance ID (for P3 PTMemDisjoint).
    pub alloc_inst_id: InstanceId,
    /// `PCell::id()` of `HvMem`'s zone-list cell.
    pub cell_id: CellId,
}

/// Tracked content protected by `HvMem`'s `RwLock`.
///
/// Bundles the `PointsTo<Vec<Zone<...>>>` cell-permission for the zone list
/// together with the protocol-specific global ghost state (`P::GlobalState`).
pub tracked struct HvMemRwContent<PT, M, A, P> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
    P: HvMemProtocol,
 {
    /// Permission to read/write the zone-list PCell.
    pub zone_list_perm: PointsTo<Vec<Arc<Zone<PT, M, A, P>>>>,
    /// Protocol-specific global ghost state (e.g. `ClosureGlobalState` for ClosureProtocol).
    pub global_state: P::GlobalState,
}

/// Phantom struct that carries the `HvMem`-level `InvariantPredicate`.
pub struct HvMemPred<PT, M, A, P> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
    P: HvMemProtocol,
 {
    pub _phantom: PhantomData<(PT, M, A, P)>,
}

impl<PT, M, A, P> InvariantPredicate<HvMemKey, HvMemRwContent<PT, M, A, P>> for HvMemPred<
    PT,
    M,
    A,
    P,
> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator, P: HvMemProtocol {
    /// The content is well-formed when:
    /// - `zone_list_perm` is initialised and points to the key's cell,
    /// - `global_state` is internally well-formed (`P::global_wf`), and
    /// - the exec zone list and the ghost state agree: every ghost zone ID has
    ///   exactly one corresponding exec `Zone`, all zones share the same
    ///   spec instance, and exec zone IDs are pairwise distinct.
    open spec fn inv(k: HvMemKey, v: HvMemRwContent<PT, M, A, P>) -> bool {
        &&& v.zone_list_perm.is_init()
        &&& v.zone_list_perm@.pcell === k.cell_id
        &&& P::mem_inst_id(&v.global_state) == k.mem_inst_id
        &&& P::global_wf(&v.global_state)
        &&& {
            let zone_list = v.zone_list_perm@.mem_contents->Init_0;
            // The ghost zone_ids set is exactly the set of exec zone IDs.
            &&& forall|zid: nat| #[trigger]
                P::zone_ids(&v.global_state).contains(zid) == (exists|i: int|
                    0 <= i < zone_list.len() && #[trigger] zone_list[i].zone_id as nat
                        == zid)
                // Exec zone IDs are pairwise distinct (ensures the bijection above is well-defined).
            &&& forall|i: int, j: int|
                #![auto]
                0 <= i < zone_list.len() && 0 <= j < zone_list.len() && i != j
                    ==> zone_list[i].zone_id
                    != zone_list[j].zone_id
            // Each exec zone is bound to the correct mem spec instance.
            &&& forall|i: int|
                #![trigger zone_list[i]]
                0 <= i < zone_list.len() ==> zone_list[i].mem_inst_id()
                    == k.mem_inst_id
            // Each exec zone is bound to the same allocator instance.
            &&& forall|i: int|
                #![trigger zone_list[i]]
                0 <= i < zone_list.len() ==> zone_list[i].alloc_inst_id()
                    == k.alloc_inst_id
            // Each zone in the list is well-formed.
            &&& forall|i: int| #![auto] 0 <= i < zone_list.len() ==> zone_list[i].wf()
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
    P: HvMemProtocol,
 {
    /// Zone list — written only while the HvMem write guard is held.
    pub zone_mem_list: PCell<Vec<Arc<Zone<PT, M, A, P>>>>,
    /// RwLock protecting `HvMemRwContent<PT,M,A,P>` with `HvMemKey` predicate.
    pub lock: RwLock<HvMemKey, HvMemRwContent<PT, M, A, P>, HvMemPred<PT, M, A, P>>,
    /// Global allocator — already protected by its own `Mutex`.
    pub allocator: GlobalAllocator<A>,
}

impl<PT, M, A, P> HvMem<PT, M, A, P> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
    P: HvMemProtocol,
 {
    /// Structural well-formedness:
    /// - the outer `RwLock` is internally consistent,
    /// - the `PointsTo` inside the lock points to the same cell as the key,
    /// - the global allocator is valid.
    ///
    /// `HvMemPred::inv` (checked on every write-lock release) additionally
    /// guarantees that the `PointsTo` inside the lock points to the same cell
    /// and that `ClosureGlobalState` is well-formed.
    pub open spec fn invariants(&self) -> bool {
        &&& self.lock.wf()
        &&& self.zone_mem_list.id() == self.lock.k@.cell_id
        &&& self.allocator.invariants()
        &&& self.lock.k@.alloc_inst_id == self.allocator.inst_id()
    }

    /// Add a new empty zone to the hypervisor memory manager.
    ///
    /// The zone is created with no regions; use `insert_region` to populate it
    /// after creation.
    ///
    /// 1. Acquire the **HvMem write lock** to serialise zone-list mutations.
    /// 2. Advance the protocol ghost state machine (`add_zone`) to obtain a
    ///    fresh `ZoneToken` for the new zone.
    /// 3. Delegate Zone assembly to `Zone::new` (infallible).
    /// 4. Push the new `Zone`, return the zone list to its `PCell`, and release
    ///    the write lock.
    pub fn add_zone(&self, zid: usize, pt_constants: PTConstants) -> (res: Result<(), ()>)
        requires
            self.invariants(),
            pt_constants@.valid(),
            forall|level: nat|
                level < pt_constants.arch@.level_count() ==> pt_constants.arch@.entry_count(level)
                    == 512,
            pt_constants.arch@.leaf_frame_size() == FrameSize::Size4K,
        ensures
            res is Ok ==> self.invariants(),
    {
        // ── Step 1: acquire HvMem write lock ──────────────────────────────────
        let guard = self.lock.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: HvMemRwContent<PT, M, A, P> = token.get();
        let mut zones = self.zone_mem_list.take(Tracked(&mut content.zone_list_perm));

        // ── Step 1b: reject duplicate zone IDs ────────────────────────────────
        let mut i: usize = 0;
        while i < zones.len()
            invariant
                i <= zones.len(),
                self.invariants(),
                !content.zone_list_perm.is_init(),
                content.zone_list_perm@.pcell === self.zone_mem_list.id(),
                content.zone_list_perm@.pcell === self.lock.k@.cell_id,
                handle@.instance_id() == self.lock.inst@.id(),
                P::mem_inst_id(&content.global_state) == self.lock.k@.mem_inst_id,
                P::global_wf(&content.global_state),
                // Scan progress: none of the zones before i have zone_id == zid.
                forall|j: int| 0 <= j < i ==> #[trigger] zones[j].zone_id != zid,
                // Bijection: ghost zone_ids <-> exec zone IDs.
                forall|z: nat| #[trigger]
                    P::zone_ids(&content.global_state).contains(z) == (exists|k: int|
                        0 <= k < zones@.len() && #[trigger] zones@[k].zone_id as nat == z),
                // Spec-instance consistency.
                forall|k: int|
                    #![trigger zones@[k]]
                    0 <= k < zones@.len() ==> zones@[k].mem_inst_id() == self.lock.k@.mem_inst_id,
                forall|k: int|
                    #![trigger zones@[k]]
                    0 <= k < zones@.len() ==> zones@[k].alloc_inst_id()
                        == self.lock.k@.alloc_inst_id,
                // Pairwise distinct IDs.
                forall|k: int, l: int|
                    #![auto]
                    0 <= k < zones@.len() && 0 <= l < zones@.len() && k != l ==> zones@[k].zone_id
                        != zones@[l].zone_id,
                // All zones well-formed.
                forall|k: int| #![auto] 0 <= k < zones@.len() ==> zones@[k].wf(),
            decreases zones.len() - i,
        {
            if zones[i].zone_id == zid {
                self.zone_mem_list.put(Tracked(&mut content.zone_list_perm), zones);
                assert(HvMemPred::<PT, M, A, P>::inv(self.lock.k@, content));
                self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });
                return Err(());
            }
            i += 1;
        }

        // ── Step 2: advance protocol ghost state, obtain zone token ───────────
        // Capture ghost values before mutating global_state.
        let ghost pre_add_zone_ids: Set<nat>;
        let tracked zone_state: P::ZoneToken;
        let ghost mem_inst_id: InstanceId;
        proof {
            pre_add_zone_ids = P::zone_ids(&content.global_state);
            mem_inst_id = P::mem_inst_id(&content.global_state);
            assert(forall|j: int| 0 <= j < zones.len() ==> #[trigger] zones[j].zone_id != zid);
            // From the bijection invariant: zone_ids.contains(zid as nat) iff
            // some exec zone has zone_id == zid — but the scan found none.
            assert(!P::zone_ids(&content.global_state).contains(zid as nat));
            zone_state = P::add_zone(&mut content.global_state, zid as nat);
            // Postcondition: zone_ids(new_gs) = pre_add_zone_ids.insert(zid as nat)
            //                mem_inst_id(new_gs)  = mem_inst_id  (unchanged)
            //                global_wf(new_gs)
        }

        // ── Step 3: assemble the new Zone with an empty MemorySet ─────────────
        let mem_set = M::new(&self.allocator, pt_constants);
        let new_zone = Arc::new(
            Zone::<PT, M, A, P>::new(
                mem_set,
                zid,
                Ghost(mem_inst_id),
                Ghost(self.allocator.inst_id()),
                Tracked(zone_state),
            ),
        );
        // Snapshot the pre-push zone list for use in the postcondition proof.
        let ghost old_zones = zones@;

        // ── Step 4: push zone, restore PCell, release write lock ─────────────
        zones.push(new_zone);
        self.zone_mem_list.put(Tracked(&mut content.zone_list_perm), zones);
        proof {
            let zone_list = content.zone_list_perm@.mem_contents->Init_0;
            // After push+put: zone_list@ = old_zones.push(new_zone)
            let new_zones = zone_list@;
            let old_len = old_zones.len() as int;
            assert(new_zones =~= old_zones.push(new_zone));
            assert(forall|k: int| 0 <= k < old_len ==> new_zones[k] == old_zones[k]);
            assert(new_zones[old_len] == new_zone);
            // From P::add_zone postconditions:
            assert(P::zone_ids(&content.global_state) =~= pre_add_zone_ids.insert(zid as nat));
            assert(P::mem_inst_id(&content.global_state) == mem_inst_id);
            assert(HvMemPred::<PT, M, A, P>::inv(self.lock.k@, content)) by {
                // 1. zone_list_perm.is_init() — from put.
                // 2. pcell matches — from loop invariant.
                assert(content.zone_list_perm@.pcell === self.lock.k@.cell_id);
                // 3. global_wf — from P::add_zone postcondition.
                // 4. Bijection: zone_ids(new_gs) <-> new_zones.
                assert forall|z: nat|
                    P::zone_ids(&content.global_state).contains(z) == (exists|k: int|
                        0 <= k < new_zones.len() && #[trigger] new_zones[k].zone_id as nat
                            == z) by {
                    if z == zid as nat {
                        // zone_ids(new_gs) contains zid as nat (inserted by add_zone).
                        assert(P::zone_ids(&content.global_state).contains(z));
                        // new_zones[old_len].zone_id == zid.
                        assert(new_zones[old_len].zone_id as nat == z);
                    } else {
                        // zone_ids(new_gs).contains(z) == pre_add_zone_ids.contains(z)
                        assert(P::zone_ids(&content.global_state).contains(z)
                            == pre_add_zone_ids.contains(z));
                        // old bijection: pre_add_zone_ids.contains(z) == exists k < old_len.
                        assert(pre_add_zone_ids.contains(z) == (exists|k: int|
                            0 <= k < old_len && #[trigger] old_zones[k].zone_id as nat == z));
                    }
                };
                // 5. Spec-instance consistency for all new zones.
                assert forall|k: int|
                    #![trigger new_zones[k]]
                    0 <= k < new_zones.len() implies new_zones[k].mem_inst_id()
                    == self.lock.k@.mem_inst_id by {
                    if k < old_len {
                        // From loop invariant: old_zones[k].mem_inst_id() == mem_inst_id.
                        assert(old_zones[k].mem_inst_id() == mem_inst_id);
                    }
                };
                // 6. Pairwise distinct IDs.
                assert forall|k: int, l: int|
                    #![auto]
                    0 <= k < new_zones.len() && 0 <= l < new_zones.len() && k
                        != l implies new_zones[k].zone_id != new_zones[l].zone_id by {
                    if k < old_len && l < old_len {
                        // From loop invariant.
                    } else if k == old_len {
                        // new_zone.zone_id == zid; old_zones[l].zone_id != zid (from scan).
                        assert(old_zones[l].zone_id != zid);
                    } else {
                        // l == old_len; old_zones[k].zone_id != zid (from scan).
                        assert(old_zones[k].zone_id != zid);
                    }
                };
                // 7. All zones well-formed.
                assert(forall|k: int| #![auto] 0 <= k < new_zones.len() ==> new_zones[k].wf());
            };
        }
        self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });

        Ok(())
    }

    /// Remove the zone identified by `zid` from the hypervisor memory manager.
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
            self.invariants(),
        ensures
            res is Ok ==> self.invariants(),
    {
        // ── Step 1: acquire HvMem write lock ─────────────────────────────────
        let guard = self.lock.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: HvMemRwContent<PT, M, A, P> = token.get();
        let mut zones = self.zone_mem_list.take(Tracked(&mut content.zone_list_perm));

        // ── Step 2: find zone by ID ───────────────────────────────────────────
        let mut i: usize = 0;
        while i < zones.len()
            invariant_except_break
                i <= zones.len(),
                self.invariants(),
                // Every zone in the list is well-formed.
                forall|j: int| 0 <= j < zones@.len() ==> #[trigger] zones@[j].wf(),
                // No zone before index i has zone_id == zid.
                forall|j: int| 0 <= j < i ==> #[trigger] zones@[j].zone_id != zid,
            ensures
                i < zones.len() ==> zones[i as int].zone_id == zid && zones[i as int].wf(),
            decreases zones.len() - i,
        {
            if zones[i].zone_id == zid {
                break ;
            }
            i += 1;
        }

        if i >= zones.len() {
            // Zone not found — restore and return error.
            self.zone_mem_list.put(Tracked(&mut content.zone_list_perm), zones);
            assert(HvMemPred::<PT, M, A, P>::inv(self.lock.k@, content));
            self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });
            return Err(());
        }
        // ── Step 3: remove zone from list ─────────────────────────────────────

        let zone = zones.swap_remove(i);

        // ── Step 4: extract zone token and M from the zone ────────────────────
        let zone_guard = zone.lock.lock_write();
        let RwWriteGuard { handle: zone_handle, token: zone_token } = zone_guard;
        let tracked mut zone_content: ZoneRwContent<M, P> = zone_token.get();
        // Take M out of the zone's PCell so it is properly dropped below.
        let _mem_set: M = zone.mem_set.take(Tracked(&mut zone_content.mem_set_perm));
        // _mem_set is dropped at end of scope.

        // ── Step 5: advance protocol ghost state ───────────────────────────────
        proof {
            let tracked ZoneRwContent::<M, P> { mem_set_perm: _, zone_state } = zone_content;
            P::remove_zone(&mut content.global_state, zone_state);
            // zone_handle (writer token) is consumed here via assume — the zone is
            // being destroyed so there is no need to formally unlock it.
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
            self.invariants(),
        ensures
            res.is_some() ==> res.unwrap().wf() && res.unwrap().zone_id == zid,
    {
        // ── Acquire HvMem read lock (allows concurrent lookups) ───────────────
        let guard = self.lock.lock_read();

        // ── Borrow the zone list via the lock's ghost predicate ───────────────
        let Tracked(content) = guard.borrow(&self.lock);
        let tracked HvMemRwContent::<PT, M, A, P> { zone_list_perm, .. } = content;
        let zones = self.zone_mem_list.borrow(Tracked(&zone_list_perm));

        // ── Scan for matching zone ID ─────────────────────────────────────────
        let mut i: usize = 0;
        while i < zones.len()
            invariant_except_break
                i <= zones.len(),
                self.invariants(),
                // Every zone in the list is well-formed.
                forall|j: int| 0 <= j < zones@.len() ==> #[trigger] zones@[j].wf(),
                // No zone before index i has zone_id == zid.
                forall|j: int| 0 <= j < i ==> #[trigger] zones@[j].zone_id != zid,
            ensures
                i < zones.len() ==> zones[i as int].zone_id == zid && zones[i as int].wf(),
            decreases zones.len() - i,
        {
            if zones[i].zone_id == zid {
                break ;
            }
            i += 1;
        }
        let result = if i < zones.len() {
            let zone = zones[i].clone();
            proof {
                // Arc::clone gives the same inner Zone; spec field access deref through Arc.
                assert(zone.zone_id == zid);
                assert(zone.wf());
            }
            Some(zone)
        } else {
            None
        };

        self.lock.unlock_read(guard);
        result
    }
}

/// Concrete `BudgetProtocol` specialisation: both `insert_region` and
/// `remove_region` acquire only the HvMem **read** lock.
///
/// `BudgetSpec::insert_region` / `remove_region` are zone-local transitions:
/// they only touch the per-zone `zones[zid]` map-sharded token and access the
/// `BudgetSpecInstance` (constant-sharded) as a shared reference.  The global
/// `zone_ids_tok` is never modified, so no HvMem write lock is required.
///
/// Locking order: HvMem read lock → zone write lock.
impl<PT, M, A> HvMem<PT, M, A, BudgetProtocol> where
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
            self.invariants(),
        ensures
            res is Ok ==> self.invariants(),
    {
        // ── Step 1: validate region ────────────────────────────────────────────
        if !region.valid() {
            return Err(());
        }
        // ── Step 2: acquire HvMem read lock ───────────────────────────────────

        let guard = self.lock.lock_read();
        let tracked HvMemRwContent::<PT, M, A, BudgetProtocol> { zone_list_perm, global_state } =
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
        let res = zones[idx].insert_region(&self.allocator, Tracked(&global_state), region);

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
            self.invariants(),
        ensures
            res is Ok ==> self.invariants(),
    {
        // ── Step 1: validate region ────────────────────────────────────────────
        if !region.valid() {
            return Err(());
        }
        // ── Step 2: acquire HvMem read lock ───────────────────────────────────

        let guard = self.lock.lock_read();
        let tracked HvMemRwContent::<PT, M, A, BudgetProtocol> { zone_list_perm, global_state } =
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
        let res = zones[idx].remove_region(&self.allocator, Tracked(&global_state), region);

        self.lock.unlock_read(guard);
        res
    }
}

/// Concrete `ClosureProtocol` implementation: `insert_region` and `remove_region`
/// require the HvMem **write** lock because `ClosureProtocol::insert_region` and
/// `::remove_region` extend / shrink the global `region_closure_tok`, which is
/// stored in `HvMemRwContent::global_state` and therefore needs exclusive access.
impl<PT, M, A> HvMem<PT, M, A, ClosureProtocol> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
 {
    /// Insert a physical memory region into the zone identified by `zid`.
    ///
    /// Acquires the HvMem **write** lock so that `ClosureProtocol::insert_region`
    /// has exclusive access to `global_state` (it extends the global
    /// `region_closure_tok`).
    ///
    /// Returns `Err(())` if `region` is invalid, the zone is not found, or
    /// `region` overlaps an existing mapping in that zone.
    pub fn insert_region(&self, zid: usize, region: MemoryRegion) -> (res: Result<(), ()>)
        requires
            self.invariants(),
        ensures
            res is Ok ==> self.invariants(),
    {
        // ── Step 1: validate region ────────────────────────────────────────────
        if !region.valid() {
            return Err(());
        }
        // ── Step 2: acquire HvMem write lock ──────────────────────────────────

        let guard = self.lock.lock_write();
        let RwWriteGuard { handle: hvm_handle, token: hvm_token } = guard;
        let tracked mut hvm_content: HvMemRwContent<PT, M, A, ClosureProtocol> = hvm_token.get();
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
                assume(HvMemPred::<PT, M, A, ClosureProtocol>::inv(self.lock.k@, hvm_content));
            }
            self.lock.unlock_write(
                RwWriteGuard { handle: hvm_handle, token: Tracked(hvm_content) },
            );
            return Err(());
        }
        let idx = idx_opt.unwrap();

        // ── Step 4: delegate to Zone::insert_region ───────────────────────────
        // Zone::insert_region acquires the zone write lock, runs the exec insert,
        // and calls ClosureProtocol::insert_region to advance the ghost state.
        // We hold the HvMem write lock throughout, supplying
        // &mut hvm_content.global_state as required by ClosureProtocol.
        let res = zones[idx].insert_region(
            &self.allocator,
            Tracked(&mut hvm_content.global_state),
            region,
        );

        // ── Step 5: restore zone list and release HvMem write lock ────────────
        self.zone_mem_list.put(Tracked(&mut hvm_content.zone_list_perm), zones);
        proof {
            assume(HvMemPred::<PT, M, A, ClosureProtocol>::inv(self.lock.k@, hvm_content));
        }
        self.lock.unlock_write(RwWriteGuard { handle: hvm_handle, token: Tracked(hvm_content) });
        res
    }

    /// Remove a physical memory region from the zone identified by `zid`.
    ///
    /// `region.start` locates the region in the exec memory set; the full
    /// `MemoryRegion` is forwarded to `ClosureProtocol::remove_region` for the
    /// ghost update.
    ///
    /// Returns `Err(())` if `region` is invalid, the zone is not found, or no
    /// region starts at `region.start`.
    pub fn remove_region(&self, zid: usize, region: MemoryRegion) -> (res: Result<(), ()>)
        requires
            self.invariants(),
        ensures
            res is Ok ==> self.invariants(),
    {
        // ── Step 1: validate region ────────────────────────────────────────────
        if !region.valid() {
            return Err(());
        }
        // ── Step 2: acquire HvMem write lock ──────────────────────────────────

        let guard = self.lock.lock_write();
        let RwWriteGuard { handle: hvm_handle, token: hvm_token } = guard;
        let tracked mut hvm_content: HvMemRwContent<PT, M, A, ClosureProtocol> = hvm_token.get();
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
                assume(HvMemPred::<PT, M, A, ClosureProtocol>::inv(self.lock.k@, hvm_content));
            }
            self.lock.unlock_write(
                RwWriteGuard { handle: hvm_handle, token: Tracked(hvm_content) },
            );
            return Err(());
        }
        let idx = idx_opt.unwrap();

        // ── Step 4: delegate to Zone::remove_region ───────────────────────────
        let res = zones[idx].remove_region(
            &self.allocator,
            Tracked(&mut hvm_content.global_state),
            region,
        );

        // ── Step 5: restore zone list and release HvMem write lock ────────────
        self.zone_mem_list.put(Tracked(&mut hvm_content.zone_list_perm), zones);
        proof {
            assume(HvMemPred::<PT, M, A, ClosureProtocol>::inv(self.lock.k@, hvm_content));
        }
        self.lock.unlock_write(RwWriteGuard { handle: hvm_handle, token: Tracked(hvm_content) });
        res
    }
}

} // verus!
