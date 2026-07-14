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
//!   - `protocol::closure`: assumption-1 ghost state (`ClosureGlobalState`) + `ClosureProtocol`.
//!   - `protocol::budget`:  assumption-2 ghost state (`BudgetGlobalState`) + `BudgetProtocol`.
//! - `config`: zone configuration types and conversion to `MemoryRegion`.
//! - `mod` (this file): `ZoneWriteGuard`, `HvMem` — the global exec orchestration layer.
mod config;
pub mod protocol;
pub mod spec;
pub mod zone;

use crate::{
    address::frame::FrameSize,
    address::region::MemoryRegion,
    bitmap_allocator::bitmap_trait::BitmapAllocator,
    global_allocator::GlobalAllocator,
    hardware::{HardwareInstr, MmuHardware},
    model::convert::pt_s2map_inner,
    model::types::{GuestPage, S2Entry, VmId},
    memory_set::{MemorySet, SpecMemorySet},
    page_table::{PTConstants, PageTable, SpecPTConstants},
    sync::rwlock::{RwLock, RwReadGuard, RwReaderToken, RwWriteGuard, RwWriterToken},
};
use core::marker::PhantomData;
use protocol::{BudgetProtocol, ZoneGhostProtocol, ZoneStateOps};
use spec::budget::{gic_region, zone_regions};
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
    /// MMU instance ID.
    pub mmu_inst_id: InstanceId,
    /// IOMMU MMU instance ID (separate `MmuHardware` instance for the SMMU stage-2).
    pub iommu_mmu_inst_id: InstanceId,
    /// Shared page-table architecture for all zones' CPU/IOMMU memory sets.
    pub pt_constants: SpecPTConstants,
}

/// Tracked content protected by `HvMem`'s `RwLock`.
///
/// Bundles the `PointsTo<Vec<Zone<...>>>` cell-permission for the zone list
/// together with the protocol-specific global ghost state (`P::GlobalState`).
pub tracked struct HvMemRwContent<PT, M, A, P, I> where
    PT: PageTable<A>,
    M: MemorySet<PT, A, I>,
    A: BitmapAllocator,
    P: ZoneGhostProtocol,
    I: HardwareInstr,
 {
    /// Permission to read/write the zone-list PCell.
    pub zone_list_perm: PointsTo<Vec<Zone<PT, M, A, P, I>>>,
    /// Protocol-specific global ghost state (e.g. `ClosureGlobalState` for ClosureProtocol).
    pub global_state: P::GlobalState,
}

/// Phantom struct that carries the `HvMem`-level `InvariantPredicate`.
pub struct HvMemPred<PT, M, A, P, I> where
    PT: PageTable<A>,
    M: MemorySet<PT, A, I>,
    A: BitmapAllocator,
    P: ZoneGhostProtocol,
    I: HardwareInstr,
 {
    pub _phantom: PhantomData<(PT, M, A, P, I)>,
}

impl<PT, M, A, P, I> InvariantPredicate<HvMemKey, HvMemRwContent<PT, M, A, P, I>> for HvMemPred<
    PT,
    M,
    A,
    P,
    I,
> where
    PT: PageTable<A>,
    M: MemorySet<PT, A, I>,
    A: BitmapAllocator,
    P: ZoneGhostProtocol,
    I: HardwareInstr,
 {
    /// The content is well-formed when:
    /// - `zone_list_perm` is initialised and points to the key's cell,
    /// - `global_state` is internally well-formed (`P::global_wf`), and
    /// - the exec zone list and the ghost state agree: every ghost zone ID has
    ///   exactly one corresponding exec `Zone`, all zones share the same
    ///   spec instance, and exec zone IDs are pairwise distinct.
    open spec fn inv(k: HvMemKey, v: HvMemRwContent<PT, M, A, P, I>) -> bool {
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
            // Each exec zone is bound to the same MMU instance.
            &&& forall|i: int|
                #![trigger zone_list[i]]
                0 <= i < zone_list.len() ==> zone_list[i].mmu_inst_id()
                    == k.mmu_inst_id
            // Each exec zone is bound to the same IOMMU MMU instance.
            &&& forall|i: int|
                #![trigger zone_list[i]]
                0 <= i < zone_list.len() ==> zone_list[i].iommu_mmu_inst_id()
                    == k.iommu_mmu_inst_id
            // Each exec zone uses the same page-table architecture.
            &&& forall|i: int|
                #![trigger zone_list[i]]
                0 <= i < zone_list.len() ==> zone_list[i].pt_constants() == k.pt_constants
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
///      .hv_mem_state   : GlobalState                <- ghost tokens     ┘ RwLock
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
pub struct HvMem<PT, M, A, P, I> where
    PT: PageTable<A>,
    M: MemorySet<PT, A, I>,
    A: BitmapAllocator,
    P: ZoneGhostProtocol,
    I: HardwareInstr,
 {
    /// Zone list — written only while the HvMem write guard is held.
    pub zone_mem_list: PCell<Vec<Zone<PT, M, A, P, I>>>,
    /// RwLock protecting `HvMemRwContent<PT,M,A,P>` with `HvMemKey` predicate.
    pub lock: RwLock<HvMemKey, HvMemRwContent<PT, M, A, P, I>, HvMemPred<PT, M, A, P, I>>,
    /// Global allocator — already protected by its own `Mutex`.
    pub allocator: GlobalAllocator<A>,
}

impl<PT, M, A, P, I> HvMem<PT, M, A, P, I> where
    PT: PageTable<A>,
    M: MemorySet<PT, A, I>,
    A: BitmapAllocator,
    P: ZoneGhostProtocol,
    I: HardwareInstr,
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

    /// Return the index of `zid` in a well-formed zone list, if present.
    fn find_zone_index(zones: &Vec<Zone<PT, M, A, P, I>>, zid: usize) -> (res: Option<usize>)
        requires
            forall|j: int| 0 <= j < zones@.len() ==> #[trigger] zones@[j].wf(),
        ensures
            res is Some ==> {
                &&& res->Some_0 < zones@.len()
                &&& zones@[res->Some_0 as int].zone_id == zid
                &&& zones@[res->Some_0 as int].wf()
            },
            res is None ==> forall|j: int|
                0 <= j < zones@.len() ==> #[trigger] zones@[j].zone_id != zid,
    {
        let mut i: usize = 0;
        while i < zones.len()
            invariant
                i <= zones.len(),
                forall|j: int| 0 <= j < zones@.len() ==> #[trigger] zones@[j].wf(),
                forall|j: int| 0 <= j < i ==> #[trigger] zones@[j].zone_id != zid,
            decreases zones.len() - i,
        {
            if zones[i].zone_id == zid {
                assert(zones@[i as int].wf());
                return Some(i);
            }
            i += 1;
        }
        None
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
    pub fn add_zone(
        &self,
        zid: usize,
        pt_constants: PTConstants,
        mmu: &mut MmuHardware<I>,
        iommu_mmu: &mut MmuHardware<I>,
    ) -> (res: Result<(), ()>)
        requires
            self.invariants(),
            pt_constants@.valid(),
            pt_constants@ == self.lock.k@.pt_constants,
            forall|level: nat|
                level < pt_constants.arch@.level_count() ==> pt_constants.arch@.entry_count(level)
                    == 512,
            pt_constants.arch@.leaf_frame_size() == FrameSize::Size4K,
            old(mmu).wf(),
            old(mmu).inst_id() == self.lock.k@.mmu_inst_id,
            old(iommu_mmu).wf(),
            old(iommu_mmu).inst_id() == self.lock.k@.iommu_mmu_inst_id,
            // Neither MMU may yet know this vm — the caller's obligation (trusted
            // configuration, like zone budgets); discharged once HvMem carries a
            // `mmu.live_vms() == zone_ids` invariant (a later refinement step).
            !old(mmu).live_vms().contains(VmId(zid as nat)),
            !old(iommu_mmu).live_vms().contains(VmId(zid as nat)),
        ensures
            res is Ok ==> self.invariants(),
            mmu.wf(),
            mmu.inst_id() == old(mmu).inst_id(),
            iommu_mmu.wf(),
            iommu_mmu.inst_id() == old(iommu_mmu).inst_id(),
    {
        // ── Step 1: acquire HvMem write lock ──────────────────────────────────
        let guard = self.lock.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: HvMemRwContent<PT, M, A, P, I> = token.get();
        let mut zones = self.zone_mem_list.take(Tracked(&mut content.zone_list_perm));

        // ── Step 1b: reject duplicate zone IDs ────────────────────────────────
        match Self::find_zone_index(&zones, zid) {
            Some(_) => {
                self.zone_mem_list.put(Tracked(&mut content.zone_list_perm), zones);
                assert(HvMemPred::<PT, M, A, P, I>::inv(self.lock.k@, content));
                self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });
                return Err(());
            },
            None => {},
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
            // some exec zone has zone_id == zid — but `find_zone_index` found none.
            assert(!P::zone_ids(&content.global_state).contains(zid as nat));
            zone_state = P::add_zone(&mut content.global_state, zid as nat);
            // Postcondition: zone_ids(new_gs) = pre_add_zone_ids.insert(zid as nat)
            //                mem_inst_id(new_gs)  = mem_inst_id  (unchanged)
            //                global_wf(new_gs)
        }

        // ── Step 3: assemble the new Zone with empty CPU/IOMMU MemorySets ────
        let cpu_mem_set = M::new(&self.allocator, pt_constants.clone());
        let iommu_mem_set = M::new(&self.allocator, pt_constants);
        // Mint this zone's CPU MMU `s2map` slice token (empty, keyed by the vm); the
        // forced sync clause holds at birth because an empty mem_set projects to an
        // empty `s2map`.
        let s2map_tok = mmu.add_vm(Ghost(VmId(zid as nat)));
        // Mint this zone's IOMMU slice token (empty) on the separate IOMMU instance.
        let iommu_s2map_tok = iommu_mmu.add_vm(Ghost(VmId(zid as nat)));
        proof {
            assert(pt_s2map_inner(cpu_mem_set@.mappings) =~= Map::<GuestPage, S2Entry>::empty());
            assert(pt_s2map_inner(iommu_mem_set@.mappings) =~= Map::<GuestPage, S2Entry>::empty());
            // Both fresh mem_sets equal the literal empty SpecMemorySet that
            // `P::add_zone` put in the ghost zone token — this discharges
            // `Zone::new`'s ghost/exec mirror preconditions.
            assert(cpu_mem_set@ == SpecMemorySet {
                regions: Set::empty(),
                mappings: Map::empty(),
            });
            assert(iommu_mem_set@ == SpecMemorySet {
                regions: Set::empty(),
                mappings: Map::empty(),
            });
        }
        let new_zone = Zone::<PT, M, A, P, I>::new(
            cpu_mem_set,
            iommu_mem_set,
            zid,
            Ghost(mem_inst_id),
            Ghost(self.allocator.inst_id()),
            Ghost(mmu.inst_id()),
            Ghost(iommu_mmu.inst_id()),
            Tracked(zone_state),
            s2map_tok,
            iommu_s2map_tok,
        );
        // Snapshot the pre-push zone list for use in the postcondition proof.
        let ghost old_zones = zones@;

        // ── Step 4: push zone, restore PCell, release write lock ─────────────
        zones.push(new_zone);
        self.zone_mem_list.put(Tracked(&mut content.zone_list_perm), zones);
        proof {
            let zone_list = content.zone_list_perm@.mem_contents->Init_0;
            // After push+put: zone_list@ = old_zones.push(new_zone).
            let new_zones = zone_list@;
            let old_len = old_zones.len() as int;
            assert(new_zones =~= old_zones.push(new_zone));
            assert(forall|k: int| 0 <= k < old_len ==> new_zones[k] == old_zones[k]);
            assert(new_zones[old_len] == new_zone);
            // From P::add_zone postconditions:
            assert(P::zone_ids(&content.global_state) =~= pre_add_zone_ids.insert(zid as nat));
            assert(P::mem_inst_id(&content.global_state) == mem_inst_id);
            assert(HvMemPred::<PT, M, A, P, I>::inv(self.lock.k@, content)) by {
                // 1. zone_list_perm.is_init() — from put.
                // 2. pcell matches — from loop invariant.
                assert(content.zone_list_perm@.pcell === self.lock.k@.cell_id);
                // 3. global_wf — from P::add_zone postcondition.
                // 4. Bijection: zone_ids(new_gs) <-> new_zones.
                assert forall|z: nat|
                    P::zone_ids(&content.global_state).contains(z) == (exists|k: int|
                        0 <= k < new_zones.len() && #[trigger] new_zones[k].zone_id as nat
                            == z) by {
                    if z == zid {
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
                // 5b. MMU-instance consistency for all new zones.
                assert forall|k: int|
                    #![trigger new_zones[k]]
                    0 <= k < new_zones.len() implies new_zones[k].mmu_inst_id()
                    == self.lock.k@.mmu_inst_id by {
                    if k < old_len {
                        // From loop invariant: old_zones[k].mmu_inst_id() == k.mmu_inst_id.
                        assert(old_zones[k].mmu_inst_id() == self.lock.k@.mmu_inst_id);
                    } else {
                        // new_zone.mmu_inst_id() == mmu.inst_id() (Zone::new) ==
                        // k.mmu_inst_id (loop invariant, preserved by add_vm's stable inst_id).
                        assert(new_zones[k] == new_zone);
                    }
                };
                // 5c. IOMMU-instance consistency for all new zones.
                assert forall|k: int|
                    #![trigger new_zones[k]]
                    0 <= k < new_zones.len() implies new_zones[k].iommu_mmu_inst_id()
                    == self.lock.k@.iommu_mmu_inst_id by {
                    if k < old_len {
                        assert(old_zones[k].iommu_mmu_inst_id() == self.lock.k@.iommu_mmu_inst_id);
                    } else {
                        assert(new_zones[k] == new_zone);
                    }
                };
                // 5d. Page-table architecture consistency for all new zones.
                assert forall|k: int|
                    #![trigger new_zones[k]]
                    0 <= k < new_zones.len() implies new_zones[k].pt_constants()
                    == self.lock.k@.pt_constants by {
                    if k < old_len {
                        assert(old_zones[k].pt_constants() == self.lock.k@.pt_constants);
                    } else {
                        assert(new_zones[k] == new_zone);
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
                        // new_zone.zone_id == zid; old_zones[l].zone_id != zid
                        // (from `find_zone_index`).
                        assert(old_zones[l].zone_id != zid);
                    } else {
                        // l == old_len; old_zones[k].zone_id != zid
                        // (from `find_zone_index`).
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
    /// 3. Acquire the zone write lock and reject removal unless both its CPU and
    ///    IOMMU memory sets are empty.
    /// 4. Swap-remove the empty zone from the list.
    /// 5. Advance the protocol's `remove_zone` transition to drop the zone token.
    /// 6. Restore the zone list and release the HvMem write lock.
    ///
    /// Returns `Err(())` if no zone with the given `zid` is found or either of
    /// its memory sets is non-empty.
    pub fn remove_zone(&self, zid: usize) -> (res: Result<(), ()>)
        requires
            self.invariants(),
        ensures
            res is Ok ==> self.invariants(),
    {
        // ── Step 1: acquire HvMem write lock ─────────────────────────────────
        let guard = self.lock.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: HvMemRwContent<PT, M, A, P, I> = token.get();
        let mut zones = self.zone_mem_list.take(Tracked(&mut content.zone_list_perm));

        // ── Step 2: find zone by ID ───────────────────────────────────────────
        let i = match Self::find_zone_index(&zones, zid) {
            Some(i) => i,
            None => {
            // Zone not found — restore and return error.
                self.zone_mem_list.put(Tracked(&mut content.zone_list_perm), zones);
                assert(HvMemPred::<PT, M, A, P, I>::inv(self.lock.k@, content));
                self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });
                return Err(());
            },
        };
        // ── Step 3: lock the zone and require both memory sets to be empty ─────
        let zone_guard = zones[i].lock.lock_write();
        let RwWriteGuard { handle: zone_handle, token: zone_token } = zone_guard;
        let tracked mut zone_content: ZoneRwContent<M, P> = zone_token.get();
        let cpu_mem_set: M = zones[i].cpu_mem_set.take(
            Tracked(&mut zone_content.cpu_mem_set_perm),
        );
        let iommu_mem_set: M = zones[i].iommu_mem_set.take(
            Tracked(&mut zone_content.iommu_mem_set_perm),
        );
        let cpu_empty = cpu_mem_set.is_empty();
        let iommu_empty = iommu_mem_set.is_empty();
        if !cpu_empty || !iommu_empty {
            zones[i].cpu_mem_set.put(Tracked(&mut zone_content.cpu_mem_set_perm), cpu_mem_set);
            zones[i].iommu_mem_set.put(
                Tracked(&mut zone_content.iommu_mem_set_perm),
                iommu_mem_set,
            );
            assert(ZonePred::<PT, M, A, P, I>::inv(zones[i as int].lock.k@, zone_content));
            zones[i].lock.unlock_write(RwWriteGuard {
                handle: zone_handle,
                token: Tracked(zone_content),
            });
            self.zone_mem_list.put(Tracked(&mut content.zone_list_perm), zones);
            assert(HvMemPred::<PT, M, A, P, I>::inv(self.lock.k@, content));
            self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });
            return Err(());
        }

        proof {
            assert(zone_content.zone_state.ghost_zone().cpu_mem_set == cpu_mem_set@);
            assert(zone_content.zone_state.ghost_zone().iommu_mem_set == iommu_mem_set@);
            assert(zone_content.zone_state.ghost_zone().cpu_mem_set.empty());
            assert(zone_content.zone_state.ghost_zone().iommu_mem_set.empty());
        }

        // ── Step 4: remove the empty zone from the list ────────────────────────
        let ghost old_zones = zones@;
        let _zone = zones.swap_remove(i);

        // ── Step 5: advance protocol ghost state ───────────────────────────────
        proof {
            // Both retained hardware slices are empty, so dropping the zone keeps
            // the dead-slice clauses of `impl_synced` true.
            let tracked ZoneRwContent::<M, P> {
                cpu_mem_set_perm: _,
                iommu_mem_set_perm: _,
                zone_state,
                s2map_tok: _,
                iommu_s2map_tok: _,
            } = zone_content;
            P::remove_zone(&mut content.global_state, zone_state);
            // The writer token and the empty exec memory sets are dropped with the
            // destroyed zone; there is no lock to release afterwards.
        }

        // ── Step 6: restore zone list and release HvMem write lock ───────────
        self.zone_mem_list.put(Tracked(&mut content.zone_list_perm), zones);
        proof {
            let zone_list = content.zone_list_perm@.mem_contents->Init_0;
            // After swap_remove+put: zone_list@ is old_zones with index `i`
            // replaced by the previous last element.
            let new_zones = zone_list@;
            assert(forall|k: int|
                0 <= k < new_zones.len() && k != i ==> new_zones[k] == old_zones[k]);
            assert(i < new_zones.len() ==> new_zones[i as int] == old_zones[old_zones.len() - 1]);
            assert(HvMemPred::<PT, M, A, P, I>::inv(self.lock.k@, content)) by {
                // 1. zone_list_perm.is_init() — from put.
                // 2. pcell matches — from loop invariant.
                assert(content.zone_list_perm@.pcell === self.lock.k@.cell_id);
                // 3. global_wf — from P::remove_zone postcondition.
                // 4. Bijection: zone_ids(new_gs) <-> new_zones.
                assert(forall|z: nat|
                    P::zone_ids(&content.global_state).contains(z) == (exists|k: int|
                        0 <= k < new_zones.len() && #[trigger] new_zones[k].zone_id as nat == z));
                // 5. Spec-instance consistency for all new zones.
                assert(forall|k: int|
                    #![trigger new_zones[k]]
                    0 <= k < new_zones.len() ==> new_zones[k].mem_inst_id()
                        == self.lock.k@.mem_inst_id);
                // 6. Pairwise distinct IDs.
                assert(forall|k: int, l: int|
                    #![auto]
                    0 <= k < new_zones.len() && 0 <= l < new_zones.len() && k != l
                        ==> new_zones[k].zone_id != new_zones[l].zone_id);
                // 7. All zones well-formed.
                assert(forall|k: int| #![auto] 0 <= k < new_zones.len() ==> new_zones[k].wf());
            };
        }
        self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });

        Ok(())
    }

    /// Access the zone identified by `zid` via a scoped callback.
    ///
    /// Holds the HvMem **read** lock for the entire duration of the callback:
    /// - Multiple CPUs may call `with_zone` concurrently (multiple readers allowed).
    /// - `remove_zone` (a writer) is excluded while any callback is running, so
    ///   the zone reference passed to `f` is guaranteed to remain valid.
    ///
    /// Returns `None` if no zone with `zid` is registered; otherwise calls `f`
    /// with a shared reference to the matching zone and returns `Some(f(zone))`.
    pub fn with_zone<R, F: FnOnce(&Zone<PT, M, A, P, I>) -> R>(&self, zid: usize, f: F) -> (res:
        Option<R>)
        requires
            self.invariants(),
            forall|zone: &Zone<PT, M, A, P, I>| #[trigger] f.requires((zone,)) == zone.wf(),
    {
        // ── Acquire HvMem read lock ───────────────────────────────────────────
        let guard = self.lock.lock_read();

        // ── Borrow the zone list via the lock's ghost predicate ───────────────
        let Tracked(content) = guard.borrow(&self.lock);
        let tracked HvMemRwContent::<PT, M, A, P, I> { zone_list_perm, .. } = content;
        let zones = self.zone_mem_list.borrow(Tracked(&zone_list_perm));

        // ── Invoke callback while the read lock is held ───────────────────────
        // The borrow of the selected zone ends when `f` returns (R does not borrow from
        // the zone), so `unlock_read` can safely consume `guard` afterwards.
        let result = match Self::find_zone_index(zones, zid) {
            Some(i) => {
                assert(zones@[i as int].wf());
                Some(f(&zones[i]))
            },
            None => None,
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
impl<PT, M, A, I> HvMem<PT, M, A, BudgetProtocol, I> where
    PT: PageTable<A>,
    M: MemorySet<PT, A, I>,
    A: BitmapAllocator,
    I: HardwareInstr,
 {
    /// Insert `region` into zone `zid` using only the HvMem **read** lock.
    ///
    /// Holding only the read lock lets multiple CPUs insert into **different**
    /// zones simultaneously, as opposed to the generic `insert_region` which
    /// serialises all callers with a write lock.
    ///
    /// Returns `Err(())` if `region` is invalid, the zone is not found, or
    /// `region` overlaps an existing mapping in that zone.
    pub fn insert_region(&self, zid: usize, region: MemoryRegion, mmu: &mut MmuHardware<I>) -> (res:
        Result<(), ()>)
        requires
            self.invariants(),
            zone_regions(zid as nat).contains(region),
            region.spec_within_vspace(self.lock.k@.pt_constants.arch.vspace_size()),
            old(mmu).wf(),
            old(mmu).inst_id() == self.lock.k@.mmu_inst_id,
        ensures
            res is Ok ==> self.invariants(),
            mmu.wf(),
            mmu.inst_id() == old(mmu).inst_id(),
    {
        // ── Step 1: validate region ────────────────────────────────────────────
        if !region.valid() {
            return Err(());
        }
        // ── Step 2: acquire HvMem read lock ───────────────────────────────────

        let guard = self.lock.lock_read();
        let Tracked(content) = guard.borrow(&self.lock);
        let tracked HvMemRwContent::<PT, M, A, BudgetProtocol, I> { zone_list_perm, global_state } =
            content;
        let zones = self.zone_mem_list.borrow(Tracked(&zone_list_perm));

        // ── Step 3: find zone by ID ────────────────────────────────────────────
        let i = match Self::find_zone_index(zones, zid) {
            Some(i) => i,
            None => {
                self.lock.unlock_read(guard);
                return Err(());
            },
        };
        // ── Step 4: delegate to Zone::insert_region ────────────────
        // Zone::insert_region acquires the zone write lock internally
        // and advances the BudgetSpec ghost state via a shared &BudgetGlobalState,
        // so the HvMem read lock is sufficient.

        assert(zones[i as int].zone_id == zid);
        proof {
            // The `HvMemKey::mmu_inst_id` lock-invariant clause pins every zone's MMU
            // instance, and the precondition pins `mmu.inst_id()` to it — so the handle
            // passed here is the one whose `add_vm` minted this zone's slice token.
            assert(zones[i as int].lock.k@.mmu_inst_id == mmu.inst_id());
            assert(zones[i as int].pt_constants() == self.lock.k@.pt_constants);
        }
        let res = zones[i].insert_region(&self.allocator, Tracked(&global_state), region, mmu);

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
    pub fn remove_region(&self, zid: usize, region: MemoryRegion, mmu: &mut MmuHardware<I>) -> (res:
        Result<(), ()>)
        requires
            self.invariants(),
            old(mmu).wf(),
            old(mmu).inst_id() == self.lock.k@.mmu_inst_id,
        ensures
            res is Ok ==> self.invariants(),
            mmu.wf(),
            mmu.inst_id() == old(mmu).inst_id(),
    {
        // ── Step 1: validate region ────────────────────────────────────────────
        if !region.valid() {
            return Err(());
        }
        // ── Step 2: acquire HvMem read lock ───────────────────────────────────

        let guard = self.lock.lock_read();
        let Tracked(content) = guard.borrow(&self.lock);
        let tracked HvMemRwContent::<PT, M, A, BudgetProtocol, I> { zone_list_perm, global_state } =
            content;
        let zones = self.zone_mem_list.borrow(Tracked(&zone_list_perm));

        // ── Step 3: find zone by ID ────────────────────────────────────────────
        let i = match Self::find_zone_index(zones, zid) {
            Some(i) => i,
            None => {
                self.lock.unlock_read(guard);
                return Err(());
            },
        };
        // ── Step 4: delegate to Zone::remove_region ────────────────

        proof {
            // MMU instance-id bridge — see `insert_region`.
            assert(zones[i as int].lock.k@.mmu_inst_id == mmu.inst_id());
        }
        let res = zones[i].remove_region(&self.allocator, Tracked(&global_state), region, mmu);

        self.lock.unlock_read(guard);
        res
    }

    /// Insert `region` into zone `zid`'s IOMMU-visible set using only the HvMem read lock.
    pub fn insert_iommu_region(
        &self,
        zid: usize,
        region: MemoryRegion,
        iommu_mmu: &mut MmuHardware<I>,
    ) -> (res: Result<(), ()>)
        requires
            self.invariants(),
            zone_regions(zid as nat).contains(region) || region == gic_region(),
            region.spec_within_vspace(self.lock.k@.pt_constants.arch.vspace_size()),
            old(iommu_mmu).wf(),
            old(iommu_mmu).inst_id() == self.lock.k@.iommu_mmu_inst_id,
        ensures
            res is Ok ==> self.invariants(),
            iommu_mmu.wf(),
            iommu_mmu.inst_id() == old(iommu_mmu).inst_id(),
    {
        if !region.valid() {
            return Err(());
        }
        let guard = self.lock.lock_read();
        let Tracked(content) = guard.borrow(&self.lock);
        let tracked HvMemRwContent::<PT, M, A, BudgetProtocol, I> { zone_list_perm, global_state } =
            content;
        let zones = self.zone_mem_list.borrow(Tracked(&zone_list_perm));

        let i = match Self::find_zone_index(zones, zid) {
            Some(i) => i,
            None => {
                self.lock.unlock_read(guard);
                return Err(());
            },
        };
        proof {
            // IOMMU instance-id bridge: `HvMemPred` pins every zone's IOMMU instance,
            // and the precondition pins `iommu_mmu.inst_id()` to it.
            assert(zones[i as int].lock.k@.iommu_mmu_inst_id == iommu_mmu.inst_id());
            assert(zones[i as int].pt_constants() == self.lock.k@.pt_constants);
        }
        let res = zones[i].insert_iommu_region(
            &self.allocator,
            Tracked(&global_state),
            region,
            iommu_mmu,
        );
        self.lock.unlock_read(guard);
        res
    }

    /// Remove `region` from zone `zid`'s IOMMU-visible set using only the HvMem read lock.
    pub fn remove_iommu_region(
        &self,
        zid: usize,
        region: MemoryRegion,
        iommu_mmu: &mut MmuHardware<I>,
    ) -> (res: Result<(), ()>)
        requires
            self.invariants(),
            old(iommu_mmu).wf(),
            old(iommu_mmu).inst_id() == self.lock.k@.iommu_mmu_inst_id,
        ensures
            res is Ok ==> self.invariants(),
            iommu_mmu.wf(),
            iommu_mmu.inst_id() == old(iommu_mmu).inst_id(),
    {
        if !region.valid() {
            return Err(());
        }
        let guard = self.lock.lock_read();
        let Tracked(content) = guard.borrow(&self.lock);
        let tracked HvMemRwContent::<PT, M, A, BudgetProtocol, I> { zone_list_perm, global_state } =
            content;
        let zones = self.zone_mem_list.borrow(Tracked(&zone_list_perm));

        let i = match Self::find_zone_index(zones, zid) {
            Some(i) => i,
            None => {
                self.lock.unlock_read(guard);
                return Err(());
            },
        };
        proof {
            assert(zones[i as int].lock.k@.iommu_mmu_inst_id == iommu_mmu.inst_id());
        }
        let res = zones[i].remove_iommu_region(
            &self.allocator,
            Tracked(&global_state),
            region,
            iommu_mmu,
        );
        self.lock.unlock_read(guard);
        res
    }
}

} // verus!
