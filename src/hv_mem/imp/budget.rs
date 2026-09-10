//! Executable operations specific to `BudgetProtocol`.
//!
//! This module keeps the BudgetSpec policy checks and transitions separate from
//! the policy-generic `Zone` and `HvMem` definitions.
extern crate alloc;

use super::{
    mem::{HvMem, HvMemKey, HvMemPred, HvMemRwContent},
    zone::{Zone, ZoneRwContent},
};
use crate::{
    address::{
        addr::{PAddr, SpecVAddr, VAddr},
        frame::{FrameSize, MemAttr, SpecFrame},
        region::MemoryRegion,
    },
    bitmap_allocator::bitmap_trait::BitmapAllocator,
    constants::*,
    global_allocator::GlobalAllocator,
    hardware::{HardwareInstr, MmuHardware},
    hv_mem::{
        protocol::{BudgetGlobalState, BudgetProtocol, ZoneGhostProtocol, ZoneStateOps},
        spec::budget::*,
    },
    memory_set::{MemorySet, SpecMemorySet},
    model::types::{GuestPage, S2Entry, VmId},
    page_table::{PTConstants, PageTable},
    sync::rwlock::{RwLock, RwWriteGuard},
};
use alloc::vec::Vec;
use vstd::{cell::PCell, invariant::InvariantPredicate, prelude::*};

verus! {

use crate::model::convert::*;

/// Concrete `BudgetProtocol` implementation for `Zone`.
///
/// These methods take a shared `Tracked<&BudgetGlobalState>` because the
/// `BudgetSpec` region transitions are zone-local: they only consume/produce the
/// per-zone `zones[zid]` map-sharded token and access `BudgetSpecInstance`
/// (constant-sharded) as a shared reference.
impl<PT, M, A, I, D, IOPT, IOM> Zone<PT, M, A, BudgetProtocol, I, D, IOPT, IOM> where
    PT: PageTable<A>,
    M: MemorySet<PT, A, I>,
    IOPT: PageTable<A>,
    IOM: MemorySet<IOPT, A, I>,
    A: BitmapAllocator,
    I: HardwareInstr,
 {
    /// Insert `region` into this zone's CPU set using only a shared borrow of the global state.
    ///
    /// Returns `Err(())` if `region` is invalid or virtually/physically overlaps
    /// an existing region in this CPU memory set.
    pub fn insert_region(
        &self,
        allocator: &GlobalAllocator<A>,
        Tracked(gs): Tracked<&BudgetGlobalState>,
        region: MemoryRegion,
        mmu: &MmuHardware<I>,
    ) -> (res: Result<(), ()>)
        requires
            self.wf(),
            self.lock.k@.mem_inst_id == BudgetProtocol::mem_inst_id(gs),
            self.lock.k@.alloc_inst_id == allocator.inst_id(),
            self.lock.k@.mmu_inst_id == mmu.inst_id(),
            allocator.invariants(),
            mmu.wf(),
            region_in_budget(self.zone_id as nat, region),
            region.spec_within_vspace(self.vspace_size()),
            M::spec_supports_attr(region.attr),
    {
        if !region.valid() {
            return Err(());
        }
        let (mut mem_set, guard) = self.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, BudgetProtocol, D, IOM> = token.get();

        if mem_set.overlaps_vmem_or_pmem(&region) {
            self.unlock_write(mem_set, RwWriteGuard { handle, token: Tracked(content) });
            return Err(());
        }
        let ghost old_mem_set = mem_set@;
        // Pull this zone's CPU MMU slice token out of the lock content so it can be
        // threaded through `mem_set.insert` (which fires `map`/`map_dsb` per page).

        let tracked ZoneRwContent::<M, BudgetProtocol, D, IOM> {
            cpu_mem_set_perm,
            iommu_mem_set_perm,
            payload_perm,
            zone_state,
            cpu_mmu_tok,
            iommu_mmu_tok,
        } = content;
        let s2_out = mem_set.insert(
            allocator,
            region,
            self.zone_id,
            mmu,
            Tracked(cpu_mmu_tok),
            false,
        );
        let tracked new_cpu_mmu_tok = s2_out.get();

        proof {
            let tracked new_zone_state = BudgetProtocol::cpu_insert_region(gs, zone_state, region);
            content =
            ZoneRwContent::<M, BudgetProtocol, D, IOM> {
                cpu_mem_set_perm,
                iommu_mem_set_perm,
                payload_perm,
                zone_state: new_zone_state,
                cpu_mmu_tok: new_cpu_mmu_tok,
                iommu_mmu_tok,
            };
        }

        self.unlock_write(mem_set, RwWriteGuard { handle, token: Tracked(content) });
        Ok(())
    }

    /// Remove `region` from this zone's CPU set using only a shared borrow of the global state.
    ///
    /// Returns `Err(())` if `region` is invalid or no region starts at `region.vstart`.
    pub fn remove_region(
        &self,
        allocator: &GlobalAllocator<A>,
        Tracked(gs): Tracked<&BudgetGlobalState>,
        region: MemoryRegion,
        mmu: &MmuHardware<I>,
    ) -> (res: Result<(), ()>)
        requires
            self.wf(),
            self.lock.k@.mem_inst_id == BudgetProtocol::mem_inst_id(gs),
            self.lock.k@.alloc_inst_id == allocator.inst_id(),
            self.lock.k@.mmu_inst_id == mmu.inst_id(),
            allocator.invariants(),
            mmu.wf(),
    {
        if !region.valid() {
            return Err(());
        }
        let (mut mem_set, guard) = self.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, BudgetProtocol, D, IOM> = token.get();

        if !mem_set.has_region_starting_at(region.vstart) {
            self.unlock_write(mem_set, RwWriteGuard { handle, token: Tracked(content) });
            return Err(());
        }
        let ghost old_mem_set = mem_set@;
        // Pull this zone's CPU MMU slice token out of the lock content.  Its lock
        // invariant `cpu_mmu_tok.value().s2map == pt_s2map_inner(mem_set@.mappings)` is the
        // sync point, threaded through `mem_set.remove`, which fires
        // `unmap_invalidate` (forced `DSB`+`TLBI`) per page.
        let tracked ZoneRwContent::<M, BudgetProtocol, D, IOM> {
            cpu_mem_set_perm,
            iommu_mem_set_perm,
            payload_perm,
            zone_state,
            cpu_mmu_tok,
            iommu_mmu_tok,
        } = content;
        let s2_out = mem_set.remove(
            allocator,
            region.vstart,
            self.zone_id,
            mmu,
            Tracked(cpu_mmu_tok),
            false,
        );
        let tracked new_cpu_mmu_tok = s2_out.get();

        proof {
            let ghost ghost_region = choose|r: MemoryRegion| #[trigger]
                old_mem_set.regions.contains(r) && r.vstart@ == region.vstart@;
            let tracked new_zone_state = BudgetProtocol::cpu_remove_region(
                gs,
                zone_state,
                ghost_region,
            );
            content =
            ZoneRwContent::<M, BudgetProtocol, D, IOM> {
                cpu_mem_set_perm,
                iommu_mem_set_perm,
                payload_perm,
                zone_state: new_zone_state,
                cpu_mmu_tok: new_cpu_mmu_tok,
                iommu_mmu_tok,
            };
        }

        self.unlock_write(mem_set, RwWriteGuard { handle, token: Tracked(content) });
        Ok(())
    }

    /// Remove every CPU-visible region from this zone.
    pub fn clear(
        &self,
        allocator: &GlobalAllocator<A>,
        Tracked(gs): Tracked<&BudgetGlobalState>,
        mmu: &MmuHardware<I>,
    )
        requires
            self.wf(),
            self.lock.k@.mem_inst_id == BudgetProtocol::mem_inst_id(gs),
            self.lock.k@.alloc_inst_id == allocator.inst_id(),
            self.lock.k@.mmu_inst_id == mmu.inst_id(),
            allocator.invariants(),
            mmu.wf(),
    {
        let (mut mem_set, guard) = self.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, BudgetProtocol, D, IOM> = token.get();
        let tracked ZoneRwContent::<M, BudgetProtocol, D, IOM> {
            cpu_mem_set_perm,
            iommu_mem_set_perm,
            payload_perm,
            zone_state,
            cpu_mmu_tok,
            iommu_mmu_tok,
        } = content;
        let s2_out = mem_set.clear(allocator, self.zone_id, mmu, Tracked(cpu_mmu_tok), false);
        let tracked new_cpu_mmu_tok = s2_out.get();

        proof {
            let tracked new_zone_state = BudgetProtocol::cpu_clear(gs, zone_state);
            content =
            ZoneRwContent::<M, BudgetProtocol, D, IOM> {
                cpu_mem_set_perm,
                iommu_mem_set_perm,
                payload_perm,
                zone_state: new_zone_state,
                cpu_mmu_tok: new_cpu_mmu_tok,
                iommu_mmu_tok,
            };
        }

        self.unlock_write(mem_set, RwWriteGuard { handle, token: Tracked(content) });
    }

    /// Insert `region` into this zone's IOMMU-visible set, forcing the SMMU stage-2
    /// maintenance instructions per page via the IOMMU `MmuHardware` instance.
    /// Same-set virtual or physical overlaps are rejected before insertion.
    pub fn insert_iommu_region(
        &self,
        allocator: &GlobalAllocator<A>,
        Tracked(gs): Tracked<&BudgetGlobalState>,
        region: MemoryRegion,
        iommu_mmu: &MmuHardware<I>,
    ) -> (res: Result<(), ()>)
        requires
            self.wf(),
            self.lock.k@.mem_inst_id == BudgetProtocol::mem_inst_id(gs),
            self.lock.k@.alloc_inst_id == allocator.inst_id(),
            self.lock.k@.iommu_mmu_inst_id == iommu_mmu.inst_id(),
            allocator.invariants(),
            iommu_mmu.wf(),
            region_in_budget(self.zone_id as nat, region),
            region.spec_within_vspace(self.vspace_size()),
            IOM::spec_supports_attr(region.attr),
    {
        if !region.valid() {
            return Err(());
        }
        let (mut mem_set, guard) = self.lock_write_iommu();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, BudgetProtocol, D, IOM> = token.get();

        if mem_set.overlaps_vmem_or_pmem(&region) {
            self.unlock_write_iommu(mem_set, RwWriteGuard { handle, token: Tracked(content) });
            return Err(());
        }
        let ghost old_mem_set = mem_set@;
        // Pull the IOMMU slice token out and thread it through `mem_set.insert` with
        // `iommu = true`, which fires the SMMU `iommu_map_sync` per inserted page.

        let tracked ZoneRwContent::<M, BudgetProtocol, D, IOM> {
            cpu_mem_set_perm,
            iommu_mem_set_perm,
            payload_perm,
            zone_state,
            cpu_mmu_tok,
            iommu_mmu_tok,
        } = content;
        let s2_out = mem_set.insert(
            allocator,
            region,
            self.zone_id,
            iommu_mmu,
            Tracked(iommu_mmu_tok),
            true,
        );
        let tracked new_iommu_mmu_tok = s2_out.get();

        proof {
            let tracked new_zone_state = BudgetProtocol::iommu_insert_region(
                gs,
                zone_state,
                region,
            );
            content =
            ZoneRwContent::<M, BudgetProtocol, D, IOM> {
                cpu_mem_set_perm,
                iommu_mem_set_perm,
                payload_perm,
                zone_state: new_zone_state,
                cpu_mmu_tok,
                iommu_mmu_tok: new_iommu_mmu_tok,
            };
        }

        self.unlock_write_iommu(mem_set, RwWriteGuard { handle, token: Tracked(content) });
        Ok(())
    }

    /// Remove `region` from this zone's IOMMU-visible set, forcing the SMMU stage-2
    /// invalidation per page via the IOMMU `MmuHardware` instance.
    pub fn remove_iommu_region(
        &self,
        allocator: &GlobalAllocator<A>,
        Tracked(gs): Tracked<&BudgetGlobalState>,
        region: MemoryRegion,
        iommu_mmu: &MmuHardware<I>,
    ) -> (res: Result<(), ()>)
        requires
            self.wf(),
            self.lock.k@.mem_inst_id == BudgetProtocol::mem_inst_id(gs),
            self.lock.k@.alloc_inst_id == allocator.inst_id(),
            self.lock.k@.iommu_mmu_inst_id == iommu_mmu.inst_id(),
            allocator.invariants(),
            iommu_mmu.wf(),
    {
        if !region.valid() {
            return Err(());
        }
        let (mut mem_set, guard) = self.lock_write_iommu();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, BudgetProtocol, D, IOM> = token.get();

        if !mem_set.has_region_starting_at(region.vstart) {
            self.unlock_write_iommu(mem_set, RwWriteGuard { handle, token: Tracked(content) });
            return Err(());
        }
        let ghost old_mem_set = mem_set@;
        let tracked ZoneRwContent::<M, BudgetProtocol, D, IOM> {
            cpu_mem_set_perm,
            iommu_mem_set_perm,
            payload_perm,
            zone_state,
            cpu_mmu_tok,
            iommu_mmu_tok,
        } = content;
        let s2_out = mem_set.remove(
            allocator,
            region.vstart,
            self.zone_id,
            iommu_mmu,
            Tracked(iommu_mmu_tok),
            true,
        );
        let tracked new_iommu_mmu_tok = s2_out.get();

        proof {
            let ghost ghost_region = choose|r: MemoryRegion| #[trigger]
                old_mem_set.regions.contains(r) && r.vstart@ == region.vstart@;
            let tracked new_zone_state = BudgetProtocol::iommu_remove_region(
                gs,
                zone_state,
                ghost_region,
            );
            content =
            ZoneRwContent::<M, BudgetProtocol, D, IOM> {
                cpu_mem_set_perm,
                iommu_mem_set_perm,
                payload_perm,
                zone_state: new_zone_state,
                cpu_mmu_tok,
                iommu_mmu_tok: new_iommu_mmu_tok,
            };
        }

        self.unlock_write_iommu(mem_set, RwWriteGuard { handle, token: Tracked(content) });
        Ok(())
    }

    /// Remove every IOMMU-visible region from this zone.
    pub fn clear_iommu(
        &self,
        allocator: &GlobalAllocator<A>,
        Tracked(gs): Tracked<&BudgetGlobalState>,
        iommu_mmu: &MmuHardware<I>,
    )
        requires
            self.wf(),
            self.lock.k@.mem_inst_id == BudgetProtocol::mem_inst_id(gs),
            self.lock.k@.alloc_inst_id == allocator.inst_id(),
            self.lock.k@.iommu_mmu_inst_id == iommu_mmu.inst_id(),
            allocator.invariants(),
            iommu_mmu.wf(),
    {
        let (mut mem_set, guard) = self.lock_write_iommu();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, BudgetProtocol, D, IOM> = token.get();
        let tracked ZoneRwContent::<M, BudgetProtocol, D, IOM> {
            cpu_mem_set_perm,
            iommu_mem_set_perm,
            payload_perm,
            zone_state,
            cpu_mmu_tok,
            iommu_mmu_tok,
        } = content;
        let s2_out = mem_set.clear(
            allocator,
            self.zone_id,
            iommu_mmu,
            Tracked(iommu_mmu_tok),
            true,
        );
        let tracked new_iommu_mmu_tok = s2_out.get();

        proof {
            let tracked new_zone_state = BudgetProtocol::iommu_clear(gs, zone_state);
            content =
            ZoneRwContent::<M, BudgetProtocol, D, IOM> {
                cpu_mem_set_perm,
                iommu_mem_set_perm,
                payload_perm,
                zone_state: new_zone_state,
                cpu_mmu_tok,
                iommu_mmu_tok: new_iommu_mmu_tok,
            };
        }

        self.unlock_write_iommu(mem_set, RwWriteGuard { handle, token: Tracked(content) });
    }
}

/// Concrete `BudgetProtocol` specialisation: mapping operations acquire only
/// the HvMem **read** lock.
///
/// `BudgetSpec::insert_region` / `remove_region` are zone-local transitions:
/// they only touch the per-zone `zones[zid]` map-sharded token and access the
/// `BudgetSpecInstance` (constant-sharded) as a shared reference.  The global
/// `zone_ids_tok` is never modified, so no HvMem write lock is required.
///
/// Locking order: HvMem read lock → zone write lock.
impl<PT, M, A, I, D, IOPT, IOM> HvMem<PT, M, A, BudgetProtocol, I, D, IOPT, IOM> where
    PT: PageTable<A>,
    M: MemorySet<PT, A, I>,
    IOPT: PageTable<A>,
    IOM: MemorySet<IOPT, A, I>,
    A: BitmapAllocator,
    I: HardwareInstr,
 {
    /// Create a new `HvMem` with an empty zone list and a global allocator.
    pub fn new(allocator: GlobalAllocator<A>, pt_constants: PTConstants) -> (res: Self)
        requires
            allocator.invariants(),
            pt_constants@.valid(),
            pt_constants.hva_to_pa_offset_valid(allocator.base@, A::spec_cap() * SPEC_FRAME_SIZE),
            forall|level: nat|
                level < pt_constants.arch@.level_count() ==> pt_constants.arch@.entry_count(level)
                    == 512,
            pt_constants.arch@.leaf_frame_size() == FrameSize::Size4K,
        ensures
            res.invariants(),
            res.lock.k@.pt_constants == pt_constants@,
            res.lock.k@.alloc_inst_id == allocator.inst_id(),
    {
        let (zone_list, Tracked(zone_list_perm)) = PCell::new(Vec::new());
        let ghost zone_list_id = zone_list.id();

        let (cpu_mmu, Tracked(cpu_vm_ids_tok)) = MmuHardware::<I>::new();
        let (iommu_mmu, Tracked(iommu_vm_ids_tok)) = MmuHardware::<I>::new();

        let tracked (Tracked(inst), Tracked(zone_ids_tok), Tracked(zones_tok)) =
            BudgetSpec::Instance::initialize();
        let ghost inst_id = inst.id();

        let tracked budget_global_state = BudgetGlobalState { inst, zone_ids_tok };
        let tracked content = HvMemRwContent::<PT, M, A, BudgetProtocol, I, D, IOPT, IOM> {
            zone_list_perm,
            global_state: budget_global_state,
            cpu_vm_ids_tok,
            iommu_vm_ids_tok,
        };
        let key = Ghost(
            HvMemKey {
                mem_inst_id: inst_id,
                alloc_inst_id: allocator.inst_id(),
                cell_id: zone_list_id,
                mmu_inst_id: cpu_mmu.inst_id(),
                iommu_mmu_inst_id: iommu_mmu.inst_id(),
                pt_constants: pt_constants@,
            },
        );

        proof {
            assert(super::mem::mmu_vm_ids(Set::<nat>::empty()) =~= Set::<VmId>::empty());
            assert(HvMemPred::<PT, M, A, BudgetProtocol, I, D, IOPT, IOM>::inv(key@, content));
        }
        let lock = RwLock::new(key, Tracked(content));
        Self { zone_list, lock, allocator, cpu_mmu, iommu_mmu, pt_constants }
    }

    /// Remove every CPU-visible region from zone `zid`.
    pub fn clear(&self, zid: usize) -> (res: Result<(), ()>)
        requires
            self.invariants(),
    {
        let guard = self.lock.lock_read();
        let Tracked(hv_content) = guard.borrow(&self.lock);
        let tracked HvMemRwContent::<PT, M, A, BudgetProtocol, I, D, IOPT, IOM> {
            zone_list_perm,
            global_state,
            ..
        } = hv_content;
        let zones = self.zone_list.borrow(Tracked(&zone_list_perm));

        let i = match Self::find_zone_index(zones, zid) {
            Some(i) => i,
            None => {
                self.lock.unlock_read(guard);
                return Err(());
            },
        };

        zones[i].clear(&self.allocator, Tracked(&global_state), &self.cpu_mmu);
        self.lock.unlock_read(guard);
        Ok(())
    }

    /// Remove every IOMMU-visible region from zone `zid`.
    pub fn clear_iommu(&self, zid: usize) -> (res: Result<(), ()>)
        requires
            self.invariants(),
    {
        let guard = self.lock.lock_read();
        let Tracked(hv_content) = guard.borrow(&self.lock);
        let tracked HvMemRwContent::<PT, M, A, BudgetProtocol, I, D, IOPT, IOM> {
            zone_list_perm,
            global_state,
            ..
        } = hv_content;
        let zones = self.zone_list.borrow(Tracked(&zone_list_perm));

        let i = match Self::find_zone_index(zones, zid) {
            Some(i) => i,
            None => {
                self.lock.unlock_read(guard);
                return Err(());
            },
        };

        zones[i].clear_iommu(&self.allocator, Tracked(&global_state), &self.iommu_mmu);
        self.lock.unlock_read(guard);
        Ok(())
    }

    /// Translate `vaddr` through zone `zid`'s CPU region set under shared locks.
    pub fn query_vaddr(&self, zid: usize, vaddr: VAddr) -> (res: Result<(PAddr, MemAttr), ()>)
        requires
            self.invariants(),
            vaddr@.0 < self.lock.k@.pt_constants.arch.vspace_size(),
    {
        let guard = self.lock.lock_read();
        let Tracked(content) = guard.borrow(&self.lock);
        let tracked HvMemRwContent::<PT, M, A, BudgetProtocol, I, D, IOPT, IOM> { zone_list_perm, .. } =
            content;
        let zones = self.zone_list.borrow(Tracked(&zone_list_perm));

        let res = match Self::find_zone_index(zones, zid) {
            Some(i) => zones[i].query_vaddr(vaddr),
            None => Err(()),
        };

        self.lock.unlock_read(guard);
        res
    }

    /// Translate `vaddr` through zone `zid`'s IOMMU region set under shared locks.
    pub fn iommu_query_vaddr(&self, zid: usize, vaddr: VAddr) -> (res: Result<(PAddr, MemAttr), ()>)
        requires
            self.invariants(),
            vaddr@.0 < self.lock.k@.pt_constants.arch.vspace_size(),
    {
        let guard = self.lock.lock_read();
        let Tracked(content) = guard.borrow(&self.lock);
        let tracked HvMemRwContent::<PT, M, A, BudgetProtocol, I, D, IOPT, IOM> { zone_list_perm, .. } =
            content;
        let zones = self.zone_list.borrow(Tracked(&zone_list_perm));

        let res = match Self::find_zone_index(zones, zid) {
            Some(i) => zones[i].iommu_query_vaddr(vaddr),
            None => Err(()),
        };

        self.lock.unlock_read(guard);
        res
    }

    /// Insert `region` into zone `zid` using only the HvMem **read** lock.
    ///
    /// Holding only the read lock lets multiple CPUs insert into **different**
    /// zones simultaneously, as opposed to the generic `insert_region` which
    /// serialises all callers with a write lock.
    ///
    /// Returns `Err(())` if `region` is invalid, the zone is not found, or
    /// `region` overlaps an existing CPU region in virtual or physical memory.
    pub fn insert_region(&self, zid: usize, region: MemoryRegion) -> (res: Result<(), ()>)
        requires
            self.invariants(),
            region_in_budget(zid as nat, region),
            region.spec_within_vspace(self.lock.k@.pt_constants.arch.vspace_size()),
            M::spec_supports_attr(region.attr),
    {
        // ── Step 1: validate region ────────────────────────────────────────────
        if !region.valid() {
            return Err(());
        }
        // ── Step 2: acquire HvMem read lock ───────────────────────────────────

        let guard = self.lock.lock_read();
        let Tracked(content) = guard.borrow(&self.lock);
        let tracked HvMemRwContent::<PT, M, A, BudgetProtocol, I, D, IOPT, IOM> {
            zone_list_perm,
            global_state,
            ..
        } = content;
        let zones = self.zone_list.borrow(Tracked(&zone_list_perm));

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

        let res = zones[i].insert_region(
            &self.allocator,
            Tracked(&global_state),
            region,
            &self.cpu_mmu,
        );

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
    {
        // ── Step 1: validate region ────────────────────────────────────────────
        if !region.valid() {
            return Err(());
        }
        // ── Step 2: acquire HvMem read lock ───────────────────────────────────

        let guard = self.lock.lock_read();
        let Tracked(content) = guard.borrow(&self.lock);
        let tracked HvMemRwContent::<PT, M, A, BudgetProtocol, I, D, IOPT, IOM> {
            zone_list_perm,
            global_state,
            ..
        } = content;
        let zones = self.zone_list.borrow(Tracked(&zone_list_perm));

        // ── Step 3: find zone by ID ────────────────────────────────────────────
        let i = match Self::find_zone_index(zones, zid) {
            Some(i) => i,
            None => {
                self.lock.unlock_read(guard);
                return Err(());
            },
        };
        // ── Step 4: delegate to Zone::remove_region ────────────────

        let res = zones[i].remove_region(
            &self.allocator,
            Tracked(&global_state),
            region,
            &self.cpu_mmu,
        );

        self.lock.unlock_read(guard);
        res
    }

    /// Insert `region` into zone `zid`'s IOMMU-visible set using only the HvMem read lock.
    /// Returns `Err(())` for a virtual or physical overlap within that IOMMU set.
    pub fn insert_iommu_region(&self, zid: usize, region: MemoryRegion) -> (res: Result<(), ()>)
        requires
            self.invariants(),
            region_in_budget(zid as nat, region),
            region.spec_within_vspace(self.lock.k@.pt_constants.arch.vspace_size()),
            IOM::spec_supports_attr(region.attr),
    {
        if !region.valid() {
            return Err(());
        }
        let guard = self.lock.lock_read();
        let Tracked(content) = guard.borrow(&self.lock);
        let tracked HvMemRwContent::<PT, M, A, BudgetProtocol, I, D, IOPT, IOM> {
            zone_list_perm,
            global_state,
            ..
        } = content;
        let zones = self.zone_list.borrow(Tracked(&zone_list_perm));

        let i = match Self::find_zone_index(zones, zid) {
            Some(i) => i,
            None => {
                self.lock.unlock_read(guard);
                return Err(());
            },
        };
        let res = zones[i].insert_iommu_region(
            &self.allocator,
            Tracked(&global_state),
            region,
            &self.iommu_mmu,
        );
        self.lock.unlock_read(guard);
        res
    }

    /// Remove `region` from zone `zid`'s IOMMU-visible set using only the HvMem read lock.
    pub fn remove_iommu_region(&self, zid: usize, region: MemoryRegion) -> (res: Result<(), ()>)
        requires
            self.invariants(),
    {
        if !region.valid() {
            return Err(());
        }
        let guard = self.lock.lock_read();
        let Tracked(content) = guard.borrow(&self.lock);
        let tracked HvMemRwContent::<PT, M, A, BudgetProtocol, I, D, IOPT, IOM> {
            zone_list_perm,
            global_state,
            ..
        } = content;
        let zones = self.zone_list.borrow(Tracked(&zone_list_perm));

        let i = match Self::find_zone_index(zones, zid) {
            Some(i) => i,
            None => {
                self.lock.unlock_read(guard);
                return Err(());
            },
        };
        let res = zones[i].remove_iommu_region(
            &self.allocator,
            Tracked(&global_state),
            region,
            &self.iommu_mmu,
        );
        self.lock.unlock_read(guard);
        res
    }
}

} // verus!
