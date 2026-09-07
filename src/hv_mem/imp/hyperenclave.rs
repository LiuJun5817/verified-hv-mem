//! Executable `HvMem` adapter for HyperEnclave's four-class policy.
//!
//! `NORMAL_MEMORY`, `EPC_MEMORY`, `MONITOR_POOL`, and `ALLOCATOR_POOL` are a
//! trusted static partition.  The executable policy never changes that
//! partition and never leaf-maps monitor or page-table backing pages. It
//! dynamically serializes private-page assignment to an enclave.
//!
//! Locking order for mutations is always:
//!
//! `HvMem lock -> one or more Zone locks`.
//!
//! Structural changes and enclave-private insertion take the outer write lock.
//! Zone-local operations take its read lock, allowing independent zones to
//! make progress concurrently. The write lock makes the global overlap scan
//! and subsequent page-table update atomic with respect to all such operations.
extern crate alloc;

use super::{
    mem::{HvMem, HvMemKey, HvMemPred, HvMemRwContent},
    zone::{Zone, ZoneRwContent},
};
use crate::{
    address::{
        addr::{PAddr, VAddr},
        frame::{FrameSize, MemAttr},
        region::MemoryRegion,
    },
    bitmap_allocator::bitmap_trait::BitmapAllocator,
    constants::*,
    global_allocator::GlobalAllocator,
    hardware::{HardwareInstr, MmuHardware},
    hv_mem::{
        protocol::{
            HyperEnclaveGlobalState, HyperEnclaveProtocol, ZoneGhostProtocol, ZoneStateOps,
        },
        spec::hyperenclave::*,
    },
    memory_set::MemorySet,
    model::types::VmId,
    page_table::{PTConstants, PageTable},
    sync::rwlock::{RwLock, RwWriteGuard},
};
use alloc::vec::Vec;
use vstd::{cell::PCell, invariant::InvariantPredicate, prelude::*};

verus! {

use crate::model::convert::*;

impl<PT, M, A, I, D> Zone<PT, M, A, HyperEnclaveProtocol, I, D> where
    PT: PageTable<A>,
    M: MemorySet<PT, A, I>,
    A: BitmapAllocator,
    I: HardwareInstr,
 {
    /// Insert a normal-memory region into the root's CPU page table.
    pub fn insert_normal_region(
        &self,
        allocator: &GlobalAllocator<A>,
        Tracked(gs): Tracked<&HyperEnclaveGlobalState>,
        region: MemoryRegion,
        mmu: &MmuHardware<I>,
    ) -> (res: Result<(), ()>)
        requires
            self.wf(),
            self.zone_id == 0,
            self.lock.k@.mem_inst_id == HyperEnclaveProtocol::mem_inst_id(gs),
            self.lock.k@.alloc_inst_id == allocator.inst_id(),
            self.lock.k@.mmu_inst_id == mmu.inst_id(),
            allocator.invariants(),
            gs.wf(),
            gs.zone_ids().contains(self.zone_id as nat),
            mmu.wf(),
            region_in_normal_memory(region),
            region.spec_within_vspace(self.lock.k@.pt_constants.arch.vspace_size()),
        ensures
            mmu.wf(),
    {
        if !region.valid() {
            return Err(());
        }
        let (mut mem_set, guard) = self.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, HyperEnclaveProtocol, D> = token.get();

        if mem_set.overlaps_vmem(&region) || mem_set.has_region_starting_at(region.vstart) {
            self.unlock_write(
                mem_set,
                RwWriteGuard { handle, token: Tracked(content) },
            );
            return Err(());
        }

        let tracked ZoneRwContent::<M, HyperEnclaveProtocol, D> {
            cpu_mem_set_perm,
            iommu_mem_set_perm,
            payload_perm,
            zone_state,
            cpu_mmu_tok,
            iommu_mmu_tok,
        } = content;
        // Insert the region into the CPU memory set and update the zone state accordingly.
        // Perform the corresponding MMU operations.
        let out = mem_set.insert(allocator, region, 0, mmu, Tracked(cpu_mmu_tok), false);
        let tracked new_cpu_mmu_tok = out.get();
        proof {
            let tracked new_zone_state = gs.cpu_insert_normal_region(zone_state, region);
            content =
            ZoneRwContent::<M, HyperEnclaveProtocol, D> {
                cpu_mem_set_perm,
                iommu_mem_set_perm,
                payload_perm,
                zone_state: new_zone_state,
                cpu_mmu_tok: new_cpu_mmu_tok,
                iommu_mmu_tok,
            };
        }
        self.unlock_write(
            mem_set,
            RwWriteGuard { handle, token: Tracked(content) },
        );
        Ok(())
    }

    /// Insert an enclave-private region into this enclave's CPU page table
    /// after the caller has established the global non-overlap guard.
    fn insert_private_region(
        &self,
        allocator: &GlobalAllocator<A>,
        Tracked(gs): Tracked<&mut HyperEnclaveGlobalState>,
        region: MemoryRegion,
        mmu: &MmuHardware<I>,
    ) -> (res: Result<(), ()>)
        requires
            self.wf(),
            self.zone_id != 0,
            self.lock.k@.mem_inst_id == HyperEnclaveProtocol::mem_inst_id(old(gs)),
            self.lock.k@.alloc_inst_id == allocator.inst_id(),
            self.lock.k@.mmu_inst_id == mmu.inst_id(),
            allocator.invariants(),
            old(gs).wf(),
            old(gs).zone_ids().contains(self.zone_id as nat),
            mmu.wf(),
            region_in_enclave_memory(self.zone_id as nat, region),
            enclave_insert_allowed(old(gs).private_regions_view(), self.zone_id as nat, region),
            region.spec_within_vspace(self.lock.k@.pt_constants.arch.vspace_size()),
        ensures
            gs.wf(),
            gs.mem_inst_id() == old(gs).mem_inst_id(),
            gs.zone_ids() == old(gs).zone_ids(),
            mmu.wf(),
    {
        if !region.valid() {
            return Err(());
        }
        let (mut mem_set, guard) = self.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, HyperEnclaveProtocol, D> = token.get();

        if mem_set.overlaps_vmem(&region) || mem_set.has_region_starting_at(region.vstart)
            || mem_set.overlaps_pmem(&region) {
            self.unlock_write(mem_set, RwWriteGuard { handle, token: Tracked(content) });
            return Err(());
        }

        let tracked ZoneRwContent::<M, HyperEnclaveProtocol, D> {
            cpu_mem_set_perm,
            iommu_mem_set_perm,
            payload_perm,
            zone_state,
            cpu_mmu_tok,
            iommu_mmu_tok,
        } = content;
        let out = mem_set.insert(
            allocator,
            region,
            self.zone_id,
            mmu,
            Tracked(cpu_mmu_tok),
            false,
        );
        let tracked new_cpu_mmu_tok = out.get();
        proof {
            let tracked new_zone_state =
                gs.cpu_insert_enclave_private_region(zone_state, region);
            content =
            ZoneRwContent::<M, HyperEnclaveProtocol, D> {
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

    /// Remove memory `region` from this zone's CPU set
    pub fn remove_region(
        &self,
        allocator: &GlobalAllocator<A>,
        Tracked(gs): Tracked<&HyperEnclaveGlobalState>,
        region: MemoryRegion,
        mmu: &MmuHardware<I>,
    ) -> (res: Result<(), ()>)
        requires
            self.wf(),
            self.lock.k@.mem_inst_id == HyperEnclaveProtocol::mem_inst_id(gs),
            self.lock.k@.alloc_inst_id == allocator.inst_id(),
            self.lock.k@.mmu_inst_id == mmu.inst_id(),
            allocator.invariants(),
            gs.wf(),
            gs.zone_ids().contains(self.zone_id as nat),
            mmu.wf(),
        ensures
            mmu.wf(),
    {
        if !region.valid() {
            return Err(());
        }
        let (mut mem_set, guard) = self.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, HyperEnclaveProtocol, D> = token.get();

        if !mem_set.has_region_starting_at(region.vstart) {
            self.unlock_write(mem_set, RwWriteGuard { handle, token: Tracked(content) });
            return Err(());
        }
        let ghost old_mem_set = mem_set@;

        let tracked ZoneRwContent::<M, HyperEnclaveProtocol, D> {
            cpu_mem_set_perm,
            iommu_mem_set_perm,
            payload_perm,
            zone_state,
            cpu_mmu_tok,
            iommu_mmu_tok,
        } = content;
        // Remove the region from the CPU memory set and update the zone state accordingly.
        // Perform the corresponding MMU operations.
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
            let tracked new_zone_state = gs.cpu_remove_region(
                zone_state,
                ghost_region,
            );
            content =
            ZoneRwContent::<M, HyperEnclaveProtocol, D> {
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

    /// Remove every CPU-visible EPC region from this enclave.
    pub fn clear_epc_regions(
        &self,
        allocator: &GlobalAllocator<A>,
        Tracked(gs): Tracked<&HyperEnclaveGlobalState>,
        mmu: &MmuHardware<I>,
    )
        requires
            self.wf(),
            self.zone_id != 0,
            self.lock.k@.mem_inst_id == HyperEnclaveProtocol::mem_inst_id(gs),
            self.lock.k@.alloc_inst_id == allocator.inst_id(),
            self.lock.k@.mmu_inst_id == mmu.inst_id(),
            allocator.invariants(),
            gs.wf(),
            gs.zone_ids().contains(self.zone_id as nat),
            mmu.wf(),
        ensures
            mmu.wf(),
    {
        let (mut mem_set, guard) = self.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, HyperEnclaveProtocol, D> = token.get();
        let tracked ZoneRwContent::<M, HyperEnclaveProtocol, D> {
            cpu_mem_set_perm,
            iommu_mem_set_perm,
            payload_perm,
            zone_state,
            cpu_mmu_tok,
            iommu_mmu_tok,
        } = content;
        let out = mem_set.clear(
            allocator,
            self.zone_id,
            mmu,
            Tracked(cpu_mmu_tok),
            false,
        );
        let tracked new_cpu_mmu_tok = out.get();
        proof {
            let tracked new_zone_state = gs.cpu_clear_enclave_regions(zone_state);
            content =
            ZoneRwContent::<M, HyperEnclaveProtocol, D> {
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

    /// Insert an IOMMU region backed by DMA-authorized normal memory.
    pub fn insert_iommu_region(
        &self,
        allocator: &GlobalAllocator<A>,
        Tracked(gs): Tracked<&HyperEnclaveGlobalState>,
        region: MemoryRegion,
        iommu_mmu: &MmuHardware<I>,
    ) -> (res: Result<(), ()>)
        requires
            self.wf(),
            self.zone_id == 0,
            self.lock.k@.mem_inst_id == HyperEnclaveProtocol::mem_inst_id(gs),
            self.lock.k@.alloc_inst_id == allocator.inst_id(),
            self.lock.k@.iommu_mmu_inst_id == iommu_mmu.inst_id(),
            allocator.invariants(),
            gs.wf(),
            gs.zone_ids().contains(self.zone_id as nat),
            iommu_mmu.wf(),
            region_in_dma_memory(region),
            region.spec_within_vspace(self.lock.k@.pt_constants.arch.vspace_size()),
        ensures
            iommu_mmu.wf(),
    {
        if !region.valid() {
            return Err(());
        }
        let (mut mem_set, guard) = self.lock_write_iommu();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, HyperEnclaveProtocol, D> = token.get();

        if mem_set.overlaps_vmem(&region) || mem_set.has_region_starting_at(region.vstart)
            || mem_set.overlaps_pmem(&region) {
            self.unlock_write_iommu(mem_set, RwWriteGuard { handle, token: Tracked(content) });
            return Err(());
        }

        let tracked ZoneRwContent::<M, HyperEnclaveProtocol, D> {
            cpu_mem_set_perm,
            iommu_mem_set_perm,
            payload_perm,
            zone_state,
            cpu_mmu_tok,
            iommu_mmu_tok,
        } = content;
        let out = mem_set.insert(
            allocator,
            region,
            self.zone_id,
            iommu_mmu,
            Tracked(iommu_mmu_tok),
            true,
        );
        let tracked new_iommu_mmu_tok = out.get();
        proof {
            let tracked new_zone_state = gs.iommu_insert_region(zone_state, region);
            content =
            ZoneRwContent::<M, HyperEnclaveProtocol, D> {
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

    /// Remove the root IOMMU region that starts at `region.vstart`.
    pub fn remove_iommu_region(
        &self,
        allocator: &GlobalAllocator<A>,
        Tracked(gs): Tracked<&HyperEnclaveGlobalState>,
        region: MemoryRegion,
        iommu_mmu: &MmuHardware<I>,
    ) -> (res: Result<(), ()>)
        requires
            self.wf(),
            self.zone_id == 0,
            self.lock.k@.mem_inst_id == HyperEnclaveProtocol::mem_inst_id(gs),
            self.lock.k@.alloc_inst_id == allocator.inst_id(),
            self.lock.k@.iommu_mmu_inst_id == iommu_mmu.inst_id(),
            allocator.invariants(),
            gs.wf(),
            gs.zone_ids().contains(self.zone_id as nat),
            iommu_mmu.wf(),
        ensures
            iommu_mmu.wf(),
    {
        if !region.valid() {
            return Err(());
        }
        let (mut mem_set, guard) = self.lock_write_iommu();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, HyperEnclaveProtocol, D> = token.get();

        if !mem_set.has_region_starting_at(region.vstart) {
            self.unlock_write_iommu(mem_set, RwWriteGuard { handle, token: Tracked(content) });
            return Err(());
        }
        let ghost old_mem_set = mem_set@;
        let tracked ZoneRwContent::<M, HyperEnclaveProtocol, D> {
            cpu_mem_set_perm,
            iommu_mem_set_perm,
            payload_perm,
            zone_state,
            cpu_mmu_tok,
            iommu_mmu_tok,
        } = content;
        let out = mem_set.remove(
            allocator,
            region.vstart,
            self.zone_id,
            iommu_mmu,
            Tracked(iommu_mmu_tok),
            true,
        );
        let tracked new_iommu_mmu_tok = out.get();
        proof {
            let ghost ghost_region = choose|r: MemoryRegion| #[trigger]
                old_mem_set.regions.contains(r) && r.vstart@ == region.vstart@;
            let tracked new_zone_state = gs.iommu_remove_region(zone_state, ghost_region);
            content =
            ZoneRwContent::<M, HyperEnclaveProtocol, D> {
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

    /// Remove every root IOMMU region from the IOMMU page table.
    pub fn clear_iommu_regions(
        &self,
        allocator: &GlobalAllocator<A>,
        Tracked(gs): Tracked<&HyperEnclaveGlobalState>,
        iommu_mmu: &MmuHardware<I>,
    )
        requires
            self.wf(),
            self.zone_id == 0,
            self.lock.k@.mem_inst_id == HyperEnclaveProtocol::mem_inst_id(gs),
            self.lock.k@.alloc_inst_id == allocator.inst_id(),
            self.lock.k@.iommu_mmu_inst_id == iommu_mmu.inst_id(),
            allocator.invariants(),
            gs.wf(),
            gs.zone_ids().contains(self.zone_id as nat),
            iommu_mmu.wf(),
        ensures
            iommu_mmu.wf(),
    {
        let (mut mem_set, guard) = self.lock_write_iommu();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, HyperEnclaveProtocol, D> = token.get();
        let tracked ZoneRwContent::<M, HyperEnclaveProtocol, D> {
            cpu_mem_set_perm,
            iommu_mem_set_perm,
            payload_perm,
            zone_state,
            cpu_mmu_tok,
            iommu_mmu_tok,
        } = content;
        let out = mem_set.clear(
            allocator,
            self.zone_id,
            iommu_mmu,
            Tracked(iommu_mmu_tok),
            true,
        );
        let tracked new_iommu_mmu_tok = out.get();
        proof {
            let tracked new_zone_state = gs.iommu_clear_regions(zone_state);
            content =
            ZoneRwContent::<M, HyperEnclaveProtocol, D> {
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

impl<PT, M, A, I, D> HvMem<PT, M, A, HyperEnclaveProtocol, I, D> where
    PT: PageTable<A>,
    M: MemorySet<PT, A, I>,
    A: BitmapAllocator,
    I: HardwareInstr,
 {
    /// Create an empty manager. The integration registers root zone zero and
    /// each enclave with the policy-independent [`Self::add_zone`] operation.
    /// Page-table and internal frames are drawn only from the statically
    /// configured global allocator supplied here.
    pub fn new(allocator: GlobalAllocator<A>, pt_constants: PTConstants) -> (res: Self)
        requires
            allocator.invariants(),
            allocator_backing_in_allocator_pool(allocator.base@, A::spec_cap()),
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

        let tracked (
            Tracked(inst),
            Tracked(zone_ids_tok),
            Tracked(_zones_tok),
            Tracked(private_regions_view_tok),
        ) = HyperEnclaveSpec::Instance::initialize();
        let ghost inst_id = inst.id();
        let tracked global_state = HyperEnclaveGlobalState::new(
            inst,
            zone_ids_tok,
            private_regions_view_tok,
        );
        let tracked content = HvMemRwContent::<PT, M, A, HyperEnclaveProtocol, I, D> {
            zone_list_perm,
            global_state,
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
            assert(HvMemPred::<PT, M, A, HyperEnclaveProtocol, I, D>::inv(key@, content));
        }
        let lock = RwLock::new(key, Tracked(content));
        Self { zone_list, lock, allocator, cpu_mmu, iommu_mmu, pt_constants }
    }

    /// Translate `vaddr` through `zone_id`'s CPU page table.
    pub fn query_vaddr(&self, zone_id: usize, vaddr: VAddr) -> (res: Result<(PAddr, MemAttr), ()>)
        requires
            self.invariants(),
            vaddr@.0 < self.lock.k@.pt_constants.arch.vspace_size(),
    {
        let guard = self.lock.lock_read();
        let Tracked(content) = guard.borrow(&self.lock);
        let tracked HvMemRwContent::<PT, M, A, HyperEnclaveProtocol, I, D> { zone_list_perm, .. } =
            content;
        let zones = self.zone_list.borrow(Tracked(&zone_list_perm));
        let res = match Self::find_zone_index(zones, zone_id) {
            Some(i) => zones[i].query_vaddr(vaddr),
            None => Err(()),
        };
        self.lock.unlock_read(guard);
        res
    }

    /// Translate `vaddr` through `zone_id`'s IOMMU page table. HyperEnclave
    /// currently populates only root zone zero's IOMMU table.
    pub fn iommu_query_vaddr(
        &self,
        zone_id: usize,
        vaddr: VAddr,
    ) -> (res: Result<(PAddr, MemAttr), ()>)
        requires
            self.invariants(),
            vaddr@.0 < self.lock.k@.pt_constants.arch.vspace_size(),
    {
        let guard = self.lock.lock_read();
        let Tracked(content) = guard.borrow(&self.lock);
        let tracked HvMemRwContent::<PT, M, A, HyperEnclaveProtocol, I, D> { zone_list_perm, .. } =
            content;
        let zones = self.zone_list.borrow(Tracked(&zone_list_perm));
        let res = match Self::find_zone_index(zones, zone_id) {
            Some(i) => zones[i].iommu_query_vaddr(vaddr),
            None => Err(()),
        };
        self.lock.unlock_read(guard);
        res
    }

    /// Insert statically classified normal memory into the root CPU page table.
    pub fn insert_root_normal_region(&self, region: MemoryRegion) -> (res: Result<(), ()>)
        requires
            self.invariants(),
            region_in_normal_memory(region),
            region.spec_within_vspace(self.lock.k@.pt_constants.arch.vspace_size()),
        ensures
            res is Ok ==> self.invariants(),
    {
        if !region.valid() {
            return Err(());
        }
        let guard = self.lock.lock_read();
        let Tracked(content) = guard.borrow(&self.lock);
        let tracked HvMemRwContent::<PT, M, A, HyperEnclaveProtocol, I, D> {
            zone_list_perm,
            global_state,
            ..
        } = content;
        let zones = self.zone_list.borrow(Tracked(&zone_list_perm));
        // Find the root zone index, which is guaranteed to exist
        let i = match Self::find_zone_index(zones, 0) {
            Some(i) => i,
            None => {
                self.lock.unlock_read(guard);
                return Err(());
            },
        };
        // Acquire zone write lock to insert the normal region
        let res = zones[i].insert_normal_region(
            &self.allocator,
            Tracked(&global_state),
            region,
            &self.cpu_mmu,
        );
        self.lock.unlock_read(guard);
        res
    }

    /// Remove the CPU region that starts at `region.vstart` from `zone_id`.
    /// Zone zero contains root normal memory; nonzero zones contain enclave EPC.
    pub fn remove_region(&self, zone_id: usize, region: MemoryRegion) -> (res: Result<(), ()>)
        requires
            self.invariants(),
        ensures
            res is Ok ==> self.invariants(),
    {
        if !region.valid() {
            return Err(());
        }
        let guard = self.lock.lock_read();
        let Tracked(content) = guard.borrow(&self.lock);
        let tracked HvMemRwContent::<PT, M, A, HyperEnclaveProtocol, I, D> {
            zone_list_perm,
            global_state,
            ..
        } = content;
        let zones = self.zone_list.borrow(Tracked(&zone_list_perm));
        let i = match Self::find_zone_index(zones, zone_id) {
            Some(i) => i,
            None => {
                self.lock.unlock_read(guard);
                return Err(());
            },
        };

        let res = zones[i].remove_region(
            &self.allocator,
            Tracked(&global_state),
            region,
            &self.cpu_mmu,
        );
        self.lock.unlock_read(guard);
        res
    }

    /// Assign an EPC region to one enclave and map it in that enclave's CPU
    /// nested page table.
    pub fn insert_enclave_epc_region(&self, enclave_id: usize, region: MemoryRegion) -> (res: Result<
        (),
        (),
    >)
        requires
            self.invariants(),
            region_in_epc_memory(region),
            region.spec_within_vspace(self.lock.k@.pt_constants.arch.vspace_size()),
        ensures
            res is Ok ==> self.invariants(),
    {
        proof {
            assert(region_in_enclave_memory(enclave_id as nat, region));
        }
        self.insert_enclave_private_region(enclave_id, region)
    }

    /// Assign an enclave GPT backing region through the private
    /// allocator-client interface and map it in that enclave's CPU nested page
    /// table.
    pub fn insert_enclave_allocator_client_region(
        &self,
        enclave_id: usize,
        region: MemoryRegion,
    ) -> (res: Result<(), ()>)
        requires
            self.invariants(),
            region_in_enclave_gpt_backing_frames(enclave_id as nat, region),
            region.spec_within_vspace(self.lock.k@.pt_constants.arch.vspace_size()),
        ensures
            res is Ok ==> self.invariants(),
    {
        proof {
            assert(region_in_enclave_memory(enclave_id as nat, region));
        }
        self.insert_enclave_private_region(enclave_id, region)
    }

    /// Assign an authorized private region to one enclave. Both public
    /// insertion interfaces share this serialized non-overlap proof.
    ///
    /// The complete scan is performed while holding the `HvMem` write lock, so
    /// no competing HyperEnclave mapping operation can pass its check using a
    /// stale snapshot.  The target zone is included in the scan, preventing
    /// physical aliases inside one enclave as well as across enclaves.
    fn insert_enclave_private_region(&self, enclave_id: usize, region: MemoryRegion) -> (res: Result<
        (),
        (),
    >)
        requires
            self.invariants(),
            region_in_enclave_memory(enclave_id as nat, region),
            region.spec_within_vspace(self.lock.k@.pt_constants.arch.vspace_size()),
        ensures
            res is Ok ==> self.invariants(),
    {
        if enclave_id == 0 || !region.valid() {
            return Err(());
        }
        let guard = self.lock.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: HvMemRwContent<PT, M, A, HyperEnclaveProtocol, I, D> = token.get();
        let zones = self.zone_list.borrow(Tracked(&content.zone_list_perm));

        // Dynamic isolation check: scan every live non-root CPU memory set.
        let mut i = 0usize;
        while i < zones.len()
            invariant
                i <= zones.len(),
                region.spec_valid(),
                self.invariants(),
                handle@.instance_id() == self.lock.inst@.id(),
                HvMemPred::<PT, M, A, HyperEnclaveProtocol, I, D>::inv(self.lock.k@, content),
                content.global_state.wf(),
                forall|zid: nat| #[trigger]
                    content.global_state.zone_ids().contains(zid) == (exists|j: int|
                        0 <= j < zones@.len() && #[trigger] zones@[j].zone_id as nat == zid),
                forall|j: int| 0 <= j < zones@.len() ==> #[trigger] zones@[j].wf(),
                forall|j: int|
                    0 <= j < zones@.len() ==> #[trigger] zones@[j].mem_inst_id()
                        == content.global_state.mem_inst_id(),
                forall|j: int, k: int|
                    0 <= j < zones@.len() && 0 <= k < zones@.len() && j != k ==> zones@[j].zone_id
                        != zones@[k].zone_id,
                forall|j: int|
                    0 <= j < i && zones@[j].zone_id != 0 ==> {
                        &&& content.global_state.private_regions_view().contains_key(
                            zones@[j].zone_id as nat,
                        )
                        &&& forall|old_region: MemoryRegion| #[trigger]
                            content.global_state.private_regions_view()[zones@[j].zone_id as nat].contains(
                                old_region,
                            ) ==> !old_region.spec_overlaps_pmem(region)
                    },
            decreases zones.len() - i,
        {
            if zones[i].zone_id != 0 {
                let zone = &zones[i];
                let (mem_set, zone_guard) = zone.lock_write();
                let overlaps = mem_set.overlaps_pmem(&region);
                let ghost scanned_mem_set = mem_set@;
                let ghost old_view = content.global_state.private_regions_view();
                let RwWriteGuard { handle: zone_handle, token: zone_token } = zone_guard;
                let tracked mut zone_content: ZoneRwContent<M, HyperEnclaveProtocol, D> =
                    zone_token.get();
                let tracked ZoneRwContent::<M, HyperEnclaveProtocol, D> {
                    cpu_mem_set_perm,
                    iommu_mem_set_perm,
                    payload_perm,
                    zone_state,
                    cpu_mmu_tok,
                    iommu_mmu_tok,
                } = zone_content;
                proof {
                    assert(zone.zone_id == zones@[i as int].zone_id);
                    assert(zone.wf());
                    assert(content.global_state.zone_ids().contains(zone.zone_id as nat));
                    assert(zone.mem_inst_id() == content.global_state.mem_inst_id());
                    assert(zone_state.wf(content.global_state.mem_inst_id()));
                    assert(zone_state.zone_id() == zone.lock.k@.zone_id);
                    assert(zone.lock.k@.zone_id == zone.zone_id);
                    assert(zone_state.zone_id() == zone.zone_id as nat);
                    let tracked synchronized_zone_state =
                        content.global_state.synchronize_private_regions_view(zone_state);
                    assert(synchronized_zone_state.zone_id() == zone.zone_id as nat);
                    assert(synchronized_zone_state.ghost_zone().cpu_mem_set == scanned_mem_set);
                    assert(content.global_state.private_regions_view().contains_pair(
                        zone.zone_id as nat,
                        synchronized_zone_state.ghost_zone().cpu_mem_set.regions,
                    ));
                    zone_content =
                    ZoneRwContent::<M, HyperEnclaveProtocol, D> {
                        cpu_mem_set_perm,
                        iommu_mem_set_perm,
                        payload_perm,
                        zone_state: synchronized_zone_state,
                        cpu_mmu_tok,
                        iommu_mmu_tok,
                    };
                }
                zone.unlock_write(
                    mem_set,
                    RwWriteGuard { handle: zone_handle, token: Tracked(zone_content) },
                );
                if overlaps {
                    self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });
                    return Err(());
                }
                proof {
                    assert(!scanned_mem_set.overlaps_pmem(region));
                    assert forall|old_region: MemoryRegion| #[trigger]
                        content.global_state.private_regions_view()[zone.zone_id as nat].contains(
                            old_region,
                        ) implies !old_region.spec_overlaps_pmem(region) by {
                        assert(content.global_state.private_regions_view()[zone.zone_id as nat]
                            == scanned_mem_set.regions);
                    }
                    assert forall|j: int| 0 <= j < i + 1 && zones@[j].zone_id != 0 implies {
                        &&& content.global_state.private_regions_view().contains_key(
                            zones@[j].zone_id as nat,
                        )
                        &&& forall|old_region: MemoryRegion| #[trigger]
                            content.global_state.private_regions_view()[zones@[j].zone_id as nat].contains(
                                old_region,
                            ) ==> !old_region.spec_overlaps_pmem(region)
                    } by {
                        if j != i as int {
                            assert(0 <= j < i);
                            assert(zones@[j].zone_id != zones@[i as int].zone_id);
                            assert(content.global_state.private_regions_view()[zones@[j].zone_id as nat]
                                == old_view[zones@[j].zone_id as nat]);
                        } else {
                            assert(zones@[j].zone_id == zone.zone_id);
                        }
                    }
                }
            }
            i += 1;
        }

        let i = match Self::find_zone_index(zones, enclave_id) {
            Some(i) => i,
            None => {
                self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });
                return Err(());
            },
        };
        proof {
            assert(enclave_insert_allowed(
                content.global_state.private_regions_view(),
                enclave_id as nat,
                region,
            )) by {
                assert forall|other_zid: nat, old_region: MemoryRegion|
                    content.global_state.private_regions_view().contains_key(other_zid) && other_zid
                        != root_zone_id()
                        && #[trigger] content.global_state.private_regions_view()[other_zid].contains(
                    old_region) implies !old_region.spec_overlaps_pmem(region) by {
                    assert(content.global_state.zone_ids().contains(other_zid));
                    let j = choose|j: int|
                        0 <= j < zones@.len() && #[trigger] zones@[j].zone_id as nat == other_zid;
                    assert(0 <= j < zones@.len());
                    assert(zones@[j].zone_id != 0);
                    assert(!old_region.spec_overlaps_pmem(region));
                }
            }
        }
        let res = zones[i].insert_private_region(
            &self.allocator,
            Tracked(&mut content.global_state),
            region,
            &self.cpu_mmu,
        );
        self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });
        res
    }

    /// Tear down every CPU mapping of one enclave. Call this before the
    /// policy-independent [`Self::remove_zone`] operation.
    pub fn clear_enclave_private_regions(&self, enclave_id: usize) -> (res: Result<(), ()>)
        requires
            self.invariants(),
        ensures
            res is Ok ==> self.invariants(),
    {
        if enclave_id == 0 {
            return Err(());
        }
        let guard = self.lock.lock_read();
        let Tracked(content) = guard.borrow(&self.lock);
        let tracked HvMemRwContent::<PT, M, A, HyperEnclaveProtocol, I, D> {
            zone_list_perm,
            global_state,
            ..
        } = content;
        let zones = self.zone_list.borrow(Tracked(&zone_list_perm));
        let i = match Self::find_zone_index(zones, enclave_id) {
            Some(i) => i,
            None => {
                self.lock.unlock_read(guard);
                return Err(());
            },
        };

        zones[i].clear_epc_regions(
            &self.allocator,
            Tracked(&global_state),
            &self.cpu_mmu,
        );
        self.lock.unlock_read(guard);
        Ok(())
    }

    /// Insert a root IOMMU region backed by DMA-authorized normal memory. There
    /// is intentionally no enclave-IOMMU counterpart.
    pub fn insert_root_iommu_region(&self, region: MemoryRegion) -> (res: Result<(), ()>)
        requires
            self.invariants(),
            region_in_dma_memory(region),
            region.spec_within_vspace(self.lock.k@.pt_constants.arch.vspace_size()),
        ensures
            res is Ok ==> self.invariants(),
    {
        if !region.valid() {
            return Err(());
        }
        let guard = self.lock.lock_read();
        let Tracked(content) = guard.borrow(&self.lock);
        let tracked HvMemRwContent::<PT, M, A, HyperEnclaveProtocol, I, D> {
            zone_list_perm,
            global_state,
            ..
        } = content;
        let zones = self.zone_list.borrow(Tracked(&zone_list_perm));
        let i = match Self::find_zone_index(zones, 0) {
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

    /// Remove the root IOMMU region that starts at `region.vstart`.
    pub fn remove_root_iommu_region(&self, region: MemoryRegion) -> (res: Result<(), ()>)
        requires
            self.invariants(),
        ensures
            res is Ok ==> self.invariants(),
    {
        if !region.valid() {
            return Err(());
        }
        let guard = self.lock.lock_read();
        let Tracked(content) = guard.borrow(&self.lock);
        let tracked HvMemRwContent::<PT, M, A, HyperEnclaveProtocol, I, D> {
            zone_list_perm,
            global_state,
            ..
        } = content;
        let zones = self.zone_list.borrow(Tracked(&zone_list_perm));
        let i = match Self::find_zone_index(zones, 0) {
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

    /// Tear down every root-cell IOMMU mapping.
    pub fn clear_root_iommu_regions(&self) -> (res: Result<(), ()>)
        requires
            self.invariants(),
        ensures
            res is Ok ==> self.invariants(),
    {
        let guard = self.lock.lock_read();
        let Tracked(content) = guard.borrow(&self.lock);
        let tracked HvMemRwContent::<PT, M, A, HyperEnclaveProtocol, I, D> {
            zone_list_perm,
            global_state,
            ..
        } = content;
        let zones = self.zone_list.borrow(Tracked(&zone_list_perm));
        let i = match Self::find_zone_index(zones, 0) {
            Some(i) => i,
            None => {
                self.lock.unlock_read(guard);
                return Err(());
            },
        };

        zones[i].clear_iommu_regions(
            &self.allocator,
            Tracked(&global_state),
            &self.iommu_mmu,
        );
        self.lock.unlock_read(guard);
        Ok(())
    }
}

} // verus!
