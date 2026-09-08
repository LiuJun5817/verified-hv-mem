//! Concrete synchronization bridge for the current BudgetSpec integration.
//!
//! This module connects lock-resident BudgetSpec/MMU tokens to their two
//! policy-neutral views.  The higher SW+HW refinement in [`super::machine`]
//! intentionally contains only [`SoftwareView`] and [`HardwareView`].
use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;

verus! {

use super::hardware::*;
use super::machine::*;
use super::software::budget::*;
use super::software::SoftwareRefinement;
use crate::bitmap_allocator::bitmap_trait::BitmapAllocator;
use crate::hardware::HardwareInstr;
use crate::hv_mem::protocol::{BudgetProtocol, ZoneStateOps};
use crate::hv_mem::{ZoneKey, ZonePred, ZoneRwContent};
use crate::memory_set::MemorySet;
use crate::model::convert::*;
use crate::model::hardware::HardwareView;
use crate::model::machine::MachineState;
use crate::model::software::SoftwareView;
use crate::model::types::VmId;
use crate::page_table::PageTable;

/// One zone's hardware slices equal the projections of its ghost memory sets.
pub open spec fn zone_maps_synced(hw: HardwareSpec, sw: SoftwareSpec, zid: nat) -> bool {
    &&& hw.mmu.vms.contains_key(VmId(zid))
    &&& hw.mmu.vms[VmId(zid)].s2map == pt_s2map_inner(sw.budget.zones[zid].cpu_mem_set.mappings)
    &&& hw.smmu.vms.contains_key(VmId(zid))
    &&& hw.smmu.vms[VmId(zid)].s2map == pt_s2map_inner(sw.budget.zones[zid].iommu_mem_set.mappings)
}

/// Every hardware slice and every live BudgetSpec zone agree pairwise.
pub open spec fn zonewise_maps_synced(hw: HardwareSpec, sw: SoftwareSpec) -> bool {
    &&& forall|zid: nat| #[trigger]
        sw.budget.zone_ids.contains(zid) ==> zone_maps_synced(hw, sw, zid)
    &&& forall|vm: VmId| #[trigger]
        hw.mmu.vms.contains_key(vm) ==> sw.budget.zone_ids.contains(vm.0)
    &&& forall|vm: VmId| #[trigger]
        hw.smmu.vms.contains_key(vm) ==> sw.budget.zone_ids.contains(vm.0)
}

/// Both flattened hardware maps equal the BudgetSpec projections.
pub open spec fn global_maps_synced(hw: HardwareSpec, sw: SoftwareSpec) -> bool {
    &&& flatten_vm_s2(hw.mmu.vms) == state_s2_map(sw.budget)
    &&& flatten_vm_s2(hw.smmu.vms) == state_iommu_s2_map(sw.budget)
}

/// A zone lock invariant plus token shard identities establishes local sync.
pub proof fn lemma_zone_pred_implies_zone_maps_synced<PT, M, A, I>(
    k: ZoneKey,
    v: ZoneRwContent<M, BudgetProtocol>,
    hw: HardwareSpec,
    sw: SoftwareSpec,
) where PT: PageTable<A>, M: MemorySet<PT, A, I>, A: BitmapAllocator, I: HardwareInstr
    requires
        ZonePred::<PT, M, A, BudgetProtocol, I>::inv(k, v),
        hw.mmu.vms.contains_key(VmId(k.zone_id as nat)),
        hw.mmu.vms[VmId(k.zone_id as nat)] == v.cpu_mmu_tok.value(),
        hw.smmu.vms.contains_key(VmId(k.zone_id as nat)),
        hw.smmu.vms[VmId(k.zone_id as nat)] == v.iommu_mmu_tok.value(),
        sw.budget.zones[k.zone_id as nat] == v.zone_state.ghost_zone(),
    ensures
        zone_maps_synced(hw, sw, k.zone_id as nat),
{
}

/// Zonewise synchronization implies equality of the flattened maps.
pub proof fn lemma_zonewise_maps_synced_implies_global_maps_synced(
    hw: HardwareSpec,
    sw: SoftwareSpec,
)
    requires
        zonewise_maps_synced(hw, sw),
    ensures
        global_maps_synced(hw, sw),
{
    assert(flatten_vm_s2(hw.mmu.vms) =~= state_s2_map(sw.budget));
    assert(flatten_vm_s2(hw.smmu.vms) =~= state_iommu_s2_map(sw.budget));
}

/// Synchronized, invariant concrete specs project to a well-formed machine.
pub proof fn lemma_global_maps_synced_implies_wf_machine(hw: HardwareSpec, sw: SoftwareSpec)
    requires
        hw.invariants(),
        sw.invariants(),
        global_maps_synced(hw, sw),
    ensures
        MachineState::assemble(sw.view(), hw@).wf(),
{
    sw.invariants_imply_view_wf();
    hw.inv_implies_wf();
    lemma_synced_views_wf(sw.view(), hw@);
}

/// Zonewise synchronization establishes both global sync and machine wf.
pub proof fn lemma_zonewise_maps_synced_implies_wf_machine(hw: HardwareSpec, sw: SoftwareSpec)
    requires
        hw.invariants(),
        sw.invariants(),
        zonewise_maps_synced(hw, sw),
    ensures
        global_maps_synced(hw, sw),
        MachineState::assemble(sw.view(), hw@).wf(),
{
    lemma_zonewise_maps_synced_implies_global_maps_synced(hw, sw);
    lemma_global_maps_synced_implies_wf_machine(hw, sw);
}

} // verus!
