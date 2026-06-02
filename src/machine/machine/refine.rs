use vstd::prelude::*;

use super::state::MachineState;
use crate::machine::hardware::HardwareOps;
use crate::machine::hardware::HwView;
use crate::machine::software::SoftwareOps;
use crate::machine::software::SwView;
use crate::machine::types::*;

verus! {

// ---------------------------------------------------------------------------
// Refinement: (SW step + HW step) ⟹ machine step
//
// Each `refine_*` lemma shows that composing the matching software and
// hardware sub-steps produces the corresponding high-level machine step.
// All proof bodies are `admit()` stubs; the intent is to discharge them once
// the wf invariants for SwView, HwView, and MachineState are fully developed.
// ---------------------------------------------------------------------------
// ------------------------------------------------------------------
// Stage-2 mapping management
// ------------------------------------------------------------------
/// A SW map step combined with the HW pending-invalidation side-effect refines
/// the machine-level `hv_map_step`.
pub proof fn refine_hv_map(
    sw1: SwView,
    sw2: SwView,
    hw1: HwView,
    hw2: HwView,
    vm: VmId,
    gpa: GuestPage,
    entry: S2Entry,
)
    requires
        SwView::map_step(sw1, sw2, vm, gpa, entry),
        HwView::pending_invalidation_step(hw1, hw2, vm, gpa),
        MachineState::assemble(sw1, hw1).wf(),
    ensures
        MachineState::hv_map_step(
            MachineState::assemble(sw1, hw1),
            MachineState::assemble(sw2, hw2),
            vm,
            gpa,
            entry,
        ),
{
    admit()
}

/// A SW unmap step combined with the HW pending-invalidation side-effect
/// refines `hv_unmap_step`.
pub proof fn refine_hv_unmap(
    sw1: SwView,
    sw2: SwView,
    hw1: HwView,
    hw2: HwView,
    vm: VmId,
    gpa: GuestPage,
)
    requires
        SwView::unmap_step(sw1, sw2, vm, gpa),
        HwView::pending_invalidation_step(hw1, hw2, vm, gpa),
        MachineState::assemble(sw1, hw1).wf(),
    ensures
        MachineState::hv_unmap_step(
            MachineState::assemble(sw1, hw1),
            MachineState::assemble(sw2, hw2),
            vm,
            gpa,
        ),
{
    admit()
}

// ------------------------------------------------------------------
// Ownership management (pure SW — HW state unchanged)
// ------------------------------------------------------------------
pub proof fn refine_hv_assign_page(sw1: SwView, sw2: SwView, hw: HwView, vm: VmId, page: PhysPage)
    requires
        SwView::assign_page_step(sw1, sw2, vm, page),
        MachineState::assemble(sw1, hw).wf(),
    ensures
        MachineState::hv_assign_page_step(
            MachineState::assemble(sw1, hw),
            MachineState::assemble(sw2, hw),
            vm,
            page,
        ),
{
    admit()
}

pub proof fn refine_hv_reclaim_page(sw1: SwView, sw2: SwView, hw: HwView, vm: VmId, page: PhysPage)
    requires
        SwView::reclaim_page_step(sw1, sw2, vm, page),
        MachineState::assemble(sw1, hw).wf(),
        MachineState::assemble(sw1, hw).page_is_quiescent(page),
    ensures
        MachineState::hv_reclaim_page_step(
            MachineState::assemble(sw1, hw),
            MachineState::assemble(sw2, hw),
            vm,
            page,
        ),
{
    admit()
}

// ------------------------------------------------------------------
// Sharing management (pure SW — HW state unchanged)
// ------------------------------------------------------------------
pub proof fn refine_hv_share_page(
    sw1: SwView,
    sw2: SwView,
    hw: HwView,
    left: VmId,
    right: VmId,
    page: PhysPage,
)
    requires
        SwView::share_page_step(sw1, sw2, left, right, page),
        MachineState::assemble(sw1, hw).wf(),
    ensures
        MachineState::hv_share_page_step(
            MachineState::assemble(sw1, hw),
            MachineState::assemble(sw2, hw),
            left,
            right,
            page,
        ),
{
    admit()
}

pub proof fn refine_hv_unshare_page(
    sw1: SwView,
    sw2: SwView,
    hw: HwView,
    left: VmId,
    right: VmId,
    page: PhysPage,
)
    requires
        SwView::unshare_page_step(sw1, sw2, left, right, page),
        MachineState::assemble(sw1, hw).wf(),
    ensures
        MachineState::hv_unshare_page_step(
            MachineState::assemble(sw1, hw),
            MachineState::assemble(sw2, hw),
            left,
            right,
            page,
        ),
{
    admit()
}

// ------------------------------------------------------------------
// Context switch (pure HW — SW state unchanged)
// ------------------------------------------------------------------
pub proof fn refine_hv_context_switch(sw: SwView, hw1: HwView, hw2: HwView, cpu: CpuId, vm: VmId)
    requires
        HwView::context_switch_step(hw1, hw2, cpu, vm),
        MachineState::assemble(sw, hw1).wf(),
        MachineState::assemble(sw, hw1).all_vms().contains(vm),
    ensures
        MachineState::hv_context_switch_step(
            MachineState::assemble(sw, hw1),
            MachineState::assemble(sw, hw2),
            cpu,
            vm,
        ),
{
    admit()
}

// ------------------------------------------------------------------
// TLB invalidation (pure HW)
// ------------------------------------------------------------------
pub proof fn refine_hw_tlb_invalidate(
    sw: SwView,
    hw1: HwView,
    hw2: HwView,
    cpu: CpuId,
    vm: VmId,
    gpa: GuestPage,
)
    requires
        HwView::tlbi_step(hw1, hw2, cpu, vm, gpa),
        MachineState::assemble(sw, hw1).wf(),
    ensures
        MachineState::hw_tlb_invalidate_step(
            MachineState::assemble(sw, hw1),
            MachineState::assemble(sw, hw2),
            cpu,
            vm,
            gpa,
        ),
{
    admit()
}

} // verus!
