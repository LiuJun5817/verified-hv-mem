//! Machine-refinement layer: `(SoftwareView, HardwareView)` → [`MachineState`].
//!
//! Everything here is expressed only over the policy-neutral views, in two
//! groups:
//!
//! 1. **Per-operation refinement** — each `refine_hv_*` lemma composes a
//!    `SoftwareView` step with the matching `HardwareView` step into the
//!    corresponding `MachineState::hv_*` step.
//! 2. **Region → per-page machine traces** — each bulk CPU/IOMMU region
//!    transition refines to a recursive [`run_op_sequence`] containing one
//!    combined machine action per page.
//!
//! The `refine_hv_*` family, eight region trace lemmas, and synchronization
//! endpoints are the module's refinement results.
use vstd::prelude::*;

verus! {

use crate::model::hardware::{proof::*, HardwareView};
use crate::model::machine::MachineState;
use crate::model::software::proof::*;
use crate::model::software::*;
use crate::model::types::{
    CpuId,
    GuestPage,
    HypervisorOp,
    MachineAction,
    PhysPage,
    S2Entry,
    TlbKey,
    VmId,
    VmMemOp,
    VmPageKey,
};

/// Bridge: the assembled machine state's SW-side `wf` clauses *are* the software
/// view's, because `assemble` copies the SW fields verbatim and both views define
/// the predicates identically.
pub proof fn lemma_sw_machine_wf_equiv(sw: SoftwareView, hw: HardwareView)
    ensures
        MachineState::assemble(sw, hw).s2_classification_wf() == sw.s2_classification_wf(),
        MachineState::assemble(sw, hw).translation_wf() == sw.translation_wf(),
        MachineState::assemble(sw, hw).iommu_classification_wf() == sw.iommu_classification_wf(),
        MachineState::assemble(sw, hw).iommu_translation_wf() == sw.iommu_translation_wf(),
        MachineState::assemble(sw, hw).iommu_wf() == sw.iommu_wf(),
{
    let m = MachineState::assemble(sw, hw);
    assert(m.all_vms == sw.all_vms);
    assert(m.s2_private_pages == sw.s2_private_pages);
    assert(m.s2_shared_pages == sw.s2_shared_pages);
    assert(m.s2_map == sw.s2_map);
    // `s2_private_or_shared` coincides because both private and shared page sets are copied.
    assert(forall|vm: VmId, page: PhysPage| #[trigger]
        m.s2_private_or_shared(vm, page) == sw.s2_private_or_shared(vm, page));
    assert(m.iommu_s2_map == sw.iommu_s2_map);
    assert(m.iommu_private_pages == sw.iommu_private_pages);
    assert(m.iommu_shared_pages == sw.iommu_shared_pages);
}

/// A well-formed machine state implies that its hardware view is well-formed.
proof fn lemma_machine_hw_wf(sw: SoftwareView, hw: HardwareView)
    requires
        MachineState::assemble(sw, hw).wf(),
    ensures
        hw.wf(),
{
    let m = MachineState::assemble(sw, hw);
    assert(hw.tlb_safe()) by {
        assert forall|k: TlbKey| #[trigger] hw.tlb.contains_key(k) implies {
            let sk = VmPageKey::new(k.vm, k.gpa);
            &&& hw.s2map.contains_key(sk)
            &&& hw.tlb[k].as_s2_entry() == hw.s2map[sk]
        } by {
            assert(m.tlb.contains_key(k));
        }
    }
    assert(hw.iommu_tlb_safe()) by {
        assert forall|k: TlbKey| #[trigger] hw.iommu_tlb.contains_key(k) implies {
            let sk = VmPageKey::new(k.vm, k.gpa);
            &&& hw.iommu_s2map.contains_key(sk)
            &&& hw.iommu_tlb[k].as_s2_entry() == hw.iommu_s2map[sk]
        } by {
            assert(m.iommu_tlb.contains_key(k));
        }
    }
}

/// A software view and a hardware view that are each internally well-formed and *synced*
/// assemble into a `wf` `MachineState`.
///
/// Concrete integrations establish the two view equalities at their synchronization
/// boundary; this lemma turns those policy-neutral facts into the full machine `wf`.
pub proof fn lemma_synced_views_wf(sw: SoftwareView, hw: HardwareView)
    requires
        sw.wf(),
        hw.wf(),
        hw.s2map == sw.s2_map,
        hw.iommu_s2map == sw.iommu_s2_map,
    ensures
        MachineState::assemble(sw, hw).wf(),
{
    lemma_sw_machine_wf_equiv(sw, hw);
}

// ---------------------------------------------------------------------------
// §1  Per-operation refinement: (SW step + HW step) ⟹ machine step
//
// One lemma per hypervisor operation. Private classification and mapping are
// combined in both views; each mapping operation pairs one SW step with one HW
// step. VM lifecycle operations leave the hardware view unchanged.
// ---------------------------------------------------------------------------
// ── stage-2 maintenance (SW + HW step) ──────────────────────────────────────
/// A combined software CPU S2-Private map and hardware page-table update refine
/// one atomic machine operation.
pub proof fn refine_hv_map_s2_private(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw1: HardwareView,
    hw2: HardwareView,
    vm: VmId,
    gpa: GuestPage,
    entry: S2Entry,
)
    requires
        SoftwareView::map_s2_private_step(sw1, sw2, vm, gpa, entry),
        HardwareView::map_step(hw1, hw2, vm, gpa, entry),
        MachineState::assemble(sw1, hw1).wf(),
    ensures
        MachineState::hv_map_s2_private_step(
            MachineState::assemble(sw1, hw1),
            MachineState::assemble(sw2, hw2),
            vm,
            gpa,
            entry,
        ),
{
    let s1 = MachineState::assemble(sw1, hw1);
    let s2 = MachineState::assemble(sw2, hw2);
    let key = VmPageKey::new(vm, gpa);
    let targets = s1.invalidation_targets(vm, gpa);

    lemma_sw_machine_wf_equiv(sw1, hw1);
    lemma_machine_hw_wf(sw1, hw1);
    lemma_map_s2_private_step_preserves_wf(sw1, sw2, vm, gpa, entry);

    assert(s1.tlb_safe());
    assert(!hw1.s2map.contains_key(key));
    assert forall|k: TlbKey| #[trigger] s1.tlb.contains_key(k) implies !targets.contains(k) by {
        if targets.contains(k) {
            assert(s1.hw_s2map.contains_key(VmPageKey::new(k.vm, k.gpa)));
        }
    }
    assert(s2.tlb =~= s1.tlb.remove_keys(targets));

    lemma_map_preserves_wf(hw1, hw2, vm, gpa, entry);
    lemma_synced_views_wf(sw2, hw2);
}

/// A combined software CPU S2-Private unmap/release and hardware invalidate
/// refine one atomic machine operation.
pub proof fn refine_hv_unmap_s2_private(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw1: HardwareView,
    hw2: HardwareView,
    vm: VmId,
    gpa: GuestPage,
    page: PhysPage,
)
    requires
        SoftwareView::unmap_s2_private_step(sw1, sw2, vm, gpa, page),
        HardwareView::unmap_invalidate_step(hw1, hw2, vm, gpa),
        MachineState::assemble(sw1, hw1).wf(),
    ensures
        MachineState::hv_unmap_s2_private_step(
            MachineState::assemble(sw1, hw1),
            MachineState::assemble(sw2, hw2),
            vm,
            gpa,
            page,
        ),
{
    let s1 = MachineState::assemble(sw1, hw1);
    let s2 = MachineState::assemble(sw2, hw2);
    let targets = s1.invalidation_targets(vm, gpa);

    lemma_sw_machine_wf_equiv(sw1, hw1);
    lemma_machine_hw_wf(sw1, hw1);
    lemma_unmap_s2_private_step_preserves_wf(sw1, sw2, vm, gpa, page);
    assert(s2.tlb =~= s1.tlb.remove_keys(targets));

    lemma_unmap_invalidate_preserves_wf(hw1, hw2, vm, gpa);
    lemma_synced_views_wf(sw2, hw2);
}

/// A combined software IOMMU-Private map and hardware SMMU update refine one
/// atomic machine operation.
pub proof fn refine_hv_map_iommu_private(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw1: HardwareView,
    hw2: HardwareView,
    vm: VmId,
    gpa: GuestPage,
    entry: S2Entry,
)
    requires
        SoftwareView::map_iommu_private_step(sw1, sw2, vm, gpa, entry),
        HardwareView::iommu_map_step(hw1, hw2, vm, gpa, entry),
        MachineState::assemble(sw1, hw1).wf(),
    ensures
        MachineState::hv_map_iommu_private_step(
            MachineState::assemble(sw1, hw1),
            MachineState::assemble(sw2, hw2),
            vm,
            gpa,
            entry,
        ),
{
    let s1 = MachineState::assemble(sw1, hw1);
    let s2 = MachineState::assemble(sw2, hw2);
    let key = VmPageKey::new(vm, gpa);
    let targets = s1.iommu_invalidation_targets(vm, gpa);

    lemma_sw_machine_wf_equiv(sw1, hw1);
    lemma_machine_hw_wf(sw1, hw1);
    lemma_map_iommu_private_step_preserves_wf(sw1, sw2, vm, gpa, entry);

    assert(s1.iommu_tlb_safe());
    assert(!hw1.iommu_s2map.contains_key(key));
    assert forall|k: TlbKey| #[trigger] s1.iommu_tlb.contains_key(k) implies !targets.contains(
        k,
    ) by {
        if targets.contains(k) {
            assert(s1.iommu_hw_s2map.contains_key(VmPageKey::new(k.vm, k.gpa)));
        }
    }
    assert(s2.iommu_tlb =~= s1.iommu_tlb.remove_keys(targets));

    lemma_iommu_map_preserves_wf(hw1, hw2, vm, gpa, entry);
    lemma_synced_views_wf(sw2, hw2);
}

/// A combined software IOMMU-Private unmap/release and hardware invalidate
/// refine one atomic machine operation.
pub proof fn refine_hv_unmap_iommu_private(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw1: HardwareView,
    hw2: HardwareView,
    vm: VmId,
    gpa: GuestPage,
    page: PhysPage,
)
    requires
        SoftwareView::unmap_iommu_private_step(sw1, sw2, vm, gpa, page),
        HardwareView::iommu_unmap_invalidate_step(hw1, hw2, vm, gpa),
        MachineState::assemble(sw1, hw1).wf(),
    ensures
        MachineState::hv_unmap_iommu_private_step(
            MachineState::assemble(sw1, hw1),
            MachineState::assemble(sw2, hw2),
            vm,
            gpa,
            page,
        ),
{
    let s1 = MachineState::assemble(sw1, hw1);
    let s2 = MachineState::assemble(sw2, hw2);
    let targets = s1.iommu_invalidation_targets(vm, gpa);

    lemma_sw_machine_wf_equiv(sw1, hw1);
    lemma_machine_hw_wf(sw1, hw1);
    lemma_unmap_iommu_private_step_preserves_wf(sw1, sw2, vm, gpa, page);
    assert(s2.iommu_tlb =~= s1.iommu_tlb.remove_keys(targets));

    lemma_iommu_unmap_invalidate_preserves_wf(hw1, hw2, vm, gpa);
    lemma_synced_views_wf(sw2, hw2);
}

/// A CPU shared SoftwareView map and its hardware page-table update
/// refine the corresponding atomic machine operation.
pub proof fn refine_hv_map_s2_shared(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw1: HardwareView,
    hw2: HardwareView,
    vm: VmId,
    gpa: GuestPage,
    entry: S2Entry,
)
    requires
        SoftwareView::map_s2_shared_step(sw1, sw2, vm, gpa, entry),
        HardwareView::map_step(hw1, hw2, vm, gpa, entry),
        MachineState::assemble(sw1, hw1).wf(),
    ensures
        MachineState::hv_map_s2_shared_step(
            MachineState::assemble(sw1, hw1),
            MachineState::assemble(sw2, hw2),
            vm,
            gpa,
            entry,
        ),
{
    let s1 = MachineState::assemble(sw1, hw1);
    let s2 = MachineState::assemble(sw2, hw2);
    let key = VmPageKey::new(vm, gpa);
    let targets = s1.invalidation_targets(vm, gpa);

    lemma_sw_machine_wf_equiv(sw1, hw1);
    lemma_machine_hw_wf(sw1, hw1);
    lemma_map_s2_shared_step_preserves_wf(sw1, sw2, vm, gpa, entry);
    assert(s1.tlb_safe());
    assert(!hw1.s2map.contains_key(key));
    assert forall|k: TlbKey| #[trigger] s1.tlb.contains_key(k) implies !targets.contains(k) by {
        if targets.contains(k) {
            assert(s1.hw_s2map.contains_key(VmPageKey::new(k.vm, k.gpa)));
        }
    }
    assert(s2.tlb =~= s1.tlb.remove_keys(targets));
    lemma_map_preserves_wf(hw1, hw2, vm, gpa, entry);
    lemma_synced_views_wf(sw2, hw2);
}

/// A CPU shared SoftwareView unmap and hardware invalidate refine the
/// corresponding atomic machine operation.
pub proof fn refine_hv_unmap_s2_shared(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw1: HardwareView,
    hw2: HardwareView,
    vm: VmId,
    gpa: GuestPage,
)
    requires
        SoftwareView::unmap_s2_shared_step(sw1, sw2, vm, gpa),
        HardwareView::unmap_invalidate_step(hw1, hw2, vm, gpa),
        MachineState::assemble(sw1, hw1).wf(),
    ensures
        MachineState::hv_unmap_s2_shared_step(
            MachineState::assemble(sw1, hw1),
            MachineState::assemble(sw2, hw2),
            vm,
            gpa,
        ),
{
    let s1 = MachineState::assemble(sw1, hw1);
    let s2 = MachineState::assemble(sw2, hw2);
    let targets = s1.invalidation_targets(vm, gpa);

    lemma_sw_machine_wf_equiv(sw1, hw1);
    lemma_machine_hw_wf(sw1, hw1);
    lemma_unmap_s2_shared_step_preserves_wf(sw1, sw2, vm, gpa);
    assert(s2.tlb =~= s1.tlb.remove_keys(targets));
    lemma_unmap_invalidate_preserves_wf(hw1, hw2, vm, gpa);
    lemma_synced_views_wf(sw2, hw2);
}

/// A software-only S2-Private-to-Shared classification transfer refines one
/// machine operation while leaving the hardware view unchanged.
pub proof fn refine_hv_make_s2_shared(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw: HardwareView,
    vm: VmId,
    page: PhysPage,
)
    requires
        SoftwareView::make_s2_shared_step(sw1, sw2, vm, page),
        MachineState::assemble(sw1, hw).wf(),
    ensures
        MachineState::hv_make_s2_shared_step(
            MachineState::assemble(sw1, hw),
            MachineState::assemble(sw2, hw),
            vm,
            page,
        ),
{
    lemma_sw_machine_wf_equiv(sw1, hw);
    lemma_machine_hw_wf(sw1, hw);
    lemma_make_s2_shared_step_preserves_wf(sw1, sw2, vm, page);
    lemma_synced_views_wf(sw2, hw);
}

/// A software-only S2-Shared-to-Private classification transfer refines one
/// machine operation while leaving the hardware view unchanged.
pub proof fn refine_hv_make_s2_private(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw: HardwareView,
    vm: VmId,
    page: PhysPage,
)
    requires
        SoftwareView::make_s2_private_step(sw1, sw2, vm, page),
        MachineState::assemble(sw1, hw).wf(),
    ensures
        MachineState::hv_make_s2_private_step(
            MachineState::assemble(sw1, hw),
            MachineState::assemble(sw2, hw),
            vm,
            page,
        ),
{
    lemma_sw_machine_wf_equiv(sw1, hw);
    lemma_machine_hw_wf(sw1, hw);
    lemma_make_s2_private_step_preserves_wf(sw1, sw2, vm, page);
    lemma_synced_views_wf(sw2, hw);
}

/// An IOMMU shared SoftwareView map and hardware SMMU update refine the
/// corresponding atomic machine operation.
pub proof fn refine_hv_map_iommu_shared(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw1: HardwareView,
    hw2: HardwareView,
    vm: VmId,
    gpa: GuestPage,
    entry: S2Entry,
)
    requires
        SoftwareView::map_iommu_shared_step(sw1, sw2, vm, gpa, entry),
        HardwareView::iommu_map_step(hw1, hw2, vm, gpa, entry),
        MachineState::assemble(sw1, hw1).wf(),
    ensures
        MachineState::hv_map_iommu_shared_step(
            MachineState::assemble(sw1, hw1),
            MachineState::assemble(sw2, hw2),
            vm,
            gpa,
            entry,
        ),
{
    let s1 = MachineState::assemble(sw1, hw1);
    let s2 = MachineState::assemble(sw2, hw2);
    let key = VmPageKey::new(vm, gpa);
    let targets = s1.iommu_invalidation_targets(vm, gpa);

    lemma_sw_machine_wf_equiv(sw1, hw1);
    lemma_machine_hw_wf(sw1, hw1);
    lemma_map_iommu_shared_step_preserves_wf(sw1, sw2, vm, gpa, entry);
    assert(s1.iommu_tlb_safe());
    assert(!hw1.iommu_s2map.contains_key(key));
    assert forall|k: TlbKey| #[trigger] s1.iommu_tlb.contains_key(k) implies !targets.contains(
        k,
    ) by {
        if targets.contains(k) {
            assert(s1.iommu_hw_s2map.contains_key(VmPageKey::new(k.vm, k.gpa)));
        }
    }
    assert(s2.iommu_tlb =~= s1.iommu_tlb.remove_keys(targets));
    lemma_iommu_map_preserves_wf(hw1, hw2, vm, gpa, entry);
    lemma_synced_views_wf(sw2, hw2);
}

/// An IOMMU shared SoftwareView unmap and hardware invalidate refine the
/// corresponding atomic machine operation.
pub proof fn refine_hv_unmap_iommu_shared(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw1: HardwareView,
    hw2: HardwareView,
    vm: VmId,
    gpa: GuestPage,
)
    requires
        SoftwareView::unmap_iommu_shared_step(sw1, sw2, vm, gpa),
        HardwareView::iommu_unmap_invalidate_step(hw1, hw2, vm, gpa),
        MachineState::assemble(sw1, hw1).wf(),
    ensures
        MachineState::hv_unmap_iommu_shared_step(
            MachineState::assemble(sw1, hw1),
            MachineState::assemble(sw2, hw2),
            vm,
            gpa,
        ),
{
    let s1 = MachineState::assemble(sw1, hw1);
    let s2 = MachineState::assemble(sw2, hw2);
    let targets = s1.iommu_invalidation_targets(vm, gpa);

    lemma_sw_machine_wf_equiv(sw1, hw1);
    lemma_machine_hw_wf(sw1, hw1);
    lemma_unmap_iommu_shared_step_preserves_wf(sw1, sw2, vm, gpa);
    assert(s2.iommu_tlb =~= s1.iommu_tlb.remove_keys(targets));
    lemma_iommu_unmap_invalidate_preserves_wf(hw1, hw2, vm, gpa);
    lemma_synced_views_wf(sw2, hw2);
}

// ── VM lifecycle (pure SW — HW unchanged) ───────────────────────────────────
/// Registering a fresh VM refines `hv_add_vm_step`. The new VM has no Private
/// pages or mappings; the SW clauses come via the bridge and hardware coherence carries
/// over unchanged.
pub proof fn refine_hv_add_vm(sw1: SoftwareView, sw2: SoftwareView, hw: HardwareView, vm: VmId)
    requires
        SoftwareView::add_vm_enabled(sw1, vm),
        SoftwareView::add_vm_step(sw1, sw2, vm),
        MachineState::assemble(sw1, hw).wf(),
    ensures
        MachineState::hv_add_vm_step(
            MachineState::assemble(sw1, hw),
            MachineState::assemble(sw2, hw),
            vm,
        ),
{
    let s1 = MachineState::assemble(sw1, hw);
    let s2 = MachineState::assemble(sw2, hw);
    lemma_sw_machine_wf_equiv(sw1, hw);
    lemma_machine_hw_wf(sw1, hw);
    lemma_add_vm_step_preserves_wf(sw1, sw2, vm);
    lemma_synced_views_wf(sw2, hw);
}

/// Deregistering an empty VM refines `hv_remove_vm_step`.  Beyond the SW
/// `remove_vm_enabled` condition, the machine step also requires that `vm` has no
/// cached TLB entry, so dropping it strands no hardware translation reference.
pub proof fn refine_hv_remove_vm(sw1: SoftwareView, sw2: SoftwareView, hw: HardwareView, vm: VmId)
    requires
        SoftwareView::remove_vm_enabled(sw1, vm),
        SoftwareView::remove_vm_step(sw1, sw2, vm),
        MachineState::assemble(sw1, hw).wf(),
        forall|k: TlbKey| #[trigger]
            MachineState::assemble(sw1, hw).tlb.contains_key(k) ==> k.vm != vm,
    ensures
        MachineState::hv_remove_vm_step(
            MachineState::assemble(sw1, hw),
            MachineState::assemble(sw2, hw),
            vm,
        ),
{
    let s1 = MachineState::assemble(sw1, hw);
    let s2 = MachineState::assemble(sw2, hw);
    lemma_sw_machine_wf_equiv(sw1, hw);
    lemma_machine_hw_wf(sw1, hw);
    lemma_remove_vm_step_preserves_wf(sw1, sw2, vm);
    lemma_synced_views_wf(sw2, hw);
}

// ---------------------------------------------------------------------------
// §3  Shared region-trace machinery
//
/// Execute a finite sequence of machine actions.
pub open spec fn run_op_sequence(
    start: MachineState,
    end: MachineState,
    ops: Seq<MachineAction>,
) -> bool
    decreases ops.len(),
{
    if ops.len() == 0 {
        start == end
    } else {
        exists|next: MachineState|
            MachineState::step(start, next, ops[0]) && run_op_sequence(next, end, ops.skip(1))
    }
}

/// Convert an explicit sequence of adjacent machine states into the recursive
/// operation-sequence relation. This is the only recursion needed by the eight
/// region proofs.
pub proof fn lemma_run_op_sequence_from_states(states: Seq<MachineState>, ops: Seq<MachineAction>)
    requires
        states.len() == ops.len() + 1,
        forall|i: int|
            0 <= i < ops.len() ==> #[trigger] MachineState::step(states[i], states[i + 1], ops[i]),
    ensures
        run_op_sequence(states[0], states[states.len() - 1], ops),
    decreases ops.len(),
{
    if ops.len() == 0 {
        assert(states.len() == 1);
    } else {
        let tail_states = states.skip(1);
        let tail_ops = ops.skip(1);
        assert(tail_states.len() == tail_ops.len() + 1);
        assert forall|i: int| 0 <= i < tail_ops.len() implies #[trigger] MachineState::step(
            tail_states[i],
            tail_states[i + 1],
            tail_ops[i],
        ) by {
            assert(0 <= i + 1 < ops.len());
            assert(tail_states[i] == states[i + 1]);
            assert(tail_states[i + 1] == states[i + 2]);
            assert(tail_ops[i] == ops[i + 1]);
            assert(MachineState::step(states[i + 1], states[i + 2], ops[i + 1]));
        }
        lemma_run_op_sequence_from_states(tail_states, tail_ops);
        assert(tail_states[0] == states[1]);
        assert(tail_states[tail_states.len() - 1] == states[states.len() - 1]);
        assert(MachineState::step(states[0], states[1], ops[0]));
        assert(exists|next: MachineState|
            MachineState::step(states[0], next, ops[0]) && run_op_sequence(
                next,
                states[states.len() - 1],
                ops.skip(1),
            )) by {
            let next = states[1];
            assert(run_op_sequence(next, states[states.len() - 1], tail_ops));
        }
    }
}

/// Lift one machine edge to a singleton execution.
pub proof fn lemma_run_op_sequence_single(
    start: MachineState,
    end: MachineState,
    action: MachineAction,
)
    requires
        MachineState::step(start, end, action),
    ensures
        run_op_sequence(start, end, seq![action]),
{
    assert(exists|next: MachineState|
        MachineState::step(start, next, seq![action][0]) && run_op_sequence(
            next,
            end,
            seq![action].skip(1),
        )) by {
        let next = end;
    }
}

/// Concatenate two adjacent machine executions.
pub proof fn lemma_run_op_sequence_concat(
    start: MachineState,
    middle: MachineState,
    end: MachineState,
    first: Seq<MachineAction>,
    second: Seq<MachineAction>,
)
    requires
        run_op_sequence(start, middle, first),
        run_op_sequence(middle, end, second),
    ensures
        run_op_sequence(start, end, first + second),
    decreases first.len(),
{
    if first.len() != 0 {
        let next = choose|next: MachineState|
            MachineState::step(start, next, first[0]) && run_op_sequence(
                next,
                middle,
                first.skip(1),
            );
        lemma_run_op_sequence_concat(next, middle, end, first.skip(1), second);
        assert((first + second)[0] == first[0]);
        assert((first + second).skip(1) == first.skip(1) + second);
        assert(exists|next: MachineState|
            MachineState::step(start, next, (first + second)[0]) && run_op_sequence(
                next,
                end,
                (first + second).skip(1),
            ));
    }
}

/// A finite machine execution from a well-formed state ends well-formed.
proof fn lemma_run_op_sequence_end_wf(
    start: MachineState,
    end: MachineState,
    ops: Seq<MachineAction>,
)
    requires
        start.wf(),
        run_op_sequence(start, end, ops),
    ensures
        end.wf(),
    decreases ops.len(),
{
    if ops.len() != 0 {
        let next = choose|next: MachineState|
            MachineState::step(start, next, ops[0]) && run_op_sequence(next, end, ops.skip(1));
        lemma_run_op_sequence_end_wf(next, end, ops.skip(1));
    }
}

/// First `k` physical pages of `region`.
pub open spec fn phys_prefix(region: Region, k: nat) -> Set<PhysPage> {
    Set::new(|p: PhysPage| region.phys_base <= p.0 < region.phys_base + k)
}

/// First `k` stage-2 entries of `region`.
pub open spec fn entry_prefix(region: Region, k: nat) -> Map<VmPageKey, S2Entry> {
    Map::new(
        |key: VmPageKey| key.vm == region.vm && region.gpa_base <= key.gpa.0 < region.gpa_base + k,
        |key: VmPageKey|
            S2Entry {
                page: PhysPage((region.phys_base + key.gpa.0 - region.gpa_base) as nat),
                access: region.access,
                generation: 0,
            },
    )
}

/// Extending a physical prefix by one adds exactly page `k`.
pub proof fn lemma_phys_prefix_succ(region: Region, k: nat)
    ensures
        !phys_prefix(region, k).contains(region.phys_page(k)),
        phys_prefix(region, (k + 1) as nat) == phys_prefix(region, k).insert(region.phys_page(k)),
{
}

/// Extending an entry prefix by one adds exactly entry `k`.
pub proof fn lemma_entry_prefix_succ(region: Region, k: nat)
    ensures
        !entry_prefix(region, k).dom().contains(VmPageKey::new(region.vm, region.guest_page(k))),
        entry_prefix(region, (k + 1) as nat) == entry_prefix(region, k).insert(
            VmPageKey::new(region.vm, region.guest_page(k)),
            S2Entry { page: region.phys_page(k), access: region.access, generation: 0 },
        ),
{
}

/// Force both hardware-reachable maps to agree with a software prefix.
pub open spec fn synced_hw(sw: SoftwareView, hw: HardwareView) -> HardwareView {
    HardwareView { s2map: sw.s2_map, iommu_s2map: sw.iommu_s2_map, ..hw }
}

/// TLB keys belonging to the first `k` guest pages of a region.
pub open spec fn tlb_prefix_keys(region: Region, k: nat) -> Set<TlbKey> {
    Set::new(
        |key: TlbKey| key.vm == region.vm && region.gpa_base <= key.gpa.0 < region.gpa_base + k,
    )
}

/// CPU hardware state after invalidating the first `k` region guest pages.
pub open spec fn hw_unmapped(hw: HardwareView, region: Region, k: nat) -> HardwareView {
    HardwareView { tlb: hw.tlb.remove_keys(tlb_prefix_keys(region, k)), ..hw }
}

/// IOMMU hardware state after invalidating the first `k` region guest pages.
pub open spec fn iommu_hw_unmapped(hw: HardwareView, region: Region, k: nat) -> HardwareView {
    HardwareView { iommu_tlb: hw.iommu_tlb.remove_keys(tlb_prefix_keys(region, k)), ..hw }
}

pub open spec fn hw_after_unmap_region(hw: HardwareView, region: Region) -> HardwareView {
    hw_unmapped(hw, region, region.count)
}

pub open spec fn iommu_hw_after_unmap_region(hw: HardwareView, region: Region) -> HardwareView {
    iommu_hw_unmapped(hw, region, region.count)
}

/// CPU S2-Private map actions for `region`, in increasing page-index order.
pub open spec fn cpu_private_insert_ops(region: Region) -> Seq<MachineAction> {
    Seq::new(
        region.count,
        |i: int|
            MachineAction::Hypervisor(
                HypervisorOp::MapS2Private(
                    region.vm,
                    region.guest_page(i as nat),
                    S2Entry {
                        page: region.phys_page(i as nat),
                        access: region.access,
                        generation: 0,
                    },
                ),
            ),
    )
}

/// CPU S2-Private unmap/release actions for `region`.
pub open spec fn cpu_private_remove_ops(region: Region) -> Seq<MachineAction> {
    Seq::new(
        region.count,
        |i: int|
            MachineAction::Hypervisor(
                HypervisorOp::UnmapS2Private(
                    region.vm,
                    region.guest_page(i as nat),
                    region.phys_page(i as nat),
                ),
            ),
    )
}

/// CPU shared map actions for `region`.
pub open spec fn cpu_shared_insert_ops(region: Region) -> Seq<MachineAction> {
    Seq::new(
        region.count,
        |i: int|
            MachineAction::Hypervisor(
                HypervisorOp::MapS2Shared(
                    region.vm,
                    region.guest_page(i as nat),
                    S2Entry {
                        page: region.phys_page(i as nat),
                        access: region.access,
                        generation: 0,
                    },
                ),
            ),
    )
}

/// CPU shared unmap actions for `region`.
pub open spec fn cpu_shared_remove_ops(region: Region) -> Seq<MachineAction> {
    Seq::new(
        region.count,
        |i: int|
            MachineAction::Hypervisor(
                HypervisorOp::UnmapS2Shared(region.vm, region.guest_page(i as nat)),
            ),
    )
}

/// IOMMU-Private map actions for `region`.
pub open spec fn iommu_private_insert_ops(region: Region) -> Seq<MachineAction> {
    Seq::new(
        region.count,
        |i: int|
            MachineAction::Hypervisor(
                HypervisorOp::MapIommuPrivate(
                    region.vm,
                    region.guest_page(i as nat),
                    S2Entry {
                        page: region.phys_page(i as nat),
                        access: region.access,
                        generation: 0,
                    },
                ),
            ),
    )
}

/// IOMMU-Private unmap/release actions for `region`.
pub open spec fn iommu_private_remove_ops(region: Region) -> Seq<MachineAction> {
    Seq::new(
        region.count,
        |i: int|
            MachineAction::Hypervisor(
                HypervisorOp::UnmapIommuPrivate(
                    region.vm,
                    region.guest_page(i as nat),
                    region.phys_page(i as nat),
                ),
            ),
    )
}

/// IOMMU shared map actions for `region`.
pub open spec fn iommu_shared_insert_ops(region: Region) -> Seq<MachineAction> {
    Seq::new(
        region.count,
        |i: int|
            MachineAction::Hypervisor(
                HypervisorOp::MapIommuShared(
                    region.vm,
                    region.guest_page(i as nat),
                    S2Entry {
                        page: region.phys_page(i as nat),
                        access: region.access,
                        generation: 0,
                    },
                ),
            ),
    )
}

/// IOMMU shared unmap actions for `region`.
pub open spec fn iommu_shared_remove_ops(region: Region) -> Seq<MachineAction> {
    Seq::new(
        region.count,
        |i: int|
            MachineAction::Hypervisor(
                HypervisorOp::UnmapIommuShared(region.vm, region.guest_page(i as nat)),
            ),
    )
}

// ---------------------------------------------------------------------------
// CPU S2-Private insert
// ---------------------------------------------------------------------------
pub open spec fn cpu_private_insert_partial(
    s1: SoftwareView,
    region: Region,
    k: nat,
) -> SoftwareView {
    SoftwareView {
        s2_private_pages: s1.s2_private_pages.insert(
            region.vm,
            s1.s2_private_pages[region.vm].union(phys_prefix(region, k)),
        ),
        s2_map: s1.s2_map.union_prefer_right(entry_prefix(region, k)),
        ..s1
    }
}

pub open spec fn cpu_private_insert_machine_partial(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    k: nat,
) -> MachineState {
    let sw = cpu_private_insert_partial(sw1, region, k);
    MachineState::assemble(sw, synced_hw(sw, hw))
}

/// Refine one page of a CPU S2-Private insertion to the combined machine map
/// action, including both S2-Private classification and the hardware mapping.
proof fn lemma_cpu_private_insert_edge(sw1: SoftwareView, hw: HardwareView, region: Region, k: nat)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::cpu_insert_private_region_enabled(sw1, region),
        k < region.count,
        cpu_private_insert_machine_partial(sw1, hw, region, k).wf(),
    ensures
        MachineState::step(
            cpu_private_insert_machine_partial(sw1, hw, region, k),
            cpu_private_insert_machine_partial(sw1, hw, region, (k + 1) as nat),
            cpu_private_insert_ops(region)[k as int],
        ),
{
    let from_sw = cpu_private_insert_partial(sw1, region, k);
    let to_sw = cpu_private_insert_partial(sw1, region, (k + 1) as nat);
    let from_hw = synced_hw(from_sw, hw);
    let to_hw = synced_hw(to_sw, hw);
    let vm = region.vm;
    let gpa = region.guest_page(k);
    let page = region.phys_page(k);
    let key = VmPageKey::new(vm, gpa);
    let entry = S2Entry { page, access: region.access, generation: 0 };

    lemma_phys_prefix_succ(region, k);
    lemma_entry_prefix_succ(region, k);
    assert(region.pages().contains(page));
    assert(!phys_prefix(region, k).contains(page));
    assert forall|v: VmId| #[trigger]
        from_sw.all_vms.contains(v) && v != vm
            implies !from_sw.s2_private_pages[v].contains(page) by {
        assert(!sw1.s2_private_pages[v].contains(page));
    }
    assert(!from_sw.s2_shared_pages.contains(page));
    assert(forall|v: VmId| #[trigger]
        from_sw.all_vms.contains(v) && v != vm ==> !from_sw.iommu_private_pages[v].contains(page));
    assert(!from_sw.iommu_shared_pages.contains(page));
    assert(!sw1.s2_map.contains_key(key)) by {
        assert(region.entries().contains_key(key));
    }
    assert(!entry_prefix(region, k).dom().contains(key));
    assert(!from_sw.s2_map.contains_key(key));
    assert(sw1.s2_private_pages[vm].union(phys_prefix(region, k)).insert(page)
        =~= sw1.s2_private_pages[vm].union(phys_prefix(region, (k + 1) as nat)));
    assert(from_sw.s2_private_pages.insert(vm, from_sw.s2_private_pages[vm].insert(page))
        =~= to_sw.s2_private_pages);
    assert(from_sw.s2_map.insert(key, entry) =~= to_sw.s2_map);
    assert(SoftwareView::map_s2_private_step(from_sw, to_sw, vm, gpa, entry));

    assert(HardwareView::map_step(from_hw, to_hw, vm, gpa, entry));
    refine_hv_map_s2_private(from_sw, to_sw, from_hw, to_hw, vm, gpa, entry);
}

/// Every prefix of a CPU S2-Private insertion is a well-formed machine state.
/// The induction advances through the verified single-page edge.
proof fn lemma_cpu_private_insert_partial_wf(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    k: nat,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::cpu_insert_private_region_enabled(sw1, region),
        k <= region.count,
    ensures
        cpu_private_insert_machine_partial(sw1, hw, region, k).wf(),
    decreases k,
{
    lemma_sw_machine_wf_equiv(sw1, hw);
    if k == 0 {
        assert(phys_prefix(region, 0) =~= Set::<PhysPage>::empty());
        assert(entry_prefix(region, 0) =~= Map::<VmPageKey, S2Entry>::empty());
        assert(cpu_private_insert_partial(sw1, region, 0) == sw1) by {
            assert(sw1.s2_private_pages[region.vm].union(phys_prefix(region, 0))
                =~= sw1.s2_private_pages[region.vm]);
            assert(sw1.s2_private_pages.insert(
                region.vm,
                sw1.s2_private_pages[region.vm].union(phys_prefix(region, 0)),
            ) =~= sw1.s2_private_pages);
            assert(sw1.s2_map.union_prefer_right(entry_prefix(region, 0)) =~= sw1.s2_map);
        }
        assert(MachineState::assemble(sw1, hw).sync());
        assert(MachineState::assemble(sw1, hw).iommu_sync());
    } else {
        lemma_cpu_private_insert_partial_wf(sw1, hw, region, (k - 1) as nat);
        lemma_cpu_private_insert_edge(sw1, hw, region, (k - 1) as nat);
    }
}

/// A bulk CPU Private insertion runs one combined S2-Private map per page.
pub proof fn lemma_cpu_insert_private_region_machine_trace(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw: HardwareView,
    region: Region,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::cpu_insert_private_region_enabled(sw1, region),
        SoftwareView::cpu_insert_private_region_step(sw1, sw2, region),
    ensures
        run_op_sequence(
            MachineState::assemble(sw1, hw),
            MachineState::assemble(sw2, synced_hw(sw2, hw)),
            cpu_private_insert_ops(region),
        ),
{
    let n = region.count;
    let ops = cpu_private_insert_ops(region);
    let states = Seq::new(
        (n + 1) as nat,
        |i: int| cpu_private_insert_machine_partial(sw1, hw, region, i as nat),
    );
    assert(ops.len() == n);
    assert(states.len() == n + 1);
    assert(phys_prefix(region, 0) =~= Set::<PhysPage>::empty());
    assert(entry_prefix(region, 0) =~= Map::<VmPageKey, S2Entry>::empty());
    assert(phys_prefix(region, n) =~= region.pages());
    assert(entry_prefix(region, n) =~= region.entries());
    lemma_sw_machine_wf_equiv(sw1, hw);
    assert(cpu_private_insert_partial(sw1, region, 0) == sw1) by {
        assert(sw1.s2_private_pages[region.vm].union(phys_prefix(region, 0))
            =~= sw1.s2_private_pages[region.vm]);
        assert(sw1.s2_private_pages.insert(
            region.vm,
            sw1.s2_private_pages[region.vm].union(phys_prefix(region, 0)),
        ) =~= sw1.s2_private_pages);
        assert(sw1.s2_map.union_prefer_right(entry_prefix(region, 0)) =~= sw1.s2_map);
    }
    assert(states[0] == MachineState::assemble(sw1, hw)) by {
        assert(MachineState::assemble(sw1, hw).sync());
        assert(MachineState::assemble(sw1, hw).iommu_sync());
    }
    assert(cpu_private_insert_partial(sw1, region, n) == sw2);
    assert(states[states.len() - 1] == MachineState::assemble(sw2, synced_hw(sw2, hw)));
    assert forall|i: int| 0 <= i < ops.len() implies #[trigger] MachineState::step(
        states[i],
        states[i + 1],
        ops[i],
    ) by {
        lemma_cpu_private_insert_partial_wf(sw1, hw, region, i as nat);
        lemma_cpu_private_insert_edge(sw1, hw, region, i as nat);
    }
    lemma_run_op_sequence_from_states(states, ops);
}

// ---------------------------------------------------------------------------
// CPU S2-Private remove
// ---------------------------------------------------------------------------
pub open spec fn cpu_private_remove_partial(
    s1: SoftwareView,
    region: Region,
    k: nat,
) -> SoftwareView {
    let post_map = s1.s2_map.remove_keys(entry_prefix(region, k).dom());
    SoftwareView {
        s2_private_pages: private_pages_after_unmap(
            s1.s2_private_pages,
            post_map,
            region.vm,
            phys_prefix(region, k),
        ),
        s2_map: post_map,
        ..s1
    }
}

pub open spec fn cpu_private_remove_machine_partial(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    k: nat,
) -> MachineState {
    let sw = cpu_private_remove_partial(sw1, region, k);
    MachineState::assemble(sw, synced_hw(sw, hw_unmapped(hw, region, k)))
}

/// Refine one page of a CPU S2-Private removal to the combined machine unmap
/// action, including S2-Private removal and matching TLB invalidation.
proof fn lemma_cpu_private_remove_edge(sw1: SoftwareView, hw: HardwareView, region: Region, k: nat)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::cpu_remove_private_region_enabled(sw1, region),
        k < region.count,
        cpu_private_remove_machine_partial(sw1, hw, region, k).wf(),
    ensures
        MachineState::step(
            cpu_private_remove_machine_partial(sw1, hw, region, k),
            cpu_private_remove_machine_partial(sw1, hw, region, (k + 1) as nat),
            cpu_private_remove_ops(region)[k as int],
        ),
{
    let from_sw = cpu_private_remove_partial(sw1, region, k);
    let to_sw = cpu_private_remove_partial(sw1, region, (k + 1) as nat);
    let from_hw = synced_hw(from_sw, hw_unmapped(hw, region, k));
    let to_hw = synced_hw(to_sw, hw_unmapped(hw, region, (k + 1) as nat));
    let vm = region.vm;
    let gpa = region.guest_page(k);
    let page = region.phys_page(k);
    let key = VmPageKey::new(vm, gpa);
    let d = entry_prefix(region, k).dom();
    let d_next = entry_prefix(region, (k + 1) as nat).dom();

    lemma_phys_prefix_succ(region, k);
    lemma_entry_prefix_succ(region, k);
    assert(region.pages().contains(page));
    assert(region.entries().contains_key(key));
    assert(sw1.s2_map.contains_key(key) && sw1.s2_map[key] == region.entries()[key]);
    assert(!d.contains(key));
    assert(from_sw.s2_map.contains_key(key));
    assert(from_sw.s2_map[key].page == page);
    assert(sw1.s2_private_pages[vm].contains(page));
    assert(!phys_prefix(region, k).contains(page));
    assert(from_sw.s2_private_pages[vm].contains(page));
    assert(!from_sw.s2_shared_pages.contains(page));
    assert(d_next =~= d.insert(key));
    assert(to_sw.s2_map =~= from_sw.s2_map.remove(key));
    lemma_private_pages_after_unmap_step(
        sw1.s2_private_pages,
        from_sw.s2_map,
        to_sw.s2_map,
        vm,
        phys_prefix(region, k),
        key,
        page,
    );
    assert(SoftwareView::unmap_s2_private_step(from_sw, to_sw, vm, gpa, page));

    assert(to_hw.s2map =~= from_hw.s2map.remove(key));
    assert(forall|tk: TlbKey|
        #![auto]
        tlb_prefix_keys(region, (k + 1) as nat).contains(tk) <==> (tlb_prefix_keys(
            region,
            k,
        ).contains(tk) || (tk.vm == vm && tk.gpa == gpa)));
    assert(to_hw.tlb =~= from_hw.tlb.remove_keys(
        Set::new(|tk: TlbKey| tk.vm == vm && tk.gpa == gpa),
    ));
    assert(HardwareView::unmap_invalidate_step(from_hw, to_hw, vm, gpa));
    refine_hv_unmap_s2_private(from_sw, to_sw, from_hw, to_hw, vm, gpa, page);
}

/// Every prefix of a CPU S2-Private removal is a well-formed machine state.
/// The induction advances through the verified single-page edge.
proof fn lemma_cpu_private_remove_partial_wf(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    k: nat,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::cpu_remove_private_region_enabled(sw1, region),
        k <= region.count,
    ensures
        cpu_private_remove_machine_partial(sw1, hw, region, k).wf(),
    decreases k,
{
    lemma_sw_machine_wf_equiv(sw1, hw);
    if k == 0 {
        assert(phys_prefix(region, 0) =~= Set::<PhysPage>::empty());
        assert(entry_prefix(region, 0).dom() =~= Set::<VmPageKey>::empty());
        assert(tlb_prefix_keys(region, 0) =~= Set::<TlbKey>::empty());
        assert(cpu_private_remove_partial(sw1, region, 0) == sw1) by {
            let post_map = sw1.s2_map.remove_keys(entry_prefix(region, 0).dom());
            assert(post_map =~= sw1.s2_map);
            lemma_private_pages_after_unmap_empty(sw1.s2_private_pages, post_map, region.vm);
        }
        assert(hw_unmapped(hw, region, 0) == hw) by {
            assert(hw.tlb.remove_keys(tlb_prefix_keys(region, 0)) =~= hw.tlb);
        }
        assert(MachineState::assemble(sw1, hw).sync());
        assert(MachineState::assemble(sw1, hw).iommu_sync());
    } else {
        lemma_cpu_private_remove_partial_wf(sw1, hw, region, (k - 1) as nat);
        lemma_cpu_private_remove_edge(sw1, hw, region, (k - 1) as nat);
    }
}

/// A bulk CPU private removal runs one combined unmap/release per page.
pub proof fn lemma_cpu_remove_private_region_machine_trace(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw: HardwareView,
    region: Region,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::cpu_remove_private_region_enabled(sw1, region),
        SoftwareView::cpu_remove_private_region_step(sw1, sw2, region),
    ensures
        run_op_sequence(
            MachineState::assemble(sw1, hw),
            MachineState::assemble(sw2, synced_hw(sw2, hw_after_unmap_region(hw, region))),
            cpu_private_remove_ops(region),
        ),
{
    let n = region.count;
    let ops = cpu_private_remove_ops(region);
    let states = Seq::new(
        (n + 1) as nat,
        |i: int| cpu_private_remove_machine_partial(sw1, hw, region, i as nat),
    );
    assert(ops.len() == n && states.len() == n + 1);
    assert(phys_prefix(region, 0) =~= Set::<PhysPage>::empty());
    assert(entry_prefix(region, 0).dom() =~= Set::<VmPageKey>::empty());
    assert(tlb_prefix_keys(region, 0) =~= Set::<TlbKey>::empty());
    assert(phys_prefix(region, n) =~= region.pages());
    assert(entry_prefix(region, n).dom() =~= region.entries().dom());
    lemma_cpu_private_remove_partial_wf(sw1, hw, region, 0);
    lemma_sw_machine_wf_equiv(sw1, hw);
    assert(cpu_private_remove_partial(sw1, region, 0) == sw1) by {
        let post_map = sw1.s2_map.remove_keys(entry_prefix(region, 0).dom());
        assert(post_map =~= sw1.s2_map);
        lemma_private_pages_after_unmap_empty(sw1.s2_private_pages, post_map, region.vm);
    }
    assert(hw_unmapped(hw, region, 0) == hw) by {
        assert(hw.tlb.remove_keys(tlb_prefix_keys(region, 0)) =~= hw.tlb);
    }
    assert(states[0] == MachineState::assemble(sw1, hw)) by {
        assert(MachineState::assemble(sw1, hw).sync());
        assert(MachineState::assemble(sw1, hw).iommu_sync());
    }
    assert(cpu_private_remove_partial(sw1, region, n) == sw2);
    assert(states[states.len() - 1] == MachineState::assemble(
        sw2,
        synced_hw(sw2, hw_after_unmap_region(hw, region)),
    ));
    assert forall|i: int| 0 <= i < ops.len() implies #[trigger] MachineState::step(
        states[i],
        states[i + 1],
        ops[i],
    ) by {
        lemma_cpu_private_remove_partial_wf(sw1, hw, region, i as nat);
        lemma_cpu_private_remove_edge(sw1, hw, region, i as nat);
    }
    lemma_run_op_sequence_from_states(states, ops);
}

// ---------------------------------------------------------------------------
// CPU shared insert
// ---------------------------------------------------------------------------
pub open spec fn cpu_shared_insert_partial(
    s1: SoftwareView,
    region: Region,
    k: nat,
) -> SoftwareView {
    SoftwareView {
        s2_shared_pages: s1.s2_shared_pages.union(phys_prefix(region, k)),
        s2_map: s1.s2_map.union_prefer_right(entry_prefix(region, k)),
        ..s1
    }
}

pub open spec fn cpu_shared_insert_machine_partial(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    k: nat,
) -> MachineState {
    let sw = cpu_shared_insert_partial(sw1, region, k);
    MachineState::assemble(sw, synced_hw(sw, hw))
}

/// Refine one page of a CPU shared insertion to the machine shared-map
/// action while preserving any existing physical aliases.
proof fn lemma_cpu_shared_insert_edge(sw1: SoftwareView, hw: HardwareView, region: Region, k: nat)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::cpu_insert_shared_region_enabled(sw1, region),
        k < region.count,
        cpu_shared_insert_machine_partial(sw1, hw, region, k).wf(),
    ensures
        MachineState::step(
            cpu_shared_insert_machine_partial(sw1, hw, region, k),
            cpu_shared_insert_machine_partial(sw1, hw, region, (k + 1) as nat),
            cpu_shared_insert_ops(region)[k as int],
        ),
{
    let from_sw = cpu_shared_insert_partial(sw1, region, k);
    let to_sw = cpu_shared_insert_partial(sw1, region, (k + 1) as nat);
    let from_hw = synced_hw(from_sw, hw);
    let to_hw = synced_hw(to_sw, hw);
    let vm = region.vm;
    let gpa = region.guest_page(k);
    let page = region.phys_page(k);
    let key = VmPageKey::new(vm, gpa);
    let entry = S2Entry { page, access: region.access, generation: 0 };

    lemma_phys_prefix_succ(region, k);
    lemma_entry_prefix_succ(region, k);
    assert(region.pages().contains(page));
    assert(forall|v: VmId| #[trigger]
        from_sw.all_vms.contains(v) ==> !from_sw.s2_private_pages[v].contains(page));
    assert(!sw1.s2_map.contains_key(key)) by {
        assert(region.entries().contains_key(key));
    }
    assert(!entry_prefix(region, k).dom().contains(key));
    assert(!from_sw.s2_map.contains_key(key));
    assert(sw1.s2_shared_pages.union(phys_prefix(region, k)).insert(page)
        =~= sw1.s2_shared_pages.union(phys_prefix(region, (k + 1) as nat)));
    assert(from_sw.s2_map.insert(key, entry) =~= to_sw.s2_map);
    assert(SoftwareView::map_s2_shared_step(from_sw, to_sw, vm, gpa, entry));
    assert(HardwareView::map_step(from_hw, to_hw, vm, gpa, entry));
    refine_hv_map_s2_shared(from_sw, to_sw, from_hw, to_hw, vm, gpa, entry);
}

/// Every prefix of a CPU shared insertion is a well-formed machine state.
/// The induction advances through the verified single-page edge.
proof fn lemma_cpu_shared_insert_partial_wf(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    k: nat,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::cpu_insert_shared_region_enabled(sw1, region),
        k <= region.count,
    ensures
        cpu_shared_insert_machine_partial(sw1, hw, region, k).wf(),
    decreases k,
{
    if k == 0 {
        assert(phys_prefix(region, 0) =~= Set::<PhysPage>::empty());
        assert(entry_prefix(region, 0) =~= Map::<VmPageKey, S2Entry>::empty());
        assert(cpu_shared_insert_partial(sw1, region, 0) == sw1) by {
            assert(sw1.s2_shared_pages.union(phys_prefix(region, 0)) =~= sw1.s2_shared_pages);
            assert(sw1.s2_map.union_prefer_right(entry_prefix(region, 0)) =~= sw1.s2_map);
        }
        assert(MachineState::assemble(sw1, hw).sync());
        assert(MachineState::assemble(sw1, hw).iommu_sync());
    } else {
        lemma_cpu_shared_insert_partial_wf(sw1, hw, region, (k - 1) as nat);
        lemma_cpu_shared_insert_edge(sw1, hw, region, (k - 1) as nat);
    }
}

/// A bulk CPU shared insertion runs one shared map per page.
pub proof fn lemma_cpu_insert_shared_region_machine_trace(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw: HardwareView,
    region: Region,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::cpu_insert_shared_region_enabled(sw1, region),
        SoftwareView::cpu_insert_shared_region_step(sw1, sw2, region),
    ensures
        run_op_sequence(
            MachineState::assemble(sw1, hw),
            MachineState::assemble(sw2, synced_hw(sw2, hw)),
            cpu_shared_insert_ops(region),
        ),
{
    let n = region.count;
    let ops = cpu_shared_insert_ops(region);
    let states = Seq::new(
        (n + 1) as nat,
        |i: int| cpu_shared_insert_machine_partial(sw1, hw, region, i as nat),
    );
    assert(ops.len() == n && states.len() == n + 1);
    assert(phys_prefix(region, 0) =~= Set::<PhysPage>::empty());
    assert(entry_prefix(region, 0) =~= Map::<VmPageKey, S2Entry>::empty());
    assert(phys_prefix(region, n) =~= region.pages());
    assert(entry_prefix(region, n) =~= region.entries());
    assert(cpu_shared_insert_partial(sw1, region, 0) == sw1) by {
        assert(sw1.s2_shared_pages.union(phys_prefix(region, 0)) =~= sw1.s2_shared_pages);
        assert(sw1.s2_map.union_prefer_right(entry_prefix(region, 0)) =~= sw1.s2_map);
    }
    assert(states[0] == MachineState::assemble(sw1, hw)) by {
        assert(MachineState::assemble(sw1, hw).sync());
        assert(MachineState::assemble(sw1, hw).iommu_sync());
    }
    assert(cpu_shared_insert_partial(sw1, region, n) == sw2);
    assert(states[states.len() - 1] == MachineState::assemble(sw2, synced_hw(sw2, hw)));
    assert forall|i: int| 0 <= i < ops.len() implies #[trigger] MachineState::step(
        states[i],
        states[i + 1],
        ops[i],
    ) by {
        lemma_cpu_shared_insert_partial_wf(sw1, hw, region, i as nat);
        lemma_cpu_shared_insert_edge(sw1, hw, region, i as nat);
    }
    lemma_run_op_sequence_from_states(states, ops);
}

// ---------------------------------------------------------------------------
// CPU shared remove
// ---------------------------------------------------------------------------
pub open spec fn cpu_shared_remove_prefix_map(s1: SoftwareView, region: Region, k: nat) -> Map<
    VmPageKey,
    S2Entry,
> {
    s1.s2_map.remove_keys(entry_prefix(region, k).dom())
}

pub open spec fn s2_shared_pages_after_remove_prefix(
    s1: SoftwareView,
    region: Region,
    k: nat,
) -> Set<PhysPage> {
    let post_map = cpu_shared_remove_prefix_map(s1, region, k);
    Set::new(
        |p: PhysPage|
            {
                &&& s1.s2_shared_pages.contains(p)
                &&& (!phys_prefix(region, k).contains(p) || exists|q: VmPageKey| #[trigger]
                    post_map.contains_key(q) && post_map[q].page == p)
            },
    )
}

pub open spec fn cpu_shared_remove_partial(
    s1: SoftwareView,
    region: Region,
    k: nat,
) -> SoftwareView {
    SoftwareView {
        s2_shared_pages: s2_shared_pages_after_remove_prefix(s1, region, k),
        s2_map: cpu_shared_remove_prefix_map(s1, region, k),
        ..s1
    }
}

/// Characterize the dynamic `s2_shared_pages` projection after one more shared
/// mapping is removed: the page remains exactly when another CPU alias exists.
proof fn lemma_cpu_shared_remove_projection_succ(s1: SoftwareView, region: Region, k: nat)
    requires
        s1.wf(),
        SoftwareView::cpu_remove_shared_region_enabled(s1, region),
        k < region.count,
    ensures
        ({
            let from = cpu_shared_remove_partial(s1, region, k);
            let to = cpu_shared_remove_partial(s1, region, (k + 1) as nat);
            let page = region.phys_page(k);
            let aliased = exists|q: VmPageKey| #[trigger]
                to.s2_map.contains_key(q) && to.s2_map[q].page == page;
            to.s2_shared_pages == if aliased {
                from.s2_shared_pages
            } else {
                from.s2_shared_pages.remove(page)
            }
        }),
{
    let from = cpu_shared_remove_partial(s1, region, k);
    let to = cpu_shared_remove_partial(s1, region, (k + 1) as nat);
    let key = VmPageKey::new(region.vm, region.guest_page(k));
    let page = region.phys_page(k);
    let pp = phys_prefix(region, k);
    let aliased = exists|q: VmPageKey| #[trigger]
        to.s2_map.contains_key(q) && to.s2_map[q].page == page;
    lemma_phys_prefix_succ(region, k);
    lemma_entry_prefix_succ(region, k);
    assert(region.entries().contains_key(key));
    assert(s1.s2_map.contains_key(key) && s1.s2_map[key] == region.entries()[key]);
    assert(!entry_prefix(region, k).dom().contains(key));
    assert(from.s2_map.contains_key(key));
    assert(from.s2_map[key].page == page);
    assert(to.s2_map =~= from.s2_map.remove(key));
    assert forall|p: PhysPage| #[trigger] pp.contains(p) && p != page implies ((exists|q: VmPageKey|
     #[trigger]
        from.s2_map.contains_key(q) && from.s2_map[q].page == p) <==> (exists|q: VmPageKey|
     #[trigger]
        to.s2_map.contains_key(q) && to.s2_map[q].page == p)) by {
        if exists|q: VmPageKey| #[trigger] from.s2_map.contains_key(q) && from.s2_map[q].page == p {
            let q = choose|q: VmPageKey| #[trigger]
                from.s2_map.contains_key(q) && from.s2_map[q].page == p;
            assert(q != key);
            assert(to.s2_map.contains_key(q));
        } else if exists|q: VmPageKey| #[trigger]
            to.s2_map.contains_key(q) && to.s2_map[q].page == p {
            let q = choose|q: VmPageKey| #[trigger]
                to.s2_map.contains_key(q) && to.s2_map[q].page == p;
            assert(from.s2_map.contains_key(q));
        }
    }
    if aliased {
        assert(to.s2_shared_pages =~= from.s2_shared_pages) by {
            assert forall|p: PhysPage| #[trigger]
                to.s2_shared_pages.contains(p) <==> from.s2_shared_pages.contains(p) by {
                if p == page {
                    assert(region.pages().contains(page));
                    assert(s1.s2_shared_pages.contains(page));
                } else if pp.contains(p) {
                    assert((exists|q: VmPageKey| #[trigger]
                        from.s2_map.contains_key(q) && from.s2_map[q].page == p) <==> (exists|
                        q: VmPageKey,
                    | #[trigger]
                        to.s2_map.contains_key(q) && to.s2_map[q].page == p));
                }
            }
        }
    } else {
        assert(to.s2_shared_pages =~= from.s2_shared_pages.remove(page)) by {
            assert forall|p: PhysPage| #[trigger]
                to.s2_shared_pages.contains(p) <==> from.s2_shared_pages.remove(page).contains(
                    p,
                ) by {
                if p != page && pp.contains(p) {
                    assert((exists|q: VmPageKey| #[trigger]
                        from.s2_map.contains_key(q) && from.s2_map[q].page == p) <==> (exists|
                        q: VmPageKey,
                    | #[trigger]
                        to.s2_map.contains_key(q) && to.s2_map[q].page == p));
                }
            }
        }
    }
}

pub open spec fn cpu_shared_remove_machine_partial(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    k: nat,
) -> MachineState {
    let sw = cpu_shared_remove_partial(sw1, region, k);
    MachineState::assemble(sw, synced_hw(sw, hw_unmapped(hw, region, k)))
}

/// Refine one page of a CPU shared removal to the alias-aware machine
/// unmap action and invalidate matching TLB entries.
proof fn lemma_cpu_shared_remove_edge(sw1: SoftwareView, hw: HardwareView, region: Region, k: nat)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::cpu_remove_shared_region_enabled(sw1, region),
        k < region.count,
        cpu_shared_remove_machine_partial(sw1, hw, region, k).wf(),
    ensures
        MachineState::step(
            cpu_shared_remove_machine_partial(sw1, hw, region, k),
            cpu_shared_remove_machine_partial(sw1, hw, region, (k + 1) as nat),
            cpu_shared_remove_ops(region)[k as int],
        ),
{
    let from_sw = cpu_shared_remove_partial(sw1, region, k);
    let to_sw = cpu_shared_remove_partial(sw1, region, (k + 1) as nat);
    let from_hw = synced_hw(from_sw, hw_unmapped(hw, region, k));
    let to_hw = synced_hw(to_sw, hw_unmapped(hw, region, (k + 1) as nat));
    let vm = region.vm;
    let gpa = region.guest_page(k);
    let page = region.phys_page(k);
    let key = VmPageKey::new(vm, gpa);

    lemma_sw_machine_wf_equiv(sw1, hw);
    lemma_cpu_shared_remove_projection_succ(sw1, region, k);
    lemma_phys_prefix_succ(region, k);
    lemma_entry_prefix_succ(region, k);
    assert(region.entries().contains_key(key));
    assert(sw1.s2_map.contains_key(key) && sw1.s2_map[key] == region.entries()[key]);
    assert(!entry_prefix(region, k).dom().contains(key));
    assert(from_sw.s2_map.contains_key(key));
    assert(from_sw.s2_map[key].page == page);
    assert(region.pages().contains(page));
    assert(sw1.s2_shared_pages.contains(page));
    assert(!phys_prefix(region, k).contains(page));
    assert(from_sw.s2_shared_pages.contains(page));
    assert(to_sw.s2_map =~= from_sw.s2_map.remove(key));
    assert(SoftwareView::unmap_s2_shared_step(from_sw, to_sw, vm, gpa));

    assert(to_hw.s2map =~= from_hw.s2map.remove(key));
    assert(forall|tk: TlbKey|
        #![auto]
        tlb_prefix_keys(region, (k + 1) as nat).contains(tk) <==> (tlb_prefix_keys(
            region,
            k,
        ).contains(tk) || (tk.vm == vm && tk.gpa == gpa)));
    assert(to_hw.tlb =~= from_hw.tlb.remove_keys(
        Set::new(|tk: TlbKey| tk.vm == vm && tk.gpa == gpa),
    ));
    assert(HardwareView::unmap_invalidate_step(from_hw, to_hw, vm, gpa));
    refine_hv_unmap_s2_shared(from_sw, to_sw, from_hw, to_hw, vm, gpa);
}

/// Every prefix of a CPU shared removal is a well-formed machine state.
/// The induction uses the alias-sensitive shared projection at each edge.
proof fn lemma_cpu_shared_remove_partial_wf(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    k: nat,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::cpu_remove_shared_region_enabled(sw1, region),
        k <= region.count,
    ensures
        cpu_shared_remove_machine_partial(sw1, hw, region, k).wf(),
    decreases k,
{
    lemma_sw_machine_wf_equiv(sw1, hw);
    if k == 0 {
        assert(phys_prefix(region, 0) =~= Set::<PhysPage>::empty());
        assert(entry_prefix(region, 0).dom() =~= Set::<VmPageKey>::empty());
        assert(tlb_prefix_keys(region, 0) =~= Set::<TlbKey>::empty());
        assert(s2_shared_pages_after_remove_prefix(sw1, region, 0) =~= sw1.s2_shared_pages);
        assert(cpu_shared_remove_prefix_map(sw1, region, 0) =~= sw1.s2_map);
        assert(cpu_shared_remove_partial(sw1, region, 0) == sw1);
        assert(hw_unmapped(hw, region, 0) == hw) by {
            assert(hw.tlb.remove_keys(tlb_prefix_keys(region, 0)) =~= hw.tlb);
        }
        assert(MachineState::assemble(sw1, hw).sync());
        assert(MachineState::assemble(sw1, hw).iommu_sync());
    } else {
        lemma_cpu_shared_remove_partial_wf(sw1, hw, region, (k - 1) as nat);
        lemma_cpu_shared_remove_edge(sw1, hw, region, (k - 1) as nat);
    }
}

/// A bulk CPU shared removal runs one alias-aware shared unmap per page.
pub proof fn lemma_cpu_remove_shared_region_machine_trace(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw: HardwareView,
    region: Region,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::cpu_remove_shared_region_enabled(sw1, region),
        SoftwareView::cpu_remove_shared_region_step(sw1, sw2, region),
    ensures
        run_op_sequence(
            MachineState::assemble(sw1, hw),
            MachineState::assemble(sw2, synced_hw(sw2, hw_after_unmap_region(hw, region))),
            cpu_shared_remove_ops(region),
        ),
{
    let n = region.count;
    let ops = cpu_shared_remove_ops(region);
    let states = Seq::new(
        (n + 1) as nat,
        |i: int| cpu_shared_remove_machine_partial(sw1, hw, region, i as nat),
    );
    assert(ops.len() == n && states.len() == n + 1);
    assert(phys_prefix(region, 0) =~= Set::<PhysPage>::empty());
    assert(entry_prefix(region, 0).dom() =~= Set::<VmPageKey>::empty());
    assert(tlb_prefix_keys(region, 0) =~= Set::<TlbKey>::empty());
    assert(phys_prefix(region, n) =~= region.pages());
    assert(entry_prefix(region, n).dom() =~= region.entries().dom());
    assert(s2_shared_pages_after_remove_prefix(sw1, region, 0) =~= sw1.s2_shared_pages);
    assert(cpu_shared_remove_prefix_map(sw1, region, 0) =~= sw1.s2_map);
    assert(cpu_shared_remove_partial(sw1, region, 0) == sw1);
    assert(hw_unmapped(hw, region, 0) == hw) by {
        assert(hw.tlb.remove_keys(tlb_prefix_keys(region, 0)) =~= hw.tlb);
    }
    assert(states[0] == MachineState::assemble(sw1, hw)) by {
        assert(MachineState::assemble(sw1, hw).sync());
        assert(MachineState::assemble(sw1, hw).iommu_sync());
    }
    assert(cpu_shared_remove_partial(sw1, region, n) == sw2);
    assert(states[states.len() - 1] == MachineState::assemble(
        sw2,
        synced_hw(sw2, hw_after_unmap_region(hw, region)),
    ));
    assert forall|i: int| 0 <= i < ops.len() implies #[trigger] MachineState::step(
        states[i],
        states[i + 1],
        ops[i],
    ) by {
        lemma_cpu_shared_remove_partial_wf(sw1, hw, region, i as nat);
        lemma_cpu_shared_remove_edge(sw1, hw, region, i as nat);
    }
    lemma_run_op_sequence_from_states(states, ops);
}

// ---------------------------------------------------------------------------
// IOMMU-Private insert
// ---------------------------------------------------------------------------
pub open spec fn iommu_private_insert_partial(
    s1: SoftwareView,
    region: Region,
    k: nat,
) -> SoftwareView {
    SoftwareView {
        iommu_private_pages: s1.iommu_private_pages.insert(
            region.vm,
            s1.iommu_private_pages[region.vm].union(phys_prefix(region, k)),
        ),
        iommu_s2_map: s1.iommu_s2_map.union_prefer_right(entry_prefix(region, k)),
        ..s1
    }
}

pub open spec fn iommu_private_insert_machine_partial(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    k: nat,
) -> MachineState {
    let sw = iommu_private_insert_partial(sw1, region, k);
    MachineState::assemble(sw, synced_hw(sw, hw))
}

/// Refine one page of an IOMMU-Private insertion to the combined machine
/// map action, including IOMMU-Private classification and the hardware mapping.
proof fn lemma_iommu_private_insert_edge(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    k: nat,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::iommu_insert_private_region_enabled(sw1, region),
        k < region.count,
        iommu_private_insert_machine_partial(sw1, hw, region, k).wf(),
    ensures
        MachineState::step(
            iommu_private_insert_machine_partial(sw1, hw, region, k),
            iommu_private_insert_machine_partial(sw1, hw, region, (k + 1) as nat),
            iommu_private_insert_ops(region)[k as int],
        ),
{
    let from_sw = iommu_private_insert_partial(sw1, region, k);
    let to_sw = iommu_private_insert_partial(sw1, region, (k + 1) as nat);
    let from_hw = synced_hw(from_sw, hw);
    let to_hw = synced_hw(to_sw, hw);
    let vm = region.vm;
    let gpa = region.guest_page(k);
    let page = region.phys_page(k);
    let key = VmPageKey::new(vm, gpa);
    let entry = S2Entry { page, access: region.access, generation: 0 };

    lemma_phys_prefix_succ(region, k);
    lemma_entry_prefix_succ(region, k);
    assert(region.pages().contains(page));
    assert(!phys_prefix(region, k).contains(page));
    assert forall|v: VmId| #[trigger]
        from_sw.all_vms.contains(v) && v != vm
            implies !from_sw.iommu_private_pages[v].contains(page) by {
        assert(!sw1.iommu_private_pages[v].contains(page));
    }
    assert(forall|v: VmId| #[trigger]
        from_sw.all_vms.contains(v) && v != vm ==> !from_sw.s2_private_pages[v].contains(page));
    assert(!from_sw.iommu_shared_pages.contains(page));
    assert(!sw1.iommu_s2_map.contains_key(key)) by {
        assert(region.entries().contains_key(key));
    }
    assert(!entry_prefix(region, k).dom().contains(key));
    assert(!from_sw.iommu_s2_map.contains_key(key));
    assert(sw1.iommu_private_pages[vm].union(phys_prefix(region, k)).insert(page)
        =~= sw1.iommu_private_pages[vm].union(phys_prefix(region, (k + 1) as nat)));
    assert(from_sw.iommu_private_pages.insert(vm, from_sw.iommu_private_pages[vm].insert(page))
        =~= to_sw.iommu_private_pages);
    assert(from_sw.iommu_s2_map.insert(key, entry) =~= to_sw.iommu_s2_map);
    assert(SoftwareView::map_iommu_private_step(from_sw, to_sw, vm, gpa, entry));
    assert(HardwareView::iommu_map_step(from_hw, to_hw, vm, gpa, entry));
    refine_hv_map_iommu_private(from_sw, to_sw, from_hw, to_hw, vm, gpa, entry);
}

/// Every prefix of an IOMMU-Private insertion is a well-formed machine state.
/// The induction advances through the verified single-page edge.
proof fn lemma_iommu_private_insert_partial_wf(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    k: nat,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::iommu_insert_private_region_enabled(sw1, region),
        k <= region.count,
    ensures
        iommu_private_insert_machine_partial(sw1, hw, region, k).wf(),
    decreases k,
{
    lemma_sw_machine_wf_equiv(sw1, hw);
    if k == 0 {
        assert(phys_prefix(region, 0) =~= Set::<PhysPage>::empty());
        assert(entry_prefix(region, 0) =~= Map::<VmPageKey, S2Entry>::empty());
        assert(iommu_private_insert_partial(sw1, region, 0) == sw1) by {
            assert(sw1.iommu_private_pages[region.vm].union(phys_prefix(region, 0))
                =~= sw1.iommu_private_pages[region.vm]);
            assert(sw1.iommu_private_pages.insert(
                region.vm,
                sw1.iommu_private_pages[region.vm].union(phys_prefix(region, 0)),
            ) =~= sw1.iommu_private_pages);
            assert(sw1.iommu_s2_map.union_prefer_right(entry_prefix(region, 0))
                =~= sw1.iommu_s2_map);
        }
        assert(MachineState::assemble(sw1, hw).sync());
        assert(MachineState::assemble(sw1, hw).iommu_sync());
    } else {
        lemma_iommu_private_insert_partial_wf(sw1, hw, region, (k - 1) as nat);
        lemma_iommu_private_insert_edge(sw1, hw, region, (k - 1) as nat);
    }
}

/// A bulk IOMMU private insertion runs one combined private map per page.
pub proof fn lemma_iommu_insert_private_region_machine_trace(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw: HardwareView,
    region: Region,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::iommu_insert_private_region_enabled(sw1, region),
        SoftwareView::iommu_insert_private_region_step(sw1, sw2, region),
    ensures
        run_op_sequence(
            MachineState::assemble(sw1, hw),
            MachineState::assemble(sw2, synced_hw(sw2, hw)),
            iommu_private_insert_ops(region),
        ),
{
    let n = region.count;
    let ops = iommu_private_insert_ops(region);
    let states = Seq::new(
        (n + 1) as nat,
        |i: int| iommu_private_insert_machine_partial(sw1, hw, region, i as nat),
    );
    assert(ops.len() == n && states.len() == n + 1);
    assert(phys_prefix(region, 0) =~= Set::<PhysPage>::empty());
    assert(entry_prefix(region, 0) =~= Map::<VmPageKey, S2Entry>::empty());
    assert(phys_prefix(region, n) =~= region.pages());
    assert(entry_prefix(region, n) =~= region.entries());
    lemma_sw_machine_wf_equiv(sw1, hw);
    assert(iommu_private_insert_partial(sw1, region, 0) == sw1) by {
        assert(sw1.iommu_private_pages[region.vm].union(phys_prefix(region, 0))
            =~= sw1.iommu_private_pages[region.vm]);
        assert(sw1.iommu_private_pages.insert(
            region.vm,
            sw1.iommu_private_pages[region.vm].union(phys_prefix(region, 0)),
        ) =~= sw1.iommu_private_pages);
        assert(sw1.iommu_s2_map.union_prefer_right(entry_prefix(region, 0)) =~= sw1.iommu_s2_map);
    }
    assert(states[0] == MachineState::assemble(sw1, hw)) by {
        assert(MachineState::assemble(sw1, hw).sync());
        assert(MachineState::assemble(sw1, hw).iommu_sync());
    }
    assert(iommu_private_insert_partial(sw1, region, n) == sw2);
    assert(states[states.len() - 1] == MachineState::assemble(sw2, synced_hw(sw2, hw)));
    assert forall|i: int| 0 <= i < ops.len() implies #[trigger] MachineState::step(
        states[i],
        states[i + 1],
        ops[i],
    ) by {
        lemma_iommu_private_insert_partial_wf(sw1, hw, region, i as nat);
        lemma_iommu_private_insert_edge(sw1, hw, region, i as nat);
    }
    lemma_run_op_sequence_from_states(states, ops);
}

// ---------------------------------------------------------------------------
// IOMMU-Private remove
// ---------------------------------------------------------------------------
pub open spec fn iommu_private_remove_partial(
    s1: SoftwareView,
    region: Region,
    k: nat,
) -> SoftwareView {
    let post_map = s1.iommu_s2_map.remove_keys(entry_prefix(region, k).dom());
    SoftwareView {
        iommu_private_pages: private_pages_after_unmap(
            s1.iommu_private_pages,
            post_map,
            region.vm,
            phys_prefix(region, k),
        ),
        iommu_s2_map: post_map,
        ..s1
    }
}

pub open spec fn iommu_private_remove_machine_partial(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    k: nat,
) -> MachineState {
    let sw = iommu_private_remove_partial(sw1, region, k);
    MachineState::assemble(sw, synced_hw(sw, iommu_hw_unmapped(hw, region, k)))
}

/// Refine one page of an IOMMU-Private removal to the combined machine
/// unmap action, including IOMMU-Private removal and SMMU-TLB invalidation.
proof fn lemma_iommu_private_remove_edge(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    k: nat,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::iommu_remove_private_region_enabled(sw1, region),
        k < region.count,
        iommu_private_remove_machine_partial(sw1, hw, region, k).wf(),
    ensures
        MachineState::step(
            iommu_private_remove_machine_partial(sw1, hw, region, k),
            iommu_private_remove_machine_partial(sw1, hw, region, (k + 1) as nat),
            iommu_private_remove_ops(region)[k as int],
        ),
{
    let from_sw = iommu_private_remove_partial(sw1, region, k);
    let to_sw = iommu_private_remove_partial(sw1, region, (k + 1) as nat);
    let from_hw = synced_hw(from_sw, iommu_hw_unmapped(hw, region, k));
    let to_hw = synced_hw(to_sw, iommu_hw_unmapped(hw, region, (k + 1) as nat));
    let vm = region.vm;
    let gpa = region.guest_page(k);
    let page = region.phys_page(k);
    let key = VmPageKey::new(vm, gpa);
    let d = entry_prefix(region, k).dom();
    let d_next = entry_prefix(region, (k + 1) as nat).dom();

    lemma_phys_prefix_succ(region, k);
    lemma_entry_prefix_succ(region, k);
    assert(region.pages().contains(page));
    assert(region.entries().contains_key(key));
    assert(sw1.iommu_s2_map.contains_key(key) && sw1.iommu_s2_map[key] == region.entries()[key]);
    assert(!d.contains(key));
    assert(from_sw.iommu_s2_map.contains_key(key));
    assert(from_sw.iommu_s2_map[key].page == page);
    assert(sw1.iommu_private_pages[vm].contains(page));
    assert(!phys_prefix(region, k).contains(page));
    assert(from_sw.iommu_private_pages[vm].contains(page));
    assert(!from_sw.iommu_shared_pages.contains(page));
    assert(d_next =~= d.insert(key));
    assert(to_sw.iommu_s2_map =~= from_sw.iommu_s2_map.remove(key));
    lemma_private_pages_after_unmap_step(
        sw1.iommu_private_pages,
        from_sw.iommu_s2_map,
        to_sw.iommu_s2_map,
        vm,
        phys_prefix(region, k),
        key,
        page,
    );
    assert(SoftwareView::unmap_iommu_private_step(from_sw, to_sw, vm, gpa, page));

    assert(to_hw.iommu_s2map =~= from_hw.iommu_s2map.remove(key));
    assert(forall|tk: TlbKey|
        #![auto]
        tlb_prefix_keys(region, (k + 1) as nat).contains(tk) <==> (tlb_prefix_keys(
            region,
            k,
        ).contains(tk) || (tk.vm == vm && tk.gpa == gpa)));
    assert(to_hw.iommu_tlb =~= from_hw.iommu_tlb.remove_keys(
        Set::new(|tk: TlbKey| tk.vm == vm && tk.gpa == gpa),
    ));
    assert(HardwareView::iommu_unmap_invalidate_step(from_hw, to_hw, vm, gpa));
    refine_hv_unmap_iommu_private(from_sw, to_sw, from_hw, to_hw, vm, gpa, page);
}

/// Every prefix of an IOMMU-Private removal is a well-formed machine state.
/// The induction advances through the verified single-page edge.
proof fn lemma_iommu_private_remove_partial_wf(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    k: nat,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::iommu_remove_private_region_enabled(sw1, region),
        k <= region.count,
    ensures
        iommu_private_remove_machine_partial(sw1, hw, region, k).wf(),
    decreases k,
{
    lemma_sw_machine_wf_equiv(sw1, hw);
    if k == 0 {
        assert(phys_prefix(region, 0) =~= Set::<PhysPage>::empty());
        assert(entry_prefix(region, 0).dom() =~= Set::<VmPageKey>::empty());
        assert(tlb_prefix_keys(region, 0) =~= Set::<TlbKey>::empty());
        assert(iommu_private_remove_partial(sw1, region, 0) == sw1) by {
            let post_map = sw1.iommu_s2_map.remove_keys(entry_prefix(region, 0).dom());
            assert(post_map =~= sw1.iommu_s2_map);
            lemma_private_pages_after_unmap_empty(sw1.iommu_private_pages, post_map, region.vm);
        }
        assert(iommu_hw_unmapped(hw, region, 0) == hw) by {
            assert(hw.iommu_tlb.remove_keys(tlb_prefix_keys(region, 0)) =~= hw.iommu_tlb);
        }
        assert(MachineState::assemble(sw1, hw).sync());
        assert(MachineState::assemble(sw1, hw).iommu_sync());
    } else {
        lemma_iommu_private_remove_partial_wf(sw1, hw, region, (k - 1) as nat);
        lemma_iommu_private_remove_edge(sw1, hw, region, (k - 1) as nat);
    }
}

/// A bulk IOMMU private removal runs one combined unmap/release per page.
pub proof fn lemma_iommu_remove_private_region_machine_trace(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw: HardwareView,
    region: Region,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::iommu_remove_private_region_enabled(sw1, region),
        SoftwareView::iommu_remove_private_region_step(sw1, sw2, region),
    ensures
        run_op_sequence(
            MachineState::assemble(sw1, hw),
            MachineState::assemble(sw2, synced_hw(sw2, iommu_hw_after_unmap_region(hw, region))),
            iommu_private_remove_ops(region),
        ),
{
    let n = region.count;
    let ops = iommu_private_remove_ops(region);
    let states = Seq::new(
        (n + 1) as nat,
        |i: int| iommu_private_remove_machine_partial(sw1, hw, region, i as nat),
    );
    assert(ops.len() == n && states.len() == n + 1);
    assert(phys_prefix(region, 0) =~= Set::<PhysPage>::empty());
    assert(entry_prefix(region, 0).dom() =~= Set::<VmPageKey>::empty());
    assert(tlb_prefix_keys(region, 0) =~= Set::<TlbKey>::empty());
    assert(phys_prefix(region, n) =~= region.pages());
    assert(entry_prefix(region, n).dom() =~= region.entries().dom());
    lemma_iommu_private_remove_partial_wf(sw1, hw, region, 0);
    lemma_sw_machine_wf_equiv(sw1, hw);
    assert(iommu_private_remove_partial(sw1, region, 0) == sw1) by {
        let post_map = sw1.iommu_s2_map.remove_keys(entry_prefix(region, 0).dom());
        assert(post_map =~= sw1.iommu_s2_map);
        lemma_private_pages_after_unmap_empty(sw1.iommu_private_pages, post_map, region.vm);
    }
    assert(iommu_hw_unmapped(hw, region, 0) == hw) by {
        assert(hw.iommu_tlb.remove_keys(tlb_prefix_keys(region, 0)) =~= hw.iommu_tlb);
    }
    assert(states[0] == MachineState::assemble(sw1, hw)) by {
        assert(MachineState::assemble(sw1, hw).sync());
        assert(MachineState::assemble(sw1, hw).iommu_sync());
    }
    assert(iommu_private_remove_partial(sw1, region, n) == sw2);
    assert(states[states.len() - 1] == MachineState::assemble(
        sw2,
        synced_hw(sw2, iommu_hw_after_unmap_region(hw, region)),
    ));
    assert forall|i: int| 0 <= i < ops.len() implies #[trigger] MachineState::step(
        states[i],
        states[i + 1],
        ops[i],
    ) by {
        lemma_iommu_private_remove_partial_wf(sw1, hw, region, i as nat);
        lemma_iommu_private_remove_edge(sw1, hw, region, i as nat);
    }
    lemma_run_op_sequence_from_states(states, ops);
}

// ---------------------------------------------------------------------------
// IOMMU shared insert
// ---------------------------------------------------------------------------
pub open spec fn iommu_shared_insert_partial(
    s1: SoftwareView,
    region: Region,
    k: nat,
) -> SoftwareView {
    SoftwareView {
        iommu_shared_pages: s1.iommu_shared_pages.union(phys_prefix(region, k)),
        iommu_s2_map: s1.iommu_s2_map.union_prefer_right(entry_prefix(region, k)),
        ..s1
    }
}

pub open spec fn iommu_shared_insert_machine_partial(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    k: nat,
) -> MachineState {
    let sw = iommu_shared_insert_partial(sw1, region, k);
    MachineState::assemble(sw, synced_hw(sw, hw))
}

/// Refine one page of an IOMMU shared insertion to the machine
/// shared-map action while preserving any existing physical aliases.
proof fn lemma_iommu_shared_insert_edge(sw1: SoftwareView, hw: HardwareView, region: Region, k: nat)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::iommu_insert_shared_region_enabled(sw1, region),
        k < region.count,
        iommu_shared_insert_machine_partial(sw1, hw, region, k).wf(),
    ensures
        MachineState::step(
            iommu_shared_insert_machine_partial(sw1, hw, region, k),
            iommu_shared_insert_machine_partial(sw1, hw, region, (k + 1) as nat),
            iommu_shared_insert_ops(region)[k as int],
        ),
{
    let from_sw = iommu_shared_insert_partial(sw1, region, k);
    let to_sw = iommu_shared_insert_partial(sw1, region, (k + 1) as nat);
    let from_hw = synced_hw(from_sw, hw);
    let to_hw = synced_hw(to_sw, hw);
    let vm = region.vm;
    let gpa = region.guest_page(k);
    let page = region.phys_page(k);
    let key = VmPageKey::new(vm, gpa);
    let entry = S2Entry { page, access: region.access, generation: 0 };

    lemma_phys_prefix_succ(region, k);
    lemma_entry_prefix_succ(region, k);
    assert(region.pages().contains(page));
    assert(forall|v: VmId| #[trigger]
        from_sw.all_vms.contains(v) ==> !from_sw.s2_private_pages[v].contains(page)
            && !from_sw.iommu_private_pages[v].contains(page));
    assert(!sw1.iommu_s2_map.contains_key(key)) by {
        assert(region.entries().contains_key(key));
    }
    assert(!entry_prefix(region, k).dom().contains(key));
    assert(!from_sw.iommu_s2_map.contains_key(key));
    assert(sw1.iommu_shared_pages.union(phys_prefix(region, k)).insert(page)
        =~= sw1.iommu_shared_pages.union(phys_prefix(region, (k + 1) as nat)));
    assert(from_sw.iommu_s2_map.insert(key, entry) =~= to_sw.iommu_s2_map);
    assert(SoftwareView::map_iommu_shared_step(from_sw, to_sw, vm, gpa, entry));
    assert(HardwareView::iommu_map_step(from_hw, to_hw, vm, gpa, entry));
    refine_hv_map_iommu_shared(from_sw, to_sw, from_hw, to_hw, vm, gpa, entry);
}

/// Every prefix of an IOMMU shared insertion is a well-formed machine state.
/// The induction advances through the verified single-page edge.
proof fn lemma_iommu_shared_insert_partial_wf(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    k: nat,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::iommu_insert_shared_region_enabled(sw1, region),
        k <= region.count,
    ensures
        iommu_shared_insert_machine_partial(sw1, hw, region, k).wf(),
    decreases k,
{
    if k == 0 {
        assert(phys_prefix(region, 0) =~= Set::<PhysPage>::empty());
        assert(entry_prefix(region, 0) =~= Map::<VmPageKey, S2Entry>::empty());
        assert(iommu_shared_insert_partial(sw1, region, 0) == sw1) by {
            assert(sw1.iommu_shared_pages.union(phys_prefix(region, 0)) =~= sw1.iommu_shared_pages);
            assert(sw1.iommu_s2_map.union_prefer_right(entry_prefix(region, 0))
                =~= sw1.iommu_s2_map);
        }
        assert(MachineState::assemble(sw1, hw).sync());
        assert(MachineState::assemble(sw1, hw).iommu_sync());
    } else {
        lemma_iommu_shared_insert_partial_wf(sw1, hw, region, (k - 1) as nat);
        lemma_iommu_shared_insert_edge(sw1, hw, region, (k - 1) as nat);
    }
}

/// A bulk IOMMU shared insertion runs one shared map per page.
pub proof fn lemma_iommu_insert_shared_region_machine_trace(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw: HardwareView,
    region: Region,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::iommu_insert_shared_region_enabled(sw1, region),
        SoftwareView::iommu_insert_shared_region_step(sw1, sw2, region),
    ensures
        run_op_sequence(
            MachineState::assemble(sw1, hw),
            MachineState::assemble(sw2, synced_hw(sw2, hw)),
            iommu_shared_insert_ops(region),
        ),
{
    let n = region.count;
    let ops = iommu_shared_insert_ops(region);
    let states = Seq::new(
        (n + 1) as nat,
        |i: int| iommu_shared_insert_machine_partial(sw1, hw, region, i as nat),
    );
    assert(ops.len() == n && states.len() == n + 1);
    assert(phys_prefix(region, 0) =~= Set::<PhysPage>::empty());
    assert(entry_prefix(region, 0) =~= Map::<VmPageKey, S2Entry>::empty());
    assert(phys_prefix(region, n) =~= region.pages());
    assert(entry_prefix(region, n) =~= region.entries());
    assert(iommu_shared_insert_partial(sw1, region, 0) == sw1) by {
        assert(sw1.iommu_shared_pages.union(phys_prefix(region, 0)) =~= sw1.iommu_shared_pages);
        assert(sw1.iommu_s2_map.union_prefer_right(entry_prefix(region, 0)) =~= sw1.iommu_s2_map);
    }
    assert(states[0] == MachineState::assemble(sw1, hw)) by {
        assert(MachineState::assemble(sw1, hw).sync());
        assert(MachineState::assemble(sw1, hw).iommu_sync());
    }
    assert(iommu_shared_insert_partial(sw1, region, n) == sw2);
    assert(states[states.len() - 1] == MachineState::assemble(sw2, synced_hw(sw2, hw)));
    assert forall|i: int| 0 <= i < ops.len() implies #[trigger] MachineState::step(
        states[i],
        states[i + 1],
        ops[i],
    ) by {
        lemma_iommu_shared_insert_partial_wf(sw1, hw, region, i as nat);
        lemma_iommu_shared_insert_edge(sw1, hw, region, i as nat);
    }
    lemma_run_op_sequence_from_states(states, ops);
}

// ---------------------------------------------------------------------------
// IOMMU shared remove
// ---------------------------------------------------------------------------
pub open spec fn iommu_shared_remove_prefix_map(s1: SoftwareView, region: Region, k: nat) -> Map<
    VmPageKey,
    S2Entry,
> {
    s1.iommu_s2_map.remove_keys(entry_prefix(region, k).dom())
}

pub open spec fn iommu_shared_pages_after_remove_prefix(
    s1: SoftwareView,
    region: Region,
    k: nat,
) -> Set<PhysPage> {
    let post_map = iommu_shared_remove_prefix_map(s1, region, k);
    Set::new(
        |p: PhysPage|
            {
                &&& s1.iommu_shared_pages.contains(p)
                &&& (!phys_prefix(region, k).contains(p) || exists|q: VmPageKey| #[trigger]
                    post_map.contains_key(q) && post_map[q].page == p)
            },
    )
}

pub open spec fn iommu_shared_remove_partial(
    s1: SoftwareView,
    region: Region,
    k: nat,
) -> SoftwareView {
    SoftwareView {
        iommu_shared_pages: iommu_shared_pages_after_remove_prefix(s1, region, k),
        iommu_s2_map: iommu_shared_remove_prefix_map(s1, region, k),
        ..s1
    }
}

/// Characterize the dynamic `iommu_shared_pages` projection after one more shared
/// mapping is removed: the page remains exactly when another IOMMU alias exists.
proof fn lemma_iommu_shared_remove_projection_succ(s1: SoftwareView, region: Region, k: nat)
    requires
        s1.wf(),
        SoftwareView::iommu_remove_shared_region_enabled(s1, region),
        k < region.count,
    ensures
        ({
            let from = iommu_shared_remove_partial(s1, region, k);
            let to = iommu_shared_remove_partial(s1, region, (k + 1) as nat);
            let page = region.phys_page(k);
            let aliased = exists|q: VmPageKey| #[trigger]
                to.iommu_s2_map.contains_key(q) && to.iommu_s2_map[q].page == page;
            to.iommu_shared_pages == if aliased {
                from.iommu_shared_pages
            } else {
                from.iommu_shared_pages.remove(page)
            }
        }),
{
    let from = iommu_shared_remove_partial(s1, region, k);
    let to = iommu_shared_remove_partial(s1, region, (k + 1) as nat);
    let key = VmPageKey::new(region.vm, region.guest_page(k));
    let page = region.phys_page(k);
    let pp = phys_prefix(region, k);
    let aliased = exists|q: VmPageKey| #[trigger]
        to.iommu_s2_map.contains_key(q) && to.iommu_s2_map[q].page == page;
    lemma_phys_prefix_succ(region, k);
    lemma_entry_prefix_succ(region, k);
    assert(region.entries().contains_key(key));
    assert(s1.iommu_s2_map.contains_key(key) && s1.iommu_s2_map[key] == region.entries()[key]);
    assert(!entry_prefix(region, k).dom().contains(key));
    assert(from.iommu_s2_map.contains_key(key));
    assert(from.iommu_s2_map[key].page == page);
    assert(to.iommu_s2_map =~= from.iommu_s2_map.remove(key));
    assert forall|p: PhysPage| #[trigger] pp.contains(p) && p != page implies ((exists|q: VmPageKey|
     #[trigger]
        from.iommu_s2_map.contains_key(q) && from.iommu_s2_map[q].page == p) <==> (exists|
        q: VmPageKey,
    | #[trigger]
        to.iommu_s2_map.contains_key(q) && to.iommu_s2_map[q].page == p)) by {
        if exists|q: VmPageKey| #[trigger]
            from.iommu_s2_map.contains_key(q) && from.iommu_s2_map[q].page == p {
            let q = choose|q: VmPageKey| #[trigger]
                from.iommu_s2_map.contains_key(q) && from.iommu_s2_map[q].page == p;
            assert(q != key);
            assert(to.iommu_s2_map.contains_key(q));
        } else if exists|q: VmPageKey| #[trigger]
            to.iommu_s2_map.contains_key(q) && to.iommu_s2_map[q].page == p {
            let q = choose|q: VmPageKey| #[trigger]
                to.iommu_s2_map.contains_key(q) && to.iommu_s2_map[q].page == p;
            assert(from.iommu_s2_map.contains_key(q));
        }
    }
    if aliased {
        assert(to.iommu_shared_pages =~= from.iommu_shared_pages) by {
            assert forall|p: PhysPage| #[trigger]
                to.iommu_shared_pages.contains(p) <==> from.iommu_shared_pages.contains(p) by {
                if p == page {
                    assert(region.pages().contains(page));
                    assert(s1.iommu_shared_pages.contains(page));
                } else if pp.contains(p) {
                    assert((exists|q: VmPageKey| #[trigger]
                        from.iommu_s2_map.contains_key(q) && from.iommu_s2_map[q].page == p) <==> (
                    exists|q: VmPageKey| #[trigger]
                        to.iommu_s2_map.contains_key(q) && to.iommu_s2_map[q].page == p));
                }
            }
        }
    } else {
        assert(to.iommu_shared_pages =~= from.iommu_shared_pages.remove(page)) by {
            assert forall|p: PhysPage| #[trigger]
                to.iommu_shared_pages.contains(p) <==> from.iommu_shared_pages.remove(
                    page,
                ).contains(p) by {
                if p != page && pp.contains(p) {
                    assert((exists|q: VmPageKey| #[trigger]
                        from.iommu_s2_map.contains_key(q) && from.iommu_s2_map[q].page == p) <==> (
                    exists|q: VmPageKey| #[trigger]
                        to.iommu_s2_map.contains_key(q) && to.iommu_s2_map[q].page == p));
                }
            }
        }
    }
}

pub open spec fn iommu_shared_remove_machine_partial(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    k: nat,
) -> MachineState {
    let sw = iommu_shared_remove_partial(sw1, region, k);
    MachineState::assemble(sw, synced_hw(sw, iommu_hw_unmapped(hw, region, k)))
}

/// Refine one page of an IOMMU shared removal to the alias-aware machine
/// unmap action and invalidate matching SMMU-TLB entries.
proof fn lemma_iommu_shared_remove_edge(sw1: SoftwareView, hw: HardwareView, region: Region, k: nat)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::iommu_remove_shared_region_enabled(sw1, region),
        k < region.count,
        iommu_shared_remove_machine_partial(sw1, hw, region, k).wf(),
    ensures
        MachineState::step(
            iommu_shared_remove_machine_partial(sw1, hw, region, k),
            iommu_shared_remove_machine_partial(sw1, hw, region, (k + 1) as nat),
            iommu_shared_remove_ops(region)[k as int],
        ),
{
    let from_sw = iommu_shared_remove_partial(sw1, region, k);
    let to_sw = iommu_shared_remove_partial(sw1, region, (k + 1) as nat);
    let from_hw = synced_hw(from_sw, iommu_hw_unmapped(hw, region, k));
    let to_hw = synced_hw(to_sw, iommu_hw_unmapped(hw, region, (k + 1) as nat));
    let vm = region.vm;
    let gpa = region.guest_page(k);
    let page = region.phys_page(k);
    let key = VmPageKey::new(vm, gpa);

    lemma_sw_machine_wf_equiv(sw1, hw);
    lemma_iommu_shared_remove_projection_succ(sw1, region, k);
    lemma_phys_prefix_succ(region, k);
    lemma_entry_prefix_succ(region, k);
    assert(region.entries().contains_key(key));
    assert(sw1.iommu_s2_map.contains_key(key) && sw1.iommu_s2_map[key] == region.entries()[key]);
    assert(!entry_prefix(region, k).dom().contains(key));
    assert(from_sw.iommu_s2_map.contains_key(key));
    assert(from_sw.iommu_s2_map[key].page == page);
    assert(region.pages().contains(page));
    assert(sw1.iommu_shared_pages.contains(page));
    assert(!phys_prefix(region, k).contains(page));
    assert(from_sw.iommu_shared_pages.contains(page));
    assert(to_sw.iommu_s2_map =~= from_sw.iommu_s2_map.remove(key));
    assert(SoftwareView::unmap_iommu_shared_step(from_sw, to_sw, vm, gpa));

    assert(to_hw.iommu_s2map =~= from_hw.iommu_s2map.remove(key));
    assert(forall|tk: TlbKey|
        #![auto]
        tlb_prefix_keys(region, (k + 1) as nat).contains(tk) <==> (tlb_prefix_keys(
            region,
            k,
        ).contains(tk) || (tk.vm == vm && tk.gpa == gpa)));
    assert(to_hw.iommu_tlb =~= from_hw.iommu_tlb.remove_keys(
        Set::new(|tk: TlbKey| tk.vm == vm && tk.gpa == gpa),
    ));
    assert(HardwareView::iommu_unmap_invalidate_step(from_hw, to_hw, vm, gpa));
    refine_hv_unmap_iommu_shared(from_sw, to_sw, from_hw, to_hw, vm, gpa);
}

/// Every prefix of an IOMMU shared removal is a well-formed machine state.
/// The induction uses the alias-sensitive shared projection at each edge.
proof fn lemma_iommu_shared_remove_partial_wf(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    k: nat,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::iommu_remove_shared_region_enabled(sw1, region),
        k <= region.count,
    ensures
        iommu_shared_remove_machine_partial(sw1, hw, region, k).wf(),
    decreases k,
{
    lemma_sw_machine_wf_equiv(sw1, hw);
    if k == 0 {
        assert(phys_prefix(region, 0) =~= Set::<PhysPage>::empty());
        assert(entry_prefix(region, 0).dom() =~= Set::<VmPageKey>::empty());
        assert(tlb_prefix_keys(region, 0) =~= Set::<TlbKey>::empty());
        assert(iommu_shared_pages_after_remove_prefix(sw1, region, 0) =~= sw1.iommu_shared_pages);
        assert(iommu_shared_remove_prefix_map(sw1, region, 0) =~= sw1.iommu_s2_map);
        assert(iommu_shared_remove_partial(sw1, region, 0) == sw1);
        assert(iommu_hw_unmapped(hw, region, 0) == hw) by {
            assert(hw.iommu_tlb.remove_keys(tlb_prefix_keys(region, 0)) =~= hw.iommu_tlb);
        }
        assert(MachineState::assemble(sw1, hw).sync());
        assert(MachineState::assemble(sw1, hw).iommu_sync());
    } else {
        lemma_iommu_shared_remove_partial_wf(sw1, hw, region, (k - 1) as nat);
        lemma_iommu_shared_remove_edge(sw1, hw, region, (k - 1) as nat);
    }
}

/// A bulk IOMMU shared removal runs one alias-aware shared unmap per page.
pub proof fn lemma_iommu_remove_shared_region_machine_trace(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw: HardwareView,
    region: Region,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::iommu_remove_shared_region_enabled(sw1, region),
        SoftwareView::iommu_remove_shared_region_step(sw1, sw2, region),
    ensures
        run_op_sequence(
            MachineState::assemble(sw1, hw),
            MachineState::assemble(sw2, synced_hw(sw2, iommu_hw_after_unmap_region(hw, region))),
            iommu_shared_remove_ops(region),
        ),
{
    let n = region.count;
    let ops = iommu_shared_remove_ops(region);
    let states = Seq::new(
        (n + 1) as nat,
        |i: int| iommu_shared_remove_machine_partial(sw1, hw, region, i as nat),
    );
    assert(ops.len() == n && states.len() == n + 1);
    assert(phys_prefix(region, 0) =~= Set::<PhysPage>::empty());
    assert(entry_prefix(region, 0).dom() =~= Set::<VmPageKey>::empty());
    assert(tlb_prefix_keys(region, 0) =~= Set::<TlbKey>::empty());
    assert(phys_prefix(region, n) =~= region.pages());
    assert(entry_prefix(region, n).dom() =~= region.entries().dom());
    assert(iommu_shared_pages_after_remove_prefix(sw1, region, 0) =~= sw1.iommu_shared_pages);
    assert(iommu_shared_remove_prefix_map(sw1, region, 0) =~= sw1.iommu_s2_map);
    assert(iommu_shared_remove_partial(sw1, region, 0) == sw1);
    assert(iommu_hw_unmapped(hw, region, 0) == hw) by {
        assert(hw.iommu_tlb.remove_keys(tlb_prefix_keys(region, 0)) =~= hw.iommu_tlb);
    }
    assert(states[0] == MachineState::assemble(sw1, hw)) by {
        assert(MachineState::assemble(sw1, hw).sync());
        assert(MachineState::assemble(sw1, hw).iommu_sync());
    }
    assert(iommu_shared_remove_partial(sw1, region, n) == sw2);
    assert(states[states.len() - 1] == MachineState::assemble(
        sw2,
        synced_hw(sw2, iommu_hw_after_unmap_region(hw, region)),
    ));
    assert forall|i: int| 0 <= i < ops.len() implies #[trigger] MachineState::step(
        states[i],
        states[i + 1],
        ops[i],
    ) by {
        lemma_iommu_shared_remove_partial_wf(sw1, hw, region, i as nat);
        lemma_iommu_shared_remove_edge(sw1, hw, region, i as nat);
    }
    lemma_run_op_sequence_from_states(states, ops);
}

// ---------------------------------------------------------------------------
// §3  Policy-neutral software traces → machine traces
// ---------------------------------------------------------------------------
/// Hardware endpoint induced by one policy-neutral software operation. Mapping
/// inserts synchronize the edited walker map; removals additionally retain the
/// corresponding TLB invalidations. VM lifecycle operations leave hardware
/// unchanged.
pub open spec fn hardware_after_software_op(
    sw_post: SoftwareView,
    hw: HardwareView,
    op: SoftwareOp,
) -> HardwareView {
    match op {
        SoftwareOp::AddVm(vm) => hw,
        SoftwareOp::RemoveVm(vm) => hw,
        SoftwareOp::CpuInsertPrivateRegion(region) => synced_hw(sw_post, hw),
        SoftwareOp::CpuRemovePrivateRegion(region) => {
            synced_hw(sw_post, hw_after_unmap_region(hw, region))
        },
        SoftwareOp::CpuInsertSharedRegion(region) => synced_hw(sw_post, hw),
        SoftwareOp::CpuRemoveSharedRegion(region) => {
            synced_hw(sw_post, hw_after_unmap_region(hw, region))
        },
        SoftwareOp::MakeS2Shared(vm, page) => hw,
        SoftwareOp::MakeS2Private(vm, page) => hw,
        SoftwareOp::IommuInsertPrivateRegion(region) => synced_hw(sw_post, hw),
        SoftwareOp::IommuRemovePrivateRegion(region) => {
            synced_hw(sw_post, iommu_hw_after_unmap_region(hw, region))
        },
        SoftwareOp::IommuInsertSharedRegion(region) => synced_hw(sw_post, hw),
        SoftwareOp::IommuRemoveSharedRegion(region) => {
            synced_hw(sw_post, iommu_hw_after_unmap_region(hw, region))
        },
    }
}

/// Machine actions implementing one policy-neutral software operation.
pub open spec fn machine_ops_for_software_op(op: SoftwareOp) -> Seq<MachineAction> {
    match op {
        SoftwareOp::AddVm(vm) => seq![MachineAction::Hypervisor(HypervisorOp::AddVm(vm))],
        SoftwareOp::RemoveVm(vm) => { seq![MachineAction::Hypervisor(HypervisorOp::RemoveVm(vm))] },
        SoftwareOp::CpuInsertPrivateRegion(region) => cpu_private_insert_ops(region),
        SoftwareOp::CpuRemovePrivateRegion(region) => cpu_private_remove_ops(region),
        SoftwareOp::CpuInsertSharedRegion(region) => cpu_shared_insert_ops(region),
        SoftwareOp::CpuRemoveSharedRegion(region) => cpu_shared_remove_ops(region),
        SoftwareOp::MakeS2Shared(vm, page) => {
            seq![MachineAction::Hypervisor(HypervisorOp::MakeS2Shared(vm, page))]
        },
        SoftwareOp::MakeS2Private(vm, page) => {
            seq![MachineAction::Hypervisor(HypervisorOp::MakeS2Private(vm, page))]
        },
        SoftwareOp::IommuInsertPrivateRegion(region) => iommu_private_insert_ops(region),
        SoftwareOp::IommuRemovePrivateRegion(region) => iommu_private_remove_ops(region),
        SoftwareOp::IommuInsertSharedRegion(region) => iommu_shared_insert_ops(region),
        SoftwareOp::IommuRemoveSharedRegion(region) => iommu_shared_remove_ops(region),
    }
}

/// One policy-neutral software edge expands to its finite machine trace.
pub proof fn lemma_software_op_refines_machine_trace(
    sw_pre: SoftwareView,
    sw_post: SoftwareView,
    hw: HardwareView,
    op: SoftwareOp,
)
    requires
        MachineState::assemble(sw_pre, hw).wf(),
        SoftwareView::step(sw_pre, sw_post, op),
    ensures
        run_op_sequence(
            MachineState::assemble(sw_pre, hw),
            MachineState::assemble(sw_post, hardware_after_software_op(sw_post, hw, op)),
            machine_ops_for_software_op(op),
        ),
{
    match op {
        SoftwareOp::AddVm(vm) => {
            refine_hv_add_vm(sw_pre, sw_post, hw, vm);
            let action = MachineAction::Hypervisor(HypervisorOp::AddVm(vm));
            lemma_run_op_sequence_single(
                MachineState::assemble(sw_pre, hw),
                MachineState::assemble(sw_post, hw),
                action,
            );
        },
        SoftwareOp::RemoveVm(vm) => {
            let machine = MachineState::assemble(sw_pre, hw);
            lemma_machine_hw_wf(sw_pre, hw);
            assert forall|key: TlbKey| #[trigger] machine.tlb.contains_key(key) implies key.vm
                != vm by {
                if key.vm == vm {
                    let sw_key = VmPageKey::new(key.vm, key.gpa);
                    assert(hw.s2map.contains_key(sw_key));
                    assert(machine.sync());
                    assert(sw_pre.s2_map.contains_key(sw_key));
                    assert(false);
                }
            }
            refine_hv_remove_vm(sw_pre, sw_post, hw, vm);
            let action = MachineAction::Hypervisor(HypervisorOp::RemoveVm(vm));
            lemma_run_op_sequence_single(
                MachineState::assemble(sw_pre, hw),
                MachineState::assemble(sw_post, hw),
                action,
            );
        },
        SoftwareOp::CpuInsertPrivateRegion(region) => {
            lemma_cpu_insert_private_region_machine_trace(sw_pre, sw_post, hw, region);
        },
        SoftwareOp::CpuRemovePrivateRegion(region) => {
            lemma_cpu_remove_private_region_machine_trace(sw_pre, sw_post, hw, region);
        },
        SoftwareOp::CpuInsertSharedRegion(region) => {
            lemma_cpu_insert_shared_region_machine_trace(sw_pre, sw_post, hw, region);
        },
        SoftwareOp::CpuRemoveSharedRegion(region) => {
            lemma_cpu_remove_shared_region_machine_trace(sw_pre, sw_post, hw, region);
        },
        SoftwareOp::MakeS2Shared(vm, page) => {
            refine_hv_make_s2_shared(sw_pre, sw_post, hw, vm, page);
            let action = MachineAction::Hypervisor(HypervisorOp::MakeS2Shared(vm, page));
            lemma_run_op_sequence_single(
                MachineState::assemble(sw_pre, hw),
                MachineState::assemble(sw_post, hw),
                action,
            );
        },
        SoftwareOp::MakeS2Private(vm, page) => {
            refine_hv_make_s2_private(sw_pre, sw_post, hw, vm, page);
            let action = MachineAction::Hypervisor(HypervisorOp::MakeS2Private(vm, page));
            lemma_run_op_sequence_single(
                MachineState::assemble(sw_pre, hw),
                MachineState::assemble(sw_post, hw),
                action,
            );
        },
        SoftwareOp::IommuInsertPrivateRegion(region) => {
            lemma_iommu_insert_private_region_machine_trace(sw_pre, sw_post, hw, region);
        },
        SoftwareOp::IommuRemovePrivateRegion(region) => {
            lemma_iommu_remove_private_region_machine_trace(sw_pre, sw_post, hw, region);
        },
        SoftwareOp::IommuInsertSharedRegion(region) => {
            lemma_iommu_insert_shared_region_machine_trace(sw_pre, sw_post, hw, region);
        },
        SoftwareOp::IommuRemoveSharedRegion(region) => {
            lemma_iommu_remove_shared_region_machine_trace(sw_pre, sw_post, hw, region);
        },
    }
}

/// Compose an arbitrary finite software trace into a finite machine trace while
/// threading the policy-neutral hardware endpoint between operations.
pub proof fn lemma_software_trace_refines_machine_trace(
    sw_start: SoftwareView,
    sw_end: SoftwareView,
    hw_start: HardwareView,
    sw_ops: Seq<SoftwareOp>,
) -> (result: (HardwareView, Seq<MachineAction>))
    requires
        MachineState::assemble(sw_start, hw_start).wf(),
        run_software_ops(sw_start, sw_end, sw_ops),
    ensures
        run_op_sequence(
            MachineState::assemble(sw_start, hw_start),
            MachineState::assemble(sw_end, result.0),
            result.1,
        ),
    decreases sw_ops.len(),
{
    if sw_ops.len() == 0 {
        (hw_start, Seq::empty())
    } else {
        let sw_next = choose|sw_next: SoftwareView|
            SoftwareView::step(sw_start, sw_next, sw_ops[0]) && SoftwareView::run_ops(
                sw_next,
                sw_end,
                sw_ops.skip(1),
            );
        let op = sw_ops[0];
        let hw_next = hardware_after_software_op(sw_next, hw_start, op);
        let first_ops = machine_ops_for_software_op(op);
        lemma_software_op_refines_machine_trace(sw_start, sw_next, hw_start, op);
        lemma_run_op_sequence_end_wf(
            MachineState::assemble(sw_start, hw_start),
            MachineState::assemble(sw_next, hw_next),
            first_ops,
        );
        let rest = lemma_software_trace_refines_machine_trace(
            sw_next,
            sw_end,
            hw_next,
            sw_ops.skip(1),
        );
        lemma_run_op_sequence_concat(
            MachineState::assemble(sw_start, hw_start),
            MachineState::assemble(sw_next, hw_next),
            MachineState::assemble(sw_end, rest.0),
            first_ops,
            rest.1,
        );
        (rest.0, first_ops + rest.1)
    }
}

} // verus!
