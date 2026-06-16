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
/// A SW map step, composed with the **complete** stage-2 TLB-maintenance
/// sequence that accompanies the PTE write, refines the machine-level
/// `hv_map_step`.
///
/// The high-level `hv_map_step` models TLB invalidation *synchronously*: the
/// stale `(vm, gpa)` entries are flushed atomically with the mapping edit, and
/// the post-state is `tlb_safe`.  To discharge that abstraction soundly the
/// hardware side must actually run the maintenance to completion, not merely
/// mark the entries pending.  The sequence is the break-before-make TLB
/// shootdown:
///
/// 1. `pending_invalidation_step` — broadcast intent (mark `(vm, gpa)` pending);
/// 2. `tlbi_ipa_broadcast_step`   — `TLBI IPAS2E1IS`, invalidate the IPA on all PEs;
/// 3. `dsb_step`                  — `DSB ISH`, wait for completion on every PE.
///
/// Only after the completing `DSB` retires is no PE holding the stale entry, so
/// it is `hw2` (the post-DSB state) that the synchronous flush refines.
pub proof fn refine_hv_map(
    sw1: SwView,
    sw2: SwView,
    hw1: HwView,
    hw_pend: HwView,
    hw_tlbi: HwView,
    hw2: HwView,
    vm: VmId,
    gpa: GuestPage,
    entry: S2Entry,
)
    requires
        SwView::map_step(sw1, sw2, vm, gpa, entry),
        HwView::pending_invalidation_step(hw1, hw_pend, vm, gpa),
        HwView::tlbi_ipa_broadcast_step(hw_pend, hw_tlbi, vm, gpa),
        HwView::dsb_step(hw_tlbi, hw2),
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
    let s1 = MachineState::assemble(sw1, hw1);
    let s2 = MachineState::assemble(sw2, hw2);
    let key = VmPageKey::new(vm, gpa);
    let targets = s1.invalidation_targets(vm, gpa);

    // ── The maintenance sequence flushes exactly the stale (vm, gpa) entries. ──
    // The pending broadcast and the DSB leave the TLB untouched; the broadcast
    // TLBI removes the (vm, gpa) entries.  Its target set is computed on
    // `hw_pend.tlb == hw1.tlb`, so it coincides with `s1.invalidation_targets`.
    assert(targets =~= Set::new(
        |k: TlbKey| k.vm == vm && k.gpa == gpa && hw_pend.tlb.contains_key(k),
    ));
    assert(s2.tlb =~= s1.tlb.remove_keys(targets));
    assert(s2.active_vm == s1.active_vm);
    assert(s2.memory == s1.memory);

    // The SW step leaves identity, ownership and sharing untouched; only `s2_map`
    // grows by the new entry.  Make these field equalities explicit so the `wf`
    // sub-invariants can be inherited from `s1`.
    assert(s2.all_vms == s1.all_vms);
    assert(s2.vm_owned == s1.vm_owned);
    assert(s2.hypervisor_owned == s1.hypervisor_owned);
    assert(s2.shared_pages == s1.shared_pages);
    assert(s2.s2_map == s1.s2_map.insert(key, entry));

    // ── s2.wf() ────────────────────────────────────────────────────────────
    // Ownership / sharing / execution depend only on the SW fields and
    // `active_vm`, all unchanged from `s1` (which is `wf`).
    assert(s2.ownership_wf());
    assert(s2.sharing_wf());
    assert(s2.execution_wf());
    // translation_wf: the new key targets `entry.page` (owned-or-shared by `vm`,
    // from `map_step`); every surviving key keeps its valid target.
    assert forall|k: VmPageKey| #[trigger] s2.s2_map.contains_key(k) implies (s2.all_vms.contains(
        k.vm,
    ) && s2.owned_or_shared(k.vm, s2.s2_map[k].page)) by {
        if k == key {
            // `map_step` exposes `vm ∈ all_vms` and `owned_or_shared(vm, entry.page)`
            // on `sw1`; the relevant fields agree with `s1`/`s2`, so it transfers.
            assert(s2.s2_map[key] == entry);
            assert(sw1.all_vms.contains(vm));
            assert(sw1.owned_or_shared(vm, entry.page));
        } else {
            assert(s1.s2_map.contains_key(k));
        }
    }
    // tlb_safe: a surviving cached entry `k` was not flushed, so (k.vm, k.gpa) ≠
    // (vm, gpa); its s2-key is untouched by the insert and its cached value is
    // untouched by the flush, so the agreement from `s1.tlb_safe` carries over.
    assert(s1.tlb_safe());
    assert forall|k: TlbKey| #[trigger] s2.tlb.contains_key(k) implies {
        let sk = VmPageKey::new(k.vm, k.gpa);
        &&& s2.s2_map.contains_key(sk)
        &&& s2.tlb[k].as_s2_entry() == s2.s2_map[sk]
    } by {
        assert(s1.tlb.contains_key(k) && !targets.contains(k));
        assert(VmPageKey::new(k.vm, k.gpa) != key);
    }
    assert(s2.wf());
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

} // verus!
