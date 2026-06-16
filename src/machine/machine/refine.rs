use vstd::prelude::*;

use super::state::MachineState;
use crate::machine::hardware::HardwareOps;
use crate::machine::hardware::HwView;
use crate::machine::software::proof::{
    lemma_assign_page_step_preserves_wf, lemma_map_step_preserves_wf,
    lemma_reclaim_page_step_preserves_wf, lemma_share_page_step_preserves_wf,
    lemma_unmap_step_preserves_wf, lemma_unshare_page_step_preserves_wf,
};
use crate::machine::software::SoftwareOps;
use crate::machine::software::SwView;
use crate::machine::types::*;

verus! {

// ---------------------------------------------------------------------------
// Refinement: (SW step + HW step) ⟹ machine step
//
// Each `refine_*` lemma shows that composing the matching software and
// hardware sub-steps produces the corresponding high-level machine step.
//
// Decomposition of `MachineState::wf`: the ownership/sharing/translation clauses
// are exactly `SwView::wf` (the `lemma_sw_machine_wf_equiv` bridge below), so a
// refinement only has to additionally re-establish the two cross-cutting clauses
// — `execution_wf` and `tlb_safe`.  SW steps inherit their three clauses from the
// SwView `wf`-preservation proofs via the bridge.
// ---------------------------------------------------------------------------
/// Bridge: the assembled machine state's SW-side `wf` clauses *are* the software
/// view's, because `assemble` copies the SW fields verbatim and both views define
/// the predicates identically.  Lets each `refine_*` delegate the
/// ownership/sharing/translation obligations to the SwView `wf` proofs.
pub proof fn lemma_sw_machine_wf_equiv(sw: SwView, hw: HwView)
    ensures
        MachineState::assemble(sw, hw).ownership_wf() == sw.ownership_wf(),
        MachineState::assemble(sw, hw).sharing_wf() == sw.sharing_wf(),
        MachineState::assemble(sw, hw).translation_wf() == sw.translation_wf(),
{
    let m = MachineState::assemble(sw, hw);
    assert(m.all_vms == sw.all_vms);
    assert(m.vm_owned == sw.vm_owned);
    assert(m.hypervisor_owned == sw.hypervisor_owned);
    assert(m.shared_pages == sw.shared_pages);
    assert(m.s2_map == sw.s2_map);
    // `shared_with` — hence `owned_or_shared`, hence `translation_wf` — coincides,
    // since both are `exists`/disjunctions over the same (copied) fields.
    assert forall|vm: VmId, page: PhysPage| #[trigger] m.owned_or_shared(vm, page)
        == sw.owned_or_shared(vm, page) by {
        assert(m.shared_with(vm, page) == sw.shared_with(vm, page));
    }
}
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
    // SW clauses (ownership/sharing/translation) via the bridge + the SwView map
    // proof; the two cross-cutting clauses inline.
    lemma_sw_machine_wf_equiv(sw1, hw1);
    assert(sw1.wf());
    lemma_map_step_preserves_wf(sw1, sw2, vm, gpa, entry);
    lemma_sw_machine_wf_equiv(sw2, hw2);
    assert(s2.execution_wf());
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

/// A SW unmap step, composed with the same complete TLB-maintenance sequence as
/// `refine_hv_map` (`pending → TLBI IPAS2E1IS → DSB ISH`), refines
/// `hv_unmap_step`.
pub proof fn refine_hv_unmap(
    sw1: SwView,
    sw2: SwView,
    hw1: HwView,
    hw_pend: HwView,
    hw_tlbi: HwView,
    hw2: HwView,
    vm: VmId,
    gpa: GuestPage,
)
    requires
        SwView::unmap_step(sw1, sw2, vm, gpa),
        HwView::pending_invalidation_step(hw1, hw_pend, vm, gpa),
        HwView::tlbi_ipa_broadcast_step(hw_pend, hw_tlbi, vm, gpa),
        HwView::dsb_step(hw_tlbi, hw2),
        MachineState::assemble(sw1, hw1).wf(),
    ensures
        MachineState::hv_unmap_step(
            MachineState::assemble(sw1, hw1),
            MachineState::assemble(sw2, hw2),
            vm,
            gpa,
        ),
{
    let s1 = MachineState::assemble(sw1, hw1);
    let s2 = MachineState::assemble(sw2, hw2);
    let key = VmPageKey::new(vm, gpa);
    let targets = s1.invalidation_targets(vm, gpa);

    // Same flush as the map case: the broadcast TLBI removes exactly the (vm, gpa)
    // entries; pending broadcast and DSB leave the TLB untouched.
    assert(targets =~= Set::new(
        |k: TlbKey| k.vm == vm && k.gpa == gpa && hw_pend.tlb.contains_key(k),
    ));
    assert(s2.tlb =~= s1.tlb.remove_keys(targets));
    assert(s2.active_vm == s1.active_vm);
    assert(s2.memory == s1.memory);
    assert(s2.all_vms == s1.all_vms);
    assert(s2.vm_owned == s1.vm_owned);
    assert(s2.hypervisor_owned == s1.hypervisor_owned);
    assert(s2.shared_pages == s1.shared_pages);
    assert(s2.s2_map == s1.s2_map.remove(key));

    // s2.wf(): SW clauses via the bridge + the SwView unmap proof; the two
    // cross-cutting clauses inline.
    lemma_sw_machine_wf_equiv(sw1, hw1);
    assert(sw1.wf());
    lemma_unmap_step_preserves_wf(sw1, sw2, vm, gpa);
    lemma_sw_machine_wf_equiv(sw2, hw2);
    assert(s2.execution_wf());
    // tlb_safe: a surviving cached key `k` was not flushed ⇒ (k.vm, k.gpa) ≠ (vm, gpa),
    // so its s2-key survives the `remove` with an unchanged value.
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
    let s1 = MachineState::assemble(sw1, hw);
    let s2 = MachineState::assemble(sw2, hw);
    // Pure-SW: HW state (tlb, active_vm, memory) is unchanged.
    lemma_sw_machine_wf_equiv(sw1, hw);
    assert(sw1.wf());
    lemma_assign_page_step_preserves_wf(sw1, sw2, vm, page);
    lemma_sw_machine_wf_equiv(sw2, hw);
    // execution_wf (active_vm, all_vms unchanged) and tlb_safe (tlb, s2_map unchanged)
    // carry over from `s1`.
    assert(s2.all_vms == s1.all_vms);
    assert(s2.active_vm == s1.active_vm);
    assert(s2.tlb == s1.tlb);
    assert(s2.s2_map == s1.s2_map);
    assert(s2.execution_wf());
    assert(s1.tlb_safe());
    assert(s2.wf());
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
    let s1 = MachineState::assemble(sw1, hw);
    let s2 = MachineState::assemble(sw2, hw);
    lemma_sw_machine_wf_equiv(sw1, hw);
    assert(sw1.wf());
    // The machine-level `page_is_quiescent` supplies the SwView reclaim lemma's
    // premises (no surviving mapping or sharing edge targets `page`); `sw1` shares
    // `s1`'s `s2_map`/`shared_pages`.
    assert forall|k: VmPageKey| #[trigger] sw1.s2_map.contains_key(k) implies sw1.s2_map[k].page
        != page by {
        assert(s1.s2_map.contains_key(k));
    }
    assert forall|e: SharedPage| #[trigger] sw1.shared_pages.contains(e) implies e.page != page by {
        assert(s1.shared_pages.contains(e));
    }
    lemma_reclaim_page_step_preserves_wf(sw1, sw2, vm, page);
    lemma_sw_machine_wf_equiv(sw2, hw);
    assert(s2.all_vms == s1.all_vms);
    assert(s2.active_vm == s1.active_vm);
    assert(s2.tlb == s1.tlb);
    assert(s2.s2_map == s1.s2_map);
    assert(s2.execution_wf());
    assert(s1.tlb_safe());
    assert(s2.wf());
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
    let s1 = MachineState::assemble(sw1, hw);
    let s2 = MachineState::assemble(sw2, hw);
    lemma_sw_machine_wf_equiv(sw1, hw);
    assert(sw1.wf());
    lemma_share_page_step_preserves_wf(sw1, sw2, left, right, page);
    lemma_sw_machine_wf_equiv(sw2, hw);
    // Translation state (s2_map, tlb, active_vm) unchanged ⇒ cross-cutting clauses
    // carry over.
    assert(s2.all_vms == s1.all_vms);
    assert(s2.active_vm == s1.active_vm);
    assert(s2.tlb == s1.tlb);
    assert(s2.s2_map == s1.s2_map);
    assert(s2.execution_wf());
    assert(s1.tlb_safe());
    assert(s2.wf());
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
        // No-dangling guard (cf. `hv_unshare_page_step`): an endpoint that maps
        // `page` must own it, so dropping the share strands no translation.
        forall|k: VmPageKey|
            #[trigger] MachineState::assemble(sw1, hw).s2_map.contains_key(k) && (k.vm == left
                || k.vm == right) && MachineState::assemble(sw1, hw).s2_map[k].page == page
                ==> MachineState::assemble(sw1, hw).vm_owned[k.vm].contains(page),
    ensures
        MachineState::hv_unshare_page_step(
            MachineState::assemble(sw1, hw),
            MachineState::assemble(sw2, hw),
            left,
            right,
            page,
        ),
{
    let s1 = MachineState::assemble(sw1, hw);
    let s2 = MachineState::assemble(sw2, hw);
    lemma_sw_machine_wf_equiv(sw1, hw);
    assert(sw1.wf());
    // The guard transfers to `sw1` (same `s2_map`/`vm_owned` as `s1`).
    assert forall|k: VmPageKey| #[trigger] sw1.s2_map.contains_key(k) && (k.vm == left || k.vm
        == right) && sw1.s2_map[k].page == page implies sw1.vm_owned[k.vm].contains(page) by {
        assert(s1.s2_map.contains_key(k));
    }
    lemma_unshare_page_step_preserves_wf(sw1, sw2, left, right, page);
    lemma_sw_machine_wf_equiv(sw2, hw);
    assert(s2.all_vms == s1.all_vms);
    assert(s2.active_vm == s1.active_vm);
    assert(s2.tlb == s1.tlb);
    assert(s2.s2_map == s1.s2_map);
    assert(s2.execution_wf());
    assert(s1.tlb_safe());
    assert(s2.wf());
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
    let s1 = MachineState::assemble(sw, hw1);
    let s2 = MachineState::assemble(sw, hw2);
    // Pure-HW: the SW view is shared, so via the bridge the three SW clauses equal
    // `sw`'s on both states, hence hold for `s2` from `s1.wf()`.
    lemma_sw_machine_wf_equiv(sw, hw1);
    lemma_sw_machine_wf_equiv(sw, hw2);
    assert(s2.ownership_wf());
    assert(s2.sharing_wf());
    assert(s2.translation_wf());
    // execution_wf: `active_vm` is extended by `cpu ↦ vm` with `vm ∈ all_vms`.
    assert(s2.all_vms == s1.all_vms);
    assert(s2.active_vm == s1.active_vm.insert(cpu, vm));
    assert(s1.all_vms.contains(vm));
    assert forall|c: CpuId| #[trigger] s2.active_vm.contains_key(c) implies s2.all_vms.contains(
        s2.active_vm[c],
    ) by {
        if c != cpu {
            assert(s1.active_vm.contains_key(c) && s2.active_vm[c] == s1.active_vm[c]);
        }
    }
    // tlb_safe: `tlb` and `s2_map` are unchanged.
    assert(s2.tlb == s1.tlb);
    assert(s2.s2_map == s1.s2_map);
    assert(s1.tlb_safe());
    assert(s2.wf());
}

} // verus!
