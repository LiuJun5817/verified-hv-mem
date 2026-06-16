//! Hardware `wf`-preservation: `HwView::wf` (pending invalidations ⊆ cached TLB
//! entries) is an inductive invariant of every `HwView` step.
use vstd::prelude::*;

use super::HwView;
use crate::machine::types::*;

verus! {

pub proof fn lemma_pending_invalidation_preserves_wf(
    s1: HwView,
    s2: HwView,
    vm: VmId,
    gpa: GuestPage,
)
    requires
        s1.wf(),
        HwView::pending_invalidation_step(s1, s2, vm, gpa),
    ensures
        s2.wf(),
{
    assert forall|key: TlbKey| s2.pending_invalidations.contains(key) implies s2.tlb.contains_key(
        key,
    ) by {
        if s1.pending_invalidations.contains(key) {
        }
    }
}

pub proof fn lemma_tlb_fill_preserves_wf(
    s1: HwView,
    s2: HwView,
    s2_map: Map<VmPageKey, S2Entry>,
    cpu: CpuId,
    vm: VmId,
    gpa: GuestPage,
)
    requires
        s1.wf(),
        HwView::tlb_fill_step(s1, s2, s2_map, cpu, vm, gpa),
    ensures
        s2.wf(),
{
    // `tlb` only grows; `pending` is unchanged.
}

pub proof fn lemma_tlbi_preserves_wf(s1: HwView, s2: HwView, cpu: CpuId, vm: VmId, gpa: GuestPage)
    requires
        s1.wf(),
        HwView::tlbi_step(s1, s2, cpu, vm, gpa),
    ensures
        s2.wf(),
{
    let tkey = TlbKey::new(cpu, vm, gpa);
    assert forall|key: TlbKey| s2.pending_invalidations.contains(key) implies s2.tlb.contains_key(
        key,
    ) by {
        assert(s1.pending_invalidations.contains(key) && key != tkey);
    }
}

pub proof fn lemma_tlbi_ipa_broadcast_preserves_wf(s1: HwView, s2: HwView, vm: VmId, gpa: GuestPage)
    requires
        s1.wf(),
        HwView::tlbi_ipa_broadcast_step(s1, s2, vm, gpa),
    ensures
        s2.wf(),
{
    let targets = Set::new(
        |key: TlbKey| key.vm == vm && key.gpa == gpa && s1.tlb.contains_key(key),
    );
    // A surviving pending key was pending in `s1` (so cached, by `wf`) and is not
    // a flushed target, so it survives in `s2.tlb` too.
    assert forall|key: TlbKey| s2.pending_invalidations.contains(key) implies s2.tlb.contains_key(
        key,
    ) by {
        assert(s1.pending_invalidations.contains(key) && !targets.contains(key));
    }
}

pub proof fn lemma_context_switch_preserves_wf(s1: HwView, s2: HwView, cpu: CpuId, vm: VmId)
    requires
        s1.wf(),
        HwView::context_switch_step(s1, s2, cpu, vm),
    ensures
        s2.wf(),
{
}

pub proof fn lemma_dsb_preserves_wf(s1: HwView, s2: HwView)
    requires
        s1.wf(),
        HwView::dsb_step(s1, s2),
    ensures
        s2.wf(),
{
}

pub proof fn lemma_isb_preserves_wf(s1: HwView, s2: HwView)
    requires
        s1.wf(),
        HwView::isb_step(s1, s2),
    ensures
        s2.wf(),
{
}

pub proof fn lemma_mem_read_preserves_wf(s1: HwView, s2: HwView, pa: PhysWordAddr)
    requires
        s1.wf(),
        HwView::mem_read_step(s1, s2, pa),
    ensures
        s2.wf(),
{
}

pub proof fn lemma_mem_write_preserves_wf(s1: HwView, s2: HwView, pa: PhysWordAddr, value: DataWord)
    requires
        s1.wf(),
        HwView::mem_write_step(s1, s2, pa, value),
    ensures
        s2.wf(),
{
    // `tlb` and `pending` are unchanged.
}

} // verus!
