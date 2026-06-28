//! Hardware `wf`-preservation: [`HwView::wf`] — TLB coherence (`tlb_safe`) — is an
//! inductive invariant of every `HwView` step.
//!
//! `tlb_safe` (every cached entry agrees with the hardware-reachable `s2map`) is a
//! genuine hardware invariant under atomic invalidation: the only step that drops a
//! page from `s2map` ([`HwView::unmap_invalidate_step`]) flushes its cached entries
//! in the same step, so no cached entry ever outlives its mapping.
use vstd::prelude::*;

use super::HwView;
use crate::machine::types::*;

verus! {

/// If `tlb` and `s2map` are unchanged, `tlb_safe` carries over verbatim.
proof fn lemma_tlb_safe_unchanged(s1: HwView, s2: HwView)
    requires
        s1.tlb_safe(),
        s2.tlb == s1.tlb,
        s2.s2map == s1.s2map,
    ensures
        s2.tlb_safe(),
{
    assert forall|key: TlbKey| #[trigger] s2.tlb.contains_key(key) implies {
        let sk = VmPageKey::new(key.vm, key.gpa);
        &&& s2.s2map.contains_key(sk)
        &&& s2.tlb[key].as_s2_entry() == s2.s2map[sk]
    } by {
        assert(s1.tlb.contains_key(key));
    }
}

pub proof fn lemma_tlb_fill_preserves_wf(
    s1: HwView,
    s2: HwView,
    cpu: CpuId,
    vm: VmId,
    gpa: GuestPage,
)
    requires
        s1.wf(),
        HwView::tlb_fill_step(s1, s2, cpu, vm, gpa),
    ensures
        s2.wf(),
{
    // `tlb` only grows; the new entry is read from `s1.s2map[skey]`, so it agrees.
    let tkey = TlbKey::new(cpu, vm, gpa);
    let skey = VmPageKey::new(vm, gpa);
    assert forall|key: TlbKey| #[trigger] s2.tlb.contains_key(key) implies {
        let sk = VmPageKey::new(key.vm, key.gpa);
        &&& s2.s2map.contains_key(sk)
        &&& s2.tlb[key].as_s2_entry() == s2.s2map[sk]
    } by {
        if key == tkey {
            assert(s2.tlb[tkey].as_s2_entry() == s1.s2map[skey]);
        } else {
            assert(s1.tlb.contains_key(key));
        }
    }
}

/// The atomic break-before-make unmap preserves `tlb_safe`: a surviving cached key
/// is not `(vm, gpa)` (those were flushed), so its s2-key ≠ `skey` is untouched by
/// the `s2map` removal and the agreement carries.  (Used by the `MachineState`
/// refinement, where `tlb_safe` is the whole hardware coherence obligation.)
pub proof fn lemma_unmap_invalidate_preserves_tlb_safe(
    hw1: HwView,
    hw2: HwView,
    vm: VmId,
    gpa: GuestPage,
)
    requires
        hw1.tlb_safe(),
        HwView::unmap_invalidate_step(hw1, hw2, vm, gpa),
    ensures
        hw2.tlb_safe(),
{
    let skey = VmPageKey::new(vm, gpa);
    let targets = Set::new(|key: TlbKey| key.vm == vm && key.gpa == gpa);
    assert(hw2.s2map == hw1.s2map.remove(skey));
    assert(hw2.tlb =~= hw1.tlb.remove_keys(targets));
    assert forall|key: TlbKey| #[trigger] hw2.tlb.contains_key(key) implies {
        let sk = VmPageKey::new(key.vm, key.gpa);
        &&& hw2.s2map.contains_key(sk)
        &&& hw2.tlb[key].as_s2_entry() == hw2.s2map[sk]
    } by {
        let sk = VmPageKey::new(key.vm, key.gpa);
        // `remove_keys` is a `Map::new`; name the term to characterize `hw2.tlb`'s key.
        assert(hw1.tlb.remove_keys(targets).contains_key(key));
        assert(sk != skey);
        assert(hw1.s2map.contains_key(sk) && hw1.tlb[key].as_s2_entry() == hw1.s2map[sk]);
        assert(hw1.s2map.remove(skey).contains_key(sk));
    }
}

/// The map-side `DSB` preserves `tlb_safe`: `tlb` is unchanged and `s2map` only
/// grows by the fresh `skey` (which, being unreachable, has no cached entry).
pub proof fn lemma_map_preserves_tlb_safe(
    hw1: HwView,
    hw2: HwView,
    vm: VmId,
    gpa: GuestPage,
    entry: S2Entry,
)
    requires
        hw1.tlb_safe(),
        HwView::map_step(hw1, hw2, vm, gpa, entry),
    ensures
        hw2.tlb_safe(),
{
    let skey = VmPageKey::new(vm, gpa);
    assert forall|key: TlbKey| #[trigger] hw2.tlb.contains_key(key) implies {
        let sk = VmPageKey::new(key.vm, key.gpa);
        &&& hw2.s2map.contains_key(sk)
        &&& hw2.tlb[key].as_s2_entry() == hw2.s2map[sk]
    } by {
        let sk = VmPageKey::new(key.vm, key.gpa);
        assert(hw1.tlb.contains_key(key));
        assert(hw1.s2map.contains_key(sk) && hw1.tlb[key].as_s2_entry() == hw1.s2map[sk]);
        assert(sk != skey);
        assert(hw2.s2map == hw1.s2map.insert(skey, entry));
    }
}

pub proof fn lemma_unmap_invalidate_preserves_wf(s1: HwView, s2: HwView, vm: VmId, gpa: GuestPage)
    requires
        s1.wf(),
        HwView::unmap_invalidate_step(s1, s2, vm, gpa),
    ensures
        s2.wf(),
{
    lemma_unmap_invalidate_preserves_tlb_safe(s1, s2, vm, gpa);
}

pub proof fn lemma_map_preserves_wf(
    s1: HwView,
    s2: HwView,
    vm: VmId,
    gpa: GuestPage,
    entry: S2Entry,
)
    requires
        s1.wf(),
        HwView::map_step(s1, s2, vm, gpa, entry),
    ensures
        s2.wf(),
{
    lemma_map_preserves_tlb_safe(s1, s2, vm, gpa, entry);
}

pub proof fn lemma_context_switch_preserves_wf(s1: HwView, s2: HwView, cpu: CpuId, vm: VmId)
    requires
        s1.wf(),
        HwView::context_switch_step(s1, s2, cpu, vm),
    ensures
        s2.wf(),
{
    lemma_tlb_safe_unchanged(s1, s2);
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
    // `tlb` and `s2map` are unchanged.
    lemma_tlb_safe_unchanged(s1, s2);
}

} // verus!
