use vstd::prelude::*;

use super::hardware::HardwareRefinement;
use super::software::SoftwareRefinement;
use super::view::state_s2_map;
use crate::hardware::spec::MmuSpec;
use crate::hv_mem::spec::budget::BudgetSpec;
use crate::machine::convert::flatten_s2map;
use crate::machine::hardware::proof::{
    lemma_map_preserves_tlb_safe, lemma_unmap_invalidate_preserves_tlb_safe,
};
use crate::machine::hardware::HardwareView;
use crate::machine::machine::MachineState;
use crate::machine::software::proof::{
    lemma_add_vm_step_preserves_wf, lemma_assign_page_step_preserves_wf,
    lemma_map_step_preserves_wf, lemma_reclaim_page_step_preserves_wf,
    lemma_remove_vm_step_preserves_wf, lemma_share_page_step_preserves_wf,
    lemma_unmap_step_preserves_wf, lemma_unshare_page_step_preserves_wf,
};
use crate::machine::software::Region;
use crate::machine::software::SoftwareView;
use crate::machine::types::*;

verus! {

// ---------------------------------------------------------------------------
// Refinement: (SW step + HW step) ⟹ machine step
//
// Each `refine_*` lemma shows that composing the matching software and
// hardware sub-steps produces the corresponding high-level machine step.
//
// Decomposition of `MachineState::wf`: the ownership/sharing/translation clauses
// are exactly `SoftwareView::wf` (the `lemma_sw_machine_wf_equiv` bridge below), so a
// refinement only has to additionally re-establish the two cross-cutting clauses
// — `execution_wf` and `tlb_safe`.  SW steps inherit their three clauses from the
// SoftwareView `wf`-preservation proofs via the bridge.
// ---------------------------------------------------------------------------
/// Bridge: the assembled machine state's SW-side `wf` clauses *are* the software
/// view's, because `assemble` copies the SW fields verbatim and both views define
/// the predicates identically.  Lets each `refine_*` delegate the
/// ownership/sharing/translation obligations to the SoftwareView `wf` proofs.
pub proof fn lemma_sw_machine_wf_equiv(sw: SoftwareView, hw: HardwareView)
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
    assert forall|vm: VmId, page: PhysPage| #[trigger]
        m.owned_or_shared(vm, page) == sw.owned_or_shared(vm, page) by {
        assert(m.shared_with(vm, page) == sw.shared_with(vm, page));
    }
}

// ---------------------------------------------------------------------------
// Sync bridge: synced views ⟹ a well-formed machine state.
// ---------------------------------------------------------------------------
/// **The point-4 payoff.** A software view and a hardware view that are each
/// internally well-formed and *synced* — the hardware-reachable map equals the
/// software-maintained one (`hw.s2map == sw.s2_map`) — assemble into a `wf`
/// `MachineState`.
///
/// This is where the forced lock invariant pays off: the implementation drives the
/// `MmuSpec`/`BudgetSpec` tokens so that their reachable/maintained maps agree
/// (sync), and `tlb_safe` rides the `MmuSpec` invariant; this lemma turns that into
/// the full machine `wf` on which the isolation theorems rest.  The scheduler
/// hypothesis (every running vm is live) is the only `wf` clause spanning neither
/// view alone.
pub proof fn lemma_synced_views_wf(sw: SoftwareView, hw: HardwareView)
    requires
        sw.wf(),
        hw.wf(),
        hw.s2map == sw.s2_map,
        forall|cpu: CpuId| #[trigger]
            hw.active_vm.contains_key(cpu) ==> sw.all_vms.contains(hw.active_vm[cpu]),
    ensures
        MachineState::assemble(sw, hw).wf(),
{
    let m = MachineState::assemble(sw, hw);
    // ownership / sharing / translation clauses from the SW view.
    lemma_sw_machine_wf_equiv(sw, hw);
    // execution_wf and sync from the field copies.
    assert(m.execution_wf());
    assert(m.sync());
    // tlb_safe: identical to `hw.tlb_safe()` (both over `hw.s2map` and `hw.tlb`).
    assert(m.tlb_safe()) by {
        assert forall|k: TlbKey| #[trigger] m.tlb.contains_key(k) implies {
            let sk = VmPageKey::new(k.vm, k.gpa);
            &&& m.hw_s2map.contains_key(sk)
            &&& m.tlb[k].as_s2_entry() == m.hw_s2map[sk]
        } by {
            assert(hw.tlb.contains_key(k));
        }
    }
    assert(m.wf());
}

// ------------------------------------------------------------------
// Stage-2 mapping management
// ------------------------------------------------------------------
/// A SW map step composed with the atomic hardware [`map_step`](HardwareView::map_step)
/// (the map-side `DSB ISH` that makes the fresh PTE walker-reachable) refines the
/// machine-level `hv_map_step`.
///
/// Break-before-make on the map side needs no `TLBI`: `map_step` requires the page
/// currently unreachable, so by `tlb_safe` it has no stale cached entry, and the
/// synchronous flush in `hv_map_step` is therefore vacuous.
pub proof fn refine_hv_map(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw1: HardwareView,
    hw2: HardwareView,
    vm: VmId,
    gpa: GuestPage,
    entry: S2Entry,
)
    requires
        SoftwareView::map_step(sw1, sw2, vm, gpa, entry),
        HardwareView::map_step(hw1, hw2, vm, gpa, entry),
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

    // SW side: wf + the `s2_map` insert.
    lemma_sw_machine_wf_equiv(sw1, hw1);
    assert(sw1.wf());
    lemma_map_step_preserves_wf(sw1, sw2, vm, gpa, entry);
    lemma_sw_machine_wf_equiv(sw2, hw2);

    // Field deltas: `s2_map` (SW) and `hw_s2map` (HW) both grow by `key`; the rest fixed.
    assert(s2.s2_map == s1.s2_map.insert(key, entry));
    assert(s2.hw_s2map == s1.hw_s2map.insert(key, entry));
    assert(s2.all_vms == s1.all_vms);
    assert(s2.vm_owned == s1.vm_owned);
    assert(s2.hypervisor_owned == s1.hypervisor_owned);
    assert(s2.shared_pages == s1.shared_pages);
    assert(s2.active_vm == s1.active_vm);
    assert(s2.memory == s1.memory);

    // The flush is vacuous: the page was unreachable (`map_step` freshness), so by
    // `tlb_safe` no cached entry names `(vm, gpa)`, hence `remove_keys(targets)` is id.
    assert(s1.tlb_safe());
    assert(!hw1.s2map.contains_key(key));
    assert forall|k: TlbKey| s1.tlb.contains_key(k) implies !targets.contains(k) by {
        if targets.contains(k) {
            assert(s1.hw_s2map.contains_key(VmPageKey::new(k.vm, k.gpa)));
        }
    }
    assert(s2.tlb =~= s1.tlb.remove_keys(targets));

    // sync(s2): both maps grew by the same `key => entry` from a synced `s1`.
    assert(s1.sync());
    assert(s2.hw_s2map =~= s2.s2_map);

    // tlb_safe(s2): MachineState `tlb_safe` is exactly the HW one over `hw_s2map`.
    lemma_map_preserves_tlb_safe(hw1, hw2, vm, gpa, entry);
    assert(s2.tlb_safe()) by {
        assert forall|k: TlbKey| #[trigger] s2.tlb.contains_key(k) implies {
            let sk = VmPageKey::new(k.vm, k.gpa);
            &&& s2.hw_s2map.contains_key(sk)
            &&& s2.tlb[k].as_s2_entry() == s2.hw_s2map[sk]
        } by {
            assert(hw2.tlb.contains_key(k));
        }
    }
    assert(s2.execution_wf());
    assert(s2.wf());
}

/// A SW unmap step composed with the atomic hardware
/// [`unmap_invalidate_step`](HardwareView::unmap_invalidate_step) (the `DSB ISH` +
/// `TLBI IPAS2E1IS` that drops the page from the reachable map and flushes its
/// cached entries together) refines `hv_unmap_step`.
pub proof fn refine_hv_unmap(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw1: HardwareView,
    hw2: HardwareView,
    vm: VmId,
    gpa: GuestPage,
)
    requires
        SoftwareView::unmap_step(sw1, sw2, vm, gpa),
        HardwareView::unmap_invalidate_step(hw1, hw2, vm, gpa),
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

    // SW side: wf + the `s2_map` remove.
    lemma_sw_machine_wf_equiv(sw1, hw1);
    assert(sw1.wf());
    lemma_unmap_step_preserves_wf(sw1, sw2, vm, gpa);
    lemma_sw_machine_wf_equiv(sw2, hw2);

    // Field deltas: `s2_map` (SW) and `hw_s2map` (HW) both lose `key`.
    assert(s2.s2_map == s1.s2_map.remove(key));
    assert(s2.hw_s2map == s1.hw_s2map.remove(key));
    assert(s2.all_vms == s1.all_vms);
    assert(s2.vm_owned == s1.vm_owned);
    assert(s2.hypervisor_owned == s1.hypervisor_owned);
    assert(s2.shared_pages == s1.shared_pages);
    assert(s2.active_vm == s1.active_vm);
    assert(s2.memory == s1.memory);

    // The atomic step's unguarded flush set coincides with `invalidation_targets`.
    assert(s2.tlb =~= s1.tlb.remove_keys(targets));

    // sync(s2): both maps lost the same `key` from a synced `s1`.
    assert(s1.sync());
    assert(s2.hw_s2map =~= s2.s2_map);

    // tlb_safe(s2) via the HW lemma (MachineState `tlb_safe` == HW one over `hw_s2map`).
    lemma_unmap_invalidate_preserves_tlb_safe(hw1, hw2, vm, gpa);
    assert(s2.tlb_safe()) by {
        assert forall|k: TlbKey| #[trigger] s2.tlb.contains_key(k) implies {
            let sk = VmPageKey::new(k.vm, k.gpa);
            &&& s2.hw_s2map.contains_key(sk)
            &&& s2.tlb[k].as_s2_entry() == s2.hw_s2map[sk]
        } by {
            assert(hw2.tlb.contains_key(k));
        }
    }
    assert(s2.execution_wf());
    assert(s2.wf());
}

// ------------------------------------------------------------------
// Ownership management (pure SW — HW state unchanged)
// ------------------------------------------------------------------
pub proof fn refine_hv_assign_page(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw: HardwareView,
    vm: VmId,
    page: PhysPage,
)
    requires
        SoftwareView::assign_page_step(sw1, sw2, vm, page),
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

pub proof fn refine_hv_reclaim_page(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw: HardwareView,
    vm: VmId,
    page: PhysPage,
)
    requires
        SoftwareView::reclaim_page_step(sw1, sw2, vm, page),
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
    // The machine-level `page_is_quiescent` supplies the SoftwareView reclaim lemma's
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
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw: HardwareView,
    left: VmId,
    right: VmId,
    page: PhysPage,
)
    requires
        SoftwareView::share_page_step(sw1, sw2, left, right, page),
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
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw: HardwareView,
    left: VmId,
    right: VmId,
    page: PhysPage,
)
    requires
        SoftwareView::unshare_page_step(sw1, sw2, left, right, page),
        MachineState::assemble(sw1, hw).wf(),
        // No-dangling guard (cf. `hv_unshare_page_step`): an endpoint that maps
        // `page` must own it, so dropping the share strands no translation.
        forall|k: VmPageKey| #[trigger]
            MachineState::assemble(sw1, hw).s2_map.contains_key(k) && (k.vm == left || k.vm
                == right) && MachineState::assemble(sw1, hw).s2_map[k].page == page
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
    assert forall|k: VmPageKey| #[trigger]
        sw1.s2_map.contains_key(k) && (k.vm == left || k.vm == right) && sw1.s2_map[k].page
            == page implies sw1.vm_owned[k.vm].contains(page) by {
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
pub proof fn refine_hv_context_switch(
    sw: SoftwareView,
    hw1: HardwareView,
    hw2: HardwareView,
    cpu: CpuId,
    vm: VmId,
)
    requires
        HardwareView::context_switch_step(hw1, hw2, cpu, vm),
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

// ------------------------------------------------------------------
// VM lifecycle (pure SW — HW state unchanged)
// ------------------------------------------------------------------
/// Registering a fresh VM refines `hv_add_vm_step`.  The new VM owns and maps
/// nothing, so the only machine-only clause to re-establish is `execution_wf`
/// (which survives a growing `all_vms`); the SW clauses come via the bridge and
/// `tlb_safe` carries over unchanged.
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
    assert(sw1.wf());
    lemma_add_vm_step_preserves_wf(sw1, sw2, vm);
    lemma_sw_machine_wf_equiv(sw2, hw);
    // execution_wf: `active_vm` is unchanged and `all_vms` only grows (insert `vm`),
    // so every scheduled VM is still present.
    assert(s2.active_vm == s1.active_vm);
    assert(s2.all_vms == s1.all_vms.insert(vm));
    assert forall|c: CpuId| #[trigger] s2.active_vm.contains_key(c) implies s2.all_vms.contains(
        s2.active_vm[c],
    ) by {
        assert(s1.active_vm.contains_key(c) && s1.all_vms.contains(s1.active_vm[c]));
    }
    // tlb_safe: `tlb` and `s2_map` are unchanged.
    assert(s2.tlb == s1.tlb);
    assert(s2.s2_map == s1.s2_map);
    assert(s1.tlb_safe());
    assert(s2.wf());
}

/// Deregistering an empty VM refines `hv_remove_vm_step`.  Beyond the SW
/// `remove_vm_enabled` condition, the machine step also requires two HW-side
/// guards — `vm` has no cached TLB entry and runs on no CPU — so that dropping it
/// strands no hardware reference; both are taken as hypotheses (cf. the
/// no-dangling guard of `refine_hv_unshare_page`).
pub proof fn refine_hv_remove_vm(sw1: SoftwareView, sw2: SoftwareView, hw: HardwareView, vm: VmId)
    requires
        SoftwareView::remove_vm_enabled(sw1, vm),
        SoftwareView::remove_vm_step(sw1, sw2, vm),
        MachineState::assemble(sw1, hw).wf(),
        forall|k: TlbKey| #[trigger]
            MachineState::assemble(sw1, hw).tlb.contains_key(k) ==> k.vm != vm,
        forall|cpu: CpuId| #[trigger]
            MachineState::assemble(sw1, hw).active_vm.contains_key(cpu) ==> MachineState::assemble(
                sw1,
                hw,
            ).active_vm[cpu] != vm,
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
    assert(sw1.wf());
    lemma_remove_vm_step_preserves_wf(sw1, sw2, vm);
    lemma_sw_machine_wf_equiv(sw2, hw);
    // execution_wf: `active_vm` unchanged; `all_vms` shrinks by `vm`, and the HW
    // guard says no CPU ran `vm`, so every scheduled VM remains in `all_vms`.
    assert(s2.active_vm == s1.active_vm);
    assert(s2.all_vms == s1.all_vms.remove(vm));
    assert forall|c: CpuId| #[trigger] s2.active_vm.contains_key(c) implies s2.all_vms.contains(
        s2.active_vm[c],
    ) by {
        assert(s1.active_vm.contains_key(c) && s1.all_vms.contains(s1.active_vm[c]));
        assert(s1.active_vm[c] != vm);
    }
    // tlb_safe: `tlb` and `s2_map` are unchanged.
    assert(s2.tlb == s1.tlb);
    assert(s2.s2_map == s1.s2_map);
    assert(s1.tlb_safe());
    assert(s2.wf());
}

// ---------------------------------------------------------------------------
// SoftwareView region-trace helpers (partial states, prefixes, per-page edges)
//
// These operate purely on `SoftwareView` but live here, at the trace proof site, so the
// machine-trace lemmas below consume them directly.  (Relocated from
// `software::proof`, which no longer references them.)
// ---------------------------------------------------------------------------
// ───────────────────── partial-insert state & prefixes ──────────────────────
// `insert_partial(s1, region, a, m)` is `s1` with the first `a` region pages
// assigned to `region.vm` and the first `m` region entries mapped (`m <= a`).
// The trace's state at index `j` is `insert_partial(.., (j+1)/2, j/2)`.
/// First `k` physical pages of the region.
pub open spec fn phys_prefix(region: Region, k: nat) -> Set<PhysPage> {
    Set::new(|p: PhysPage| region.phys_base <= p.0 < region.phys_base + k)
}

/// First `k` stage-2 entries of the region (one per guest page).
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

/// `s1` with the first `a` region pages assigned and the first `m` mapped.
pub open spec fn insert_partial(s1: SoftwareView, region: Region, a: nat, m: nat) -> SoftwareView {
    SoftwareView {
        all_vms: s1.all_vms,
        hypervisor_owned: s1.hypervisor_owned.difference(phys_prefix(region, a)),
        vm_owned: s1.vm_owned.insert(
            region.vm,
            s1.vm_owned[region.vm].union(phys_prefix(region, a)),
        ),
        shared_pages: s1.shared_pages,
        s2_map: s1.s2_map.union_prefer_right(entry_prefix(region, m)),
        iommu_s2_map: s1.iommu_s2_map,
        iommu_owned: s1.iommu_owned,
        iommu_shared: s1.iommu_shared,
    }
}

// ── reusable prefix-successor & index-arithmetic helpers ─────────────────────
/// `phys_prefix` gains exactly `phys_page(k)` when extended by one.
pub proof fn lemma_phys_prefix_succ(region: Region, k: nat)
    ensures
        !phys_prefix(region, k).contains(region.phys_page(k)),
        phys_prefix(region, (k + 1) as nat) == phys_prefix(region, k).insert(region.phys_page(k)),
{
    assert(phys_prefix(region, (k + 1) as nat) =~= phys_prefix(region, k).insert(
        region.phys_page(k),
    ));
}

/// `entry_prefix` gains exactly the entry for region page `k` when extended by one.
pub proof fn lemma_entry_prefix_succ(region: Region, k: nat)
    ensures
        !entry_prefix(region, k).dom().contains(VmPageKey::new(region.vm, region.guest_page(k))),
        entry_prefix(region, (k + 1) as nat) == entry_prefix(region, k).insert(
            VmPageKey::new(region.vm, region.guest_page(k)),
            S2Entry { page: region.phys_page(k), access: region.access, generation: 0 },
        ),
{
    let key = VmPageKey::new(region.vm, region.guest_page(k));
    let entry = S2Entry { page: region.phys_page(k), access: region.access, generation: 0 };
    assert(entry_prefix(region, (k + 1) as nat) =~= entry_prefix(region, k).insert(key, entry));
}

/// Index arithmetic shared by every trace edge/`wf` loop: `i = j/2` splits even/odd.
pub proof fn lemma_half_index(j: int)
    requires
        0 <= j,
    ensures
        j % 2 == 0 ==> j == 2 * (j / 2) && (j + 1) / 2 == j / 2 && (j + 2) / 2 == j / 2 + 1,
        j % 2 == 1 ==> j == 2 * (j / 2) + 1 && (j + 1) / 2 == j / 2 + 1 && (j + 2) / 2 == j / 2 + 1,
        j / 2 <= (j + 1) / 2,
{
    assert(j == 2 * (j / 2) + j % 2 && 0 <= j % 2 < 2 && j / 2 <= (j + 1) / 2 && (j + 2) / 2 == j
        / 2 + 1 && (j + 1) / 2 == j / 2 + j % 2) by (nonlinear_arith)
        requires
            0 <= j,
    ;
}

/// A prefix page is free in `s1`: held by the hypervisor and owned by no VM.
proof fn lemma_prefix_pages_free(s1: SoftwareView, region: Region, a: nat, p: PhysPage)
    requires
        s1.wf(),
        SoftwareView::insert_region_enabled(s1, region),
        a <= region.count,
        phys_prefix(region, a).contains(p),
    ensures
        region.pages().contains(p),
        s1.hypervisor_owned.contains(p),
        forall|w: VmId| #[trigger] s1.all_vms.contains(w) ==> !s1.vm_owned[w].contains(p),
{
    assert(region.pages().contains(p));  // [phys_base, phys_base+a) ⊆ [phys_base, phys_base+count)
    assert(s1.hypervisor_owned.contains(p));  // enabled: region pages are free
    assert forall|w: VmId| #[trigger] s1.all_vms.contains(w) implies !s1.vm_owned[w].contains(
        p,
    ) by {
        // ownership_wf: a VM-owned page is not hypervisor-owned (contrapositive).
    }
}

/// Every partial-insert state is `wf` (`m <= a <= count`).
pub proof fn lemma_insert_partial_wf(s1: SoftwareView, region: Region, a: nat, m: nat)
    requires
        s1.wf(),
        SoftwareView::insert_region_enabled(s1, region),
        m <= a,
        a <= region.count,
    ensures
        insert_partial(s1, region, a, m).wf(),
{
    let vm = region.vm;
    let sp = insert_partial(s1, region, a, m);
    let pp = phys_prefix(region, a);
    let ep = entry_prefix(region, m);
    // A prefix entry targets a prefix page (its index `< m <= a`).
    assert forall|k: VmPageKey| #[trigger] ep.contains_key(k) implies pp.contains(ep[k].page) by {}
    // ownership_wf
    assert(sp.vm_owned.dom() =~= sp.all_vms);
    assert forall|x: VmId, y: VmId| #[trigger]
        sp.all_vms.contains(x) && #[trigger] sp.all_vms.contains(y) && x != y implies (forall|
        p: PhysPage,
    | #[trigger]
        sp.vm_owned[x].contains(p) ==> !sp.vm_owned[y].contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            sp.vm_owned[x].contains(p) implies !sp.vm_owned[y].contains(p) by {
            if x == vm {
                if !pp.contains(p) {
                    assert(s1.vm_owned[vm].contains(p));
                } else {
                    lemma_prefix_pages_free(s1, region, a, p);
                }
            } else if y == vm {
                assert(s1.vm_owned[x].contains(p));
                if pp.contains(p) {
                    lemma_prefix_pages_free(s1, region, a, p);
                }
            }
        }
    }
    assert forall|w: VmId| #[trigger] sp.all_vms.contains(w) implies (forall|p: PhysPage|
     #[trigger]
        sp.vm_owned[w].contains(p) ==> !sp.hypervisor_owned.contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            sp.vm_owned[w].contains(p) implies !sp.hypervisor_owned.contains(p) by {
            if w == vm && pp.contains(p) {
                // p ∈ prefix ⟹ removed from hypervisor_owned by the difference.
            } else {
                assert(s1.vm_owned[w].contains(p));
            }
        }
    }
    // sharing_wf: shared_pages / all_vms unchanged.
    assert forall|e: SharedPage| #[trigger] sp.shared_pages.contains(e) implies (e.left != e.right
        && sp.all_vms.contains(e.left) && sp.all_vms.contains(e.right) && sp.shared_pages.contains(
        e.reverse(),
    )) by {
        assert(s1.shared_pages.contains(e));
    }
    // translation_wf
    assert forall|k: VmPageKey| #[trigger] sp.s2_map.contains_key(k) implies (sp.all_vms.contains(
        k.vm,
    ) && sp.owned_or_shared(k.vm, sp.s2_map[k].page)) by {
        if ep.contains_key(k) {
            // new entry: target ∈ prefix ⊆ vm's pages.
            assert(pp.contains(ep[k].page));
        } else {
            // surviving entry: still owned-or-shared (ownership only grew).
            assert(s1.s2_map.contains_key(k));
            assert(s1.owned_or_shared(k.vm, s1.s2_map[k].page));
            if s1.shared_with(k.vm, s1.s2_map[k].page) {
                let w = choose|w: SharedPage| #[trigger]
                    s1.shared_pages.contains(w) && w.page == s1.s2_map[k].page && (w.left == k.vm
                        || w.right == k.vm);
                assert(sp.shared_pages.contains(w));
            }
        }
    }
    assert(sp.wf());
}

/// Even edge `2*i`: assigning region page `i` advances `(i, i) → (i+1, i)`.
pub proof fn lemma_insert_assign_edge(s1: SoftwareView, region: Region, i: nat)
    requires
        s1.wf(),
        SoftwareView::insert_region_enabled(s1, region),
        i < region.count,
    ensures
        SoftwareView::assign_page_step(
            insert_partial(s1, region, i, i),
            insert_partial(s1, region, (i + 1) as nat, i),
            region.vm,
            region.phys_page(i),
        ),
{
    let vm = region.vm;
    let page = region.phys_page(i);  // .0 == phys_base + i
    let from = insert_partial(s1, region, i, i);
    let pp_i = phys_prefix(region, i);
    let pp_i1 = phys_prefix(region, (i + 1) as nat);
    lemma_phys_prefix_succ(region, i);  // pp_i1 == pp_i.insert(page); page ∉ pp_i
    // `page` is free in `s1` and not in the first-`i` prefix, so it is held by `from`.
    assert(region.pages().contains(page));
    assert(s1.hypervisor_owned.contains(page));
    // hypervisor_owned: difference(prefix(i+1)) == difference(prefix(i)).remove(page)
    assert(s1.hypervisor_owned.difference(pp_i1) =~= s1.hypervisor_owned.difference(pp_i).remove(
        page,
    ));
    // vm_owned: (s1[vm] ∪ prefix(i)).insert(page) == s1[vm] ∪ prefix(i+1)
    assert(s1.vm_owned[vm].union(pp_i).insert(page) =~= s1.vm_owned[vm].union(pp_i1));
    assert(from.vm_owned.insert(vm, from.vm_owned[vm].insert(page)) =~= insert_partial(
        s1,
        region,
        (i + 1) as nat,
        i,
    ).vm_owned);
}

/// Odd edge `2*i+1`: mapping region entry `i` advances `(i+1, i) → (i+1, i+1)`.
pub proof fn lemma_insert_map_edge(s1: SoftwareView, region: Region, i: nat)
    requires
        s1.wf(),
        SoftwareView::insert_region_enabled(s1, region),
        i < region.count,
    ensures
        SoftwareView::map_step(
            insert_partial(s1, region, (i + 1) as nat, i),
            insert_partial(s1, region, (i + 1) as nat, (i + 1) as nat),
            region.vm,
            region.guest_page(i),
            S2Entry { page: region.phys_page(i), access: region.access, generation: 0 },
        ),
{
    let vm = region.vm;
    let from = insert_partial(s1, region, (i + 1) as nat, i);
    let key = VmPageKey::new(vm, region.guest_page(i));
    let entry = S2Entry { page: region.phys_page(i), access: region.access, generation: 0 };
    let ep_i = entry_prefix(region, i);
    let ep_i1 = entry_prefix(region, (i + 1) as nat);
    lemma_entry_prefix_succ(region, i);  // ep_i1 == ep_i.insert(key, entry); key ∉ ep_i
    // owned_or_shared(vm, phys_page(i)): it is in `from`'s prefix of vm-owned pages.
    assert(phys_prefix(region, (i + 1) as nat).contains(region.phys_page(i)));
    // s2_map: union(entry_prefix(i+1)) == union(entry_prefix(i)).insert(key, entry)
    assert(s1.s2_map.union_prefer_right(ep_i1) =~= s1.s2_map.union_prefer_right(ep_i).insert(
        key,
        entry,
    )) by {
        assert(!s1.s2_map.contains_key(key)) by {
            assert(region.entries().contains_key(key));
        }
    }
}

// ───────────────────── partial-remove state & prefixes ──────────────────────
// `remove_partial(s1, region, u, r)` is `s1` with the first `u` region entries
// unmapped and the first `r` region pages reclaimed (`r <= u`).  The trace's
// state at index `j` is `remove_partial(.., (j+1)/2, j/2)`.
/// `s1` with the first `u` region entries unmapped and the first `r` reclaimed.
pub open spec fn remove_partial(s1: SoftwareView, region: Region, u: nat, r: nat) -> SoftwareView {
    SoftwareView {
        all_vms: s1.all_vms,
        hypervisor_owned: s1.hypervisor_owned.union(phys_prefix(region, r)),
        vm_owned: s1.vm_owned.insert(
            region.vm,
            s1.vm_owned[region.vm].difference(phys_prefix(region, r)),
        ),
        shared_pages: s1.shared_pages,
        s2_map: s1.s2_map.remove_keys(entry_prefix(region, u).dom()),
        iommu_s2_map: s1.iommu_s2_map,
        iommu_owned: s1.iommu_owned,
        iommu_shared: s1.iommu_shared,
    }
}

/// A prefix page is owned by `region.vm` alone (`r <= count`).
proof fn lemma_remove_prefix_owned(s1: SoftwareView, region: Region, r: nat, p: PhysPage)
    requires
        s1.wf(),
        SoftwareView::remove_region_enabled(s1, region),
        r <= region.count,
        phys_prefix(region, r).contains(p),
    ensures
        region.pages().contains(p),
        s1.vm_owned[region.vm].contains(p),
        forall|w: VmId| #[trigger]
            s1.all_vms.contains(w) && w != region.vm ==> !s1.vm_owned[w].contains(p),
{
    assert(region.pages().contains(p));  // [phys_base, phys_base+r) ⊆ [phys_base, phys_base+count)
    assert(s1.vm_owned[region.vm].contains(p));  // enabled: region pages owned by vm
    assert forall|w: VmId| #[trigger]
        s1.all_vms.contains(w) && w != region.vm implies !s1.vm_owned[w].contains(p) by {
        // ownership_wf pairwise disjointness vs. `vm` (who owns `p`).
    }
}

/// A surviving stage-2 entry targets no reclaimed page (`r <= u <= count`).
pub proof fn lemma_remove_survivor_unreclaimed(
    s1: SoftwareView,
    region: Region,
    u: nat,
    r: nat,
    k: VmPageKey,
)
    requires
        s1.wf(),
        SoftwareView::remove_region_enabled(s1, region),
        r <= u,
        u <= region.count,
        s1.s2_map.contains_key(k),
        !entry_prefix(region, u).dom().contains(k),
    ensures
        !phys_prefix(region, r).contains(s1.s2_map[k].page),
{
    let p = s1.s2_map[k].page;
    if region.entries().contains_key(k) {
        // A region entry not yet unmapped: its guest index is `>= u >= r`, so its
        // target physical page lies beyond the first-`r` prefix.
        assert(s1.s2_map[k] == region.entries()[k]);  // enabled
        assert(k.vm == region.vm && region.gpa_base <= k.gpa.0 < region.gpa_base + region.count);
        assert(k.gpa.0 >= region.gpa_base + u);  // else k ∈ entry_prefix(u).dom()
        assert(p.0 == region.phys_base + k.gpa.0 - region.gpa_base);
    } else {
        // A non-region mapping: no-dangling precondition keeps it off region pages.
        assert(!region.pages().contains(p));
    }
}

/// Every partial-remove state is `wf` (`r <= u <= count`).
pub proof fn lemma_remove_partial_wf(s1: SoftwareView, region: Region, u: nat, r: nat)
    requires
        s1.wf(),
        SoftwareView::remove_region_enabled(s1, region),
        r <= u,
        u <= region.count,
    ensures
        remove_partial(s1, region, u, r).wf(),
{
    let vm = region.vm;
    let sp = remove_partial(s1, region, u, r);
    let pp = phys_prefix(region, r);
    // ownership_wf
    assert(sp.vm_owned.dom() =~= sp.all_vms);
    assert forall|x: VmId, y: VmId| #[trigger]
        sp.all_vms.contains(x) && #[trigger] sp.all_vms.contains(y) && x != y implies (forall|
        p: PhysPage,
    | #[trigger]
        sp.vm_owned[x].contains(p) ==> !sp.vm_owned[y].contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            sp.vm_owned[x].contains(p) implies !sp.vm_owned[y].contains(p) by {
            assert(s1.vm_owned[x].contains(p));  // sp[x] ⊆ s1[x]
        }
    }
    assert forall|w: VmId| #[trigger] sp.all_vms.contains(w) implies (forall|p: PhysPage|
     #[trigger]
        sp.vm_owned[w].contains(p) ==> !sp.hypervisor_owned.contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            sp.vm_owned[w].contains(p) implies !sp.hypervisor_owned.contains(p) by {
            assert(s1.vm_owned[w].contains(p));  // sp[w] ⊆ s1[w], so p ∉ s1.hypervisor_owned
            if pp.contains(p) {
                // p is reclaimed: owned by `vm` alone in s1, so `w == vm`; but sp[vm]
                // dropped the prefix, contradicting `sp.vm_owned[w].contains(p)`.
                lemma_remove_prefix_owned(s1, region, r, p);
            }
        }
    }
    // sharing_wf: shared_pages / all_vms unchanged.
    assert forall|e: SharedPage| #[trigger] sp.shared_pages.contains(e) implies (e.left != e.right
        && sp.all_vms.contains(e.left) && sp.all_vms.contains(e.right) && sp.shared_pages.contains(
        e.reverse(),
    )) by {
        assert(s1.shared_pages.contains(e));
    }
    // translation_wf: a surviving key targets an unreclaimed page, so ownership/sharing
    // (which only shrank by the reclaimed prefix) still covers it.
    assert forall|k: VmPageKey| #[trigger] sp.s2_map.contains_key(k) implies (sp.all_vms.contains(
        k.vm,
    ) && sp.owned_or_shared(k.vm, sp.s2_map[k].page)) by {
        assert(s1.s2_map.contains_key(k) && !entry_prefix(region, u).dom().contains(k));
        lemma_remove_survivor_unreclaimed(s1, region, u, r, k);
        assert(s1.owned_or_shared(k.vm, s1.s2_map[k].page));
        if s1.shared_with(k.vm, s1.s2_map[k].page) {
            let w = choose|w: SharedPage| #[trigger]
                s1.shared_pages.contains(w) && w.page == s1.s2_map[k].page && (w.left == k.vm
                    || w.right == k.vm);
            assert(sp.shared_pages.contains(w));
        }
    }
    assert(sp.wf());
}

/// Even edge `2*i`: unmapping region entry `i` advances `(i, i) → (i+1, i)`.
pub proof fn lemma_remove_unmap_edge(s1: SoftwareView, region: Region, i: nat)
    requires
        s1.wf(),
        SoftwareView::remove_region_enabled(s1, region),
        i < region.count,
    ensures
        SoftwareView::unmap_step(
            remove_partial(s1, region, i, i),
            remove_partial(s1, region, (i + 1) as nat, i),
            region.vm,
            region.guest_page(i),
        ),
{
    let vm = region.vm;
    let from = remove_partial(s1, region, i, i);
    let key = VmPageKey::new(vm, region.guest_page(i));
    let d_i = entry_prefix(region, i).dom();
    let d_i1 = entry_prefix(region, (i + 1) as nat).dom();
    lemma_entry_prefix_succ(region, i);  // entry_prefix(i+1) == entry_prefix(i).insert(key, ·)
    // `key` is a region entry, present in `s1` and not yet unmapped, so it survives in `from`.
    assert(region.entries().contains_key(key));
    assert(s1.s2_map.contains_key(key));
    // s2_map: remove_keys(dom(i+1)) == remove_keys(dom(i)).remove(key)
    assert(d_i1 =~= d_i.insert(key));
    assert(s1.s2_map.remove_keys(d_i1) =~= s1.s2_map.remove_keys(d_i).remove(key));
}

/// Odd edge `2*i+1`: reclaiming region page `i` advances `(i+1, i) → (i+1, i+1)`.
pub proof fn lemma_remove_reclaim_edge(s1: SoftwareView, region: Region, i: nat)
    requires
        s1.wf(),
        SoftwareView::remove_region_enabled(s1, region),
        i < region.count,
    ensures
        SoftwareView::reclaim_page_step(
            remove_partial(s1, region, (i + 1) as nat, i),
            remove_partial(s1, region, (i + 1) as nat, (i + 1) as nat),
            region.vm,
            region.phys_page(i),
        ),
{
    let vm = region.vm;
    let page = region.phys_page(i);  // .0 == phys_base + i
    let from = remove_partial(s1, region, (i + 1) as nat, i);
    let pp_i = phys_prefix(region, i);
    let pp_i1 = phys_prefix(region, (i + 1) as nat);
    lemma_phys_prefix_succ(region, i);  // pp_i1 == pp_i.insert(page); page ∉ pp_i
    // `page` is owned by `vm` and not yet reclaimed, so `from` still has it.
    assert(region.pages().contains(page));
    assert(s1.vm_owned[vm].contains(page));  // enabled
    // hypervisor_owned: union(prefix(i+1)) == union(prefix(i)).insert(page)
    assert(s1.hypervisor_owned.union(pp_i1) =~= s1.hypervisor_owned.union(pp_i).insert(page));
    // vm_owned: (s1[vm].difference(prefix(i))).remove(page) == s1[vm].difference(prefix(i+1))
    assert(s1.vm_owned[vm].difference(pp_i).remove(page) =~= s1.vm_owned[vm].difference(pp_i1));
    assert(from.vm_owned.insert(vm, from.vm_owned[vm].remove(page)) =~= remove_partial(
        s1,
        region,
        (i + 1) as nat,
        (i + 1) as nat,
    ).vm_owned);
}

// ---------------------------------------------------------------------------
// Region → per-page MACHINE trace  (insert side)
//
// The SoftwareView trace helpers above realize a region step as a trace of atomic
// per-page SW steps.  Lifted through `assemble(·, hw)`, each SW edge becomes a
// `MachineState` hypervisor step, so an `insert_region` is realized as a trace of
// per-page `hv_assign_page` / `hv_map` steps — the bridge that lets the bulk
// operation inherit the per-page machine-level results.
//
// Insert is the clean case: every region guest page is *unmapped* in `sw1`
// (`insert_region_enabled`), so by `tlb_safe` no TLB entry names those gpas and
// `invalidation_targets` is empty at every map.  The TLB is therefore fixed (`hw`)
// across the whole insert trace.
// ---------------------------------------------------------------------------
/// `hw` with its reachable map forced to `sw.s2_map` — the hardware state at a
/// well-formed (synced) point.  Used to assemble trace states so that the `sync`
/// invariant holds at every partial: `hw_s2map` tracks the partial's `s2_map`.
pub open spec fn synced_hw(sw: SoftwareView, hw: HardwareView) -> HardwareView {
    HardwareView { s2map: sw.s2_map, ..hw }
}

/// At a synced point (`hw.s2map == sw.s2_map`) overriding the reachable map is a
/// no-op, so the synced assembly coincides with the plain one.
pub proof fn lemma_synced_hw_id(sw: SoftwareView, hw: HardwareView)
    requires
        hw.s2map == sw.s2_map,
    ensures
        MachineState::assemble(sw, synced_hw(sw, hw)) == MachineState::assemble(sw, hw),
{
    assert(MachineState::assemble(sw, synced_hw(sw, hw)) =~= MachineState::assemble(sw, hw));
}

/// Machine partial-insert state: the SW `insert_partial`, assembled with the synced
/// `hw` (reachable map tracks `s2_map`; TLB fixed at `hw.tlb`).
pub open spec fn insert_machine_partial(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    a: nat,
    m: nat,
) -> MachineState {
    let sp = insert_partial(sw1, region, a, m);
    MachineState::assemble(sp, synced_hw(sp, hw))
}

/// Each partial-insert state is `wf`.
pub proof fn lemma_insert_partial_machine_wf(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    a: nat,
    m: nat,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::insert_region_enabled(sw1, region),
        m <= a,
        a <= region.count,
    ensures
        insert_machine_partial(sw1, hw, region, a, m).wf(),
{
    let sp = insert_partial(sw1, region, a, m);
    let m1 = MachineState::assemble(sw1, hw);
    let m2 = MachineState::assemble(sp, synced_hw(sp, hw));
    // SW clauses via the bridge + the SoftwareView partial-`wf` proof.
    lemma_sw_machine_wf_equiv(sw1, hw);
    assert(sw1.wf());
    lemma_insert_partial_wf(sw1, region, a, m);
    lemma_sw_machine_wf_equiv(sp, synced_hw(sp, hw));
    // execution_wf: `active_vm` and `all_vms` are unchanged.
    assert(m2.all_vms == m1.all_vms);
    assert(m2.active_vm == m1.active_vm);
    assert(m1.execution_wf());
    assert(m2.execution_wf());
    // sync holds by construction (`synced_hw` forces `hw_s2map == s2_map`).
    assert(m2.hw_s2map == m2.s2_map);
    // tlb_safe (over `hw_s2map == s2_map`): `tlb == hw.tlb` unchanged; `s2_map` grew
    // only by fresh region entries (keys unmapped in `sw1`), so each cached key's
    // lookup keeps the value `m1.tlb_safe` provided.
    assert(m1.tlb_safe());
    assert(m1.sync());
    assert forall|k: TlbKey| #[trigger] m2.tlb.contains_key(k) implies {
        let sk = VmPageKey::new(k.vm, k.gpa);
        &&& m2.hw_s2map.contains_key(sk)
        &&& m2.tlb[k].as_s2_entry() == m2.hw_s2map[sk]
    } by {
        let sk = VmPageKey::new(k.vm, k.gpa);
        assert(m1.tlb.contains_key(k));
        assert(m1.hw_s2map.contains_key(sk) && m1.tlb[k].as_s2_entry() == m1.hw_s2map[sk]);
        assert(sw1.s2_map.contains_key(sk));
        assert(!entry_prefix(region, m).dom().contains(sk)) by {
            if entry_prefix(region, m).dom().contains(sk) {
                assert(region.entries().contains_key(sk));  // m <= count
                assert(!sw1.s2_map.contains_key(sk));  // enabled: region entries unmapped
            }
        }
        assert(m2.hw_s2map[sk] == sw1.s2_map[sk]);
    }
    assert(m2.wf());
}

/// Odd edge `2*i+1` at the machine level: mapping region entry `i` is an
/// `hv_map_step`.  The flush is vacuous (`invalidation_targets` empty), so the TLB
/// is unchanged.
pub proof fn lemma_insert_map_machine_edge(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    i: nat,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::insert_region_enabled(sw1, region),
        i < region.count,
    ensures
        MachineState::hv_map_step(
            insert_machine_partial(sw1, hw, region, (i + 1) as nat, i),
            insert_machine_partial(sw1, hw, region, (i + 1) as nat, (i + 1) as nat),
            region.vm,
            region.guest_page(i),
            S2Entry { page: region.phys_page(i), access: region.access, generation: 0 },
        ),
{
    let vm = region.vm;
    let gpa = region.guest_page(i);
    let entry = S2Entry { page: region.phys_page(i), access: region.access, generation: 0 };
    let from_sw = insert_partial(sw1, region, (i + 1) as nat, i);
    let to_sw = insert_partial(sw1, region, (i + 1) as nat, (i + 1) as nat);
    let hw1 = synced_hw(from_sw, hw);
    let hw2 = synced_hw(to_sw, hw);
    let key = VmPageKey::new(vm, gpa);
    lemma_sw_machine_wf_equiv(sw1, hw);
    assert(sw1.wf());
    // SW map step between the two partials (gives `to_sw.s2_map == from_sw.s2_map.insert`).
    lemma_insert_map_edge(sw1, region, i);
    // `wf` of the source endpoint (the synced partial).
    lemma_insert_partial_machine_wf(sw1, hw, region, (i + 1) as nat, i);
    // The freshly-mapped gpa is unreachable in `from_sw` (region entry, unmapped in sw1).
    assert(!from_sw.s2_map.contains_key(key)) by {
        assert(region.entries().contains_key(key));
        assert(!sw1.s2_map.contains_key(key));
        assert(!entry_prefix(region, i).dom().contains(key));  // index i not < i
    }
    // The hardware side is exactly `map_step`: reachable map grows by `key`, TLB fixed.
    assert(HardwareView::map_step(hw1, hw2, vm, gpa, entry));
    refine_hv_map(from_sw, to_sw, hw1, hw2, vm, gpa, entry);
}

/// Edge `j` of the machine insert trace: assign region page `i = j/2` (even `j`)
/// then map region entry `i` (odd `j`).
pub open spec fn insert_hv_edge(s: MachineState, t: MachineState, region: Region, j: nat) -> bool {
    let i = (j / 2) as nat;
    if j % 2 == 0 {
        MachineState::hv_assign_page_step(s, t, region.vm, region.phys_page(i))
    } else {
        MachineState::hv_map_step(
            s,
            t,
            region.vm,
            region.guest_page(i),
            S2Entry { page: region.phys_page(i), access: region.access, generation: 0 },
        )
    }
}

/// An `insert_region` is realized by a `2*count + 1`-state trace of `MachineState`
/// hypervisor steps (per-page `hv_assign_page` / `hv_map`), every state `wf`.
pub proof fn lemma_insert_region_machine_trace(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw: HardwareView,
    region: Region,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::insert_region_enabled(sw1, region),
        SoftwareView::insert_region_step(sw1, sw2, region),
    ensures
        exists|trace: Seq<MachineState>|
            #![auto]
            {
                &&& trace.len() == 2 * region.count + 1
                &&& trace[0] == MachineState::assemble(sw1, hw)
                &&& trace[trace.len() - 1] == MachineState::assemble(sw2, synced_hw(sw2, hw))
                &&& forall|j: int|
                    0 <= j < 2 * region.count ==> #[trigger] insert_hv_edge(
                        trace[j],
                        trace[j + 1],
                        region,
                        j as nat,
                    )
                &&& forall|j: int| 0 <= j < trace.len() ==> (#[trigger] trace[j]).wf()
            },
{
    let n = region.count;
    lemma_sw_machine_wf_equiv(sw1, hw);
    assert(sw1.wf());
    let trace = Seq::new(
        (2 * n + 1) as nat,
        |j: int| insert_machine_partial(sw1, hw, region, ((j + 1) / 2) as nat, (j / 2) as nat),
    );
    // Endpoints: the SW partials collapse to `sw1` / `sw2`.
    assert(phys_prefix(region, 0) =~= Set::<PhysPage>::empty());
    assert(entry_prefix(region, 0) =~= Map::<VmPageKey, S2Entry>::empty());
    assert(phys_prefix(region, n) =~= region.pages());
    assert(entry_prefix(region, n) =~= region.entries());
    assert(insert_partial(sw1, region, 0, 0) == sw1) by {
        assert(sw1.hypervisor_owned.difference(phys_prefix(region, 0)) =~= sw1.hypervisor_owned);
        assert(sw1.vm_owned[region.vm].union(phys_prefix(region, 0)) =~= sw1.vm_owned[region.vm]);
        assert(sw1.vm_owned.insert(region.vm, sw1.vm_owned[region.vm]) =~= sw1.vm_owned);
        assert(sw1.s2_map.union_prefer_right(entry_prefix(region, 0)) =~= sw1.s2_map);
    }
    // trace[0]: `synced_hw(sw1, hw) == hw` since `s1` is synced (wf precondition).
    assert(trace[0] == MachineState::assemble(sw1, hw)) by {
        assert(MachineState::assemble(sw1, hw).sync());
        lemma_synced_hw_id(sw1, hw);
    }
    assert(trace[trace.len() - 1] == MachineState::assemble(sw2, synced_hw(sw2, hw))) by {
        assert(trace.len() - 1 == 2 * n);
        assert((2 * n + 1) / 2 == n && (2 * n) / 2 == n) by (nonlinear_arith);
        assert(sw1.vm_owned[region.vm].union(phys_prefix(region, n))
            =~= sw1.vm_owned[region.vm].union(region.pages()));
        assert(insert_partial(sw1, region, n, n) == sw2);
    }
    // Each edge is the matching assign / map machine step.
    assert forall|j: int| 0 <= j < 2 * n implies #[trigger] insert_hv_edge(
        trace[j],
        trace[j + 1],
        region,
        j as nat,
    ) by {
        let i = (j / 2) as nat;
        lemma_half_index(j);
        if j % 2 == 0 {
            assert(i < n);
            lemma_insert_assign_edge(sw1, region, i);
            lemma_insert_partial_machine_wf(sw1, hw, region, i, i);
            // assign keeps `s2_map` fixed, so the two partials share the synced `hw`.
            assert(insert_partial(sw1, region, i, i).s2_map == insert_partial(
                sw1,
                region,
                (i + 1) as nat,
                i,
            ).s2_map);
            refine_hv_assign_page(
                insert_partial(sw1, region, i, i),
                insert_partial(sw1, region, (i + 1) as nat, i),
                synced_hw(insert_partial(sw1, region, i, i), hw),
                region.vm,
                region.phys_page(i),
            );
        } else {
            assert(i < n);
            lemma_insert_map_machine_edge(sw1, hw, region, i);
        }
    }
    // Every intermediate state is `wf`.
    assert forall|j: int| 0 <= j < trace.len() implies (#[trigger] trace[j]).wf() by {
        assert(j / 2 <= (j + 1) / 2 <= n) by (nonlinear_arith)
            requires
                0 <= j < 2 * n + 1,
        ;
        lemma_insert_partial_machine_wf(sw1, hw, region, ((j + 1) / 2) as nat, (j / 2) as nat);
    }
    assert(trace.len() == 2 * region.count + 1);
}

// ---------------------------------------------------------------------------
// Region → per-page MACHINE trace  (remove side)
//
// Symmetric to insert, but the TLB is *not* fixed: a region gpa is mapped in
// `sw1`, so `tlb_safe` permits cached entries for it, and each unmap flushes
// exactly those.  The partial TLB is therefore `hw.tlb` minus the keys for the
// first-`u` region gpas (`tlb_prefix_keys`).  The trace ends at `hw` with *all*
// region-gpa entries flushed — the honest post-remove hardware.
//
// Reclaim's `page_is_quiescent` is discharged from: the unmapped+no-dangling
// `s2_map` (no surviving entry targets the page), `tlb_safe` (so no cached entry
// does either), and the new `remove_region_enabled` unshared clause (no sharing
// edge does).
// ---------------------------------------------------------------------------
/// TLB keys naming one of the first `u` region guest pages.
pub open spec fn tlb_prefix_keys(region: Region, u: nat) -> Set<TlbKey> {
    Set::new(|k: TlbKey| k.vm == region.vm && region.gpa_base <= k.gpa.0 < region.gpa_base + u)
}

/// `hw` after flushing the TLB entries for the first `u` region guest pages.
pub open spec fn hw_unmapped(hw: HardwareView, region: Region, u: nat) -> HardwareView {
    HardwareView {
        tlb: hw.tlb.remove_keys(tlb_prefix_keys(region, u)),
        s2map: hw.s2map,
        memory: hw.memory,
        active_vm: hw.active_vm,
    }
}

/// `hw` after a full `remove_region` (all region gpas flushed from the TLB).
pub open spec fn hw_after_unmap_region(hw: HardwareView, region: Region) -> HardwareView {
    hw_unmapped(hw, region, region.count)
}

/// Machine partial-remove state: SW `remove_partial` assembled with the partially
/// flushed TLB.
pub open spec fn remove_machine_partial(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    u: nat,
    r: nat,
) -> MachineState {
    let sp = remove_partial(sw1, region, u, r);
    MachineState::assemble(sp, synced_hw(sp, hw_unmapped(hw, region, u)))
}

/// Each partial-remove state is `wf`.
pub proof fn lemma_remove_partial_machine_wf(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    u: nat,
    r: nat,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::remove_region_enabled(sw1, region),
        r <= u,
        u <= region.count,
    ensures
        remove_machine_partial(sw1, hw, region, u, r).wf(),
{
    let sp = remove_partial(sw1, region, u, r);
    let mp = remove_machine_partial(sw1, hw, region, u, r);
    let m1 = MachineState::assemble(sw1, hw);
    lemma_sw_machine_wf_equiv(sw1, hw);
    assert(sw1.wf());
    lemma_remove_partial_wf(sw1, region, u, r);
    lemma_sw_machine_wf_equiv(sp, synced_hw(sp, hw_unmapped(hw, region, u)));
    // execution_wf: active_vm / all_vms unchanged.
    assert(mp.all_vms == m1.all_vms);
    assert(mp.active_vm == m1.active_vm);
    assert(m1.execution_wf());
    assert(mp.execution_wf());
    // sync holds by construction.
    assert(mp.hw_s2map == mp.s2_map);
    // tlb_safe (over `hw_s2map == s2_map`): a surviving cached key `k` (∉
    // tlb_prefix_keys(u)) has `sk ∉ entry_prefix(u).dom()`, so the s2_map removal
    // keeps `sw1`'s value, matching `m1.tlb_safe`.
    assert(m1.tlb_safe());
    assert(m1.sync());
    assert forall|k: TlbKey| #[trigger] mp.tlb.contains_key(k) implies {
        let sk = VmPageKey::new(k.vm, k.gpa);
        &&& mp.hw_s2map.contains_key(sk)
        &&& mp.tlb[k].as_s2_entry() == mp.hw_s2map[sk]
    } by {
        let sk = VmPageKey::new(k.vm, k.gpa);
        assert(m1.tlb.contains_key(k) && !tlb_prefix_keys(region, u).contains(k));
        assert(mp.tlb[k] == m1.tlb[k]);
        assert(m1.hw_s2map.contains_key(sk) && m1.tlb[k].as_s2_entry() == m1.hw_s2map[sk]);
        assert(sw1.s2_map.contains_key(sk));  // m1.tlb_safe + m1.sync
        assert(!entry_prefix(region, u).dom().contains(sk)) by {
            if entry_prefix(region, u).dom().contains(sk) {
                assert(tlb_prefix_keys(region, u).contains(k));
            }
        }
        assert(mp.hw_s2map[sk] == sw1.s2_map[sk]);
    }
    assert(mp.wf());
}

/// Even edge `2*i` at the machine level: unmapping region entry `i` is an
/// `hv_unmap_step`; the flush removes exactly the cached `(vm, gpa_i)` entries.
pub proof fn lemma_remove_unmap_machine_edge(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    i: nat,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::remove_region_enabled(sw1, region),
        i < region.count,
    ensures
        MachineState::hv_unmap_step(
            remove_machine_partial(sw1, hw, region, i, i),
            remove_machine_partial(sw1, hw, region, (i + 1) as nat, i),
            region.vm,
            region.guest_page(i),
        ),
{
    let vm = region.vm;
    let gpa = region.guest_page(i);
    let key = VmPageKey::new(vm, gpa);
    let s1 = remove_machine_partial(sw1, hw, region, i, i);
    let s2 = remove_machine_partial(sw1, hw, region, (i + 1) as nat, i);
    lemma_sw_machine_wf_equiv(sw1, hw);
    assert(sw1.wf());
    lemma_remove_unmap_edge(sw1, region, i);
    lemma_remove_partial_machine_wf(sw1, hw, region, i, i);
    lemma_remove_partial_machine_wf(sw1, hw, region, (i + 1) as nat, i);
    // `key` is region entry `i`: mapped in `sw1`, not yet unmapped, so present in `s1`.
    assert(region.entries().contains_key(key));
    assert(sw1.s2_map.contains_key(key));
    assert(!entry_prefix(region, i).dom().contains(key));
    assert(s1.s2_map.contains_key(key));
    // tlb: s2.tlb == s1.tlb.remove_keys(invalidation_targets(vm, gpa)).  The extra
    // flushed keys are exactly the cached `(vm, gpa_i)` ones, i.e. tlb_prefix grows.
    assert(s2.tlb =~= s1.tlb.remove_keys(s1.invalidation_targets(vm, gpa))) by {
        assert forall|k: TlbKey|
            #![auto]
            tlb_prefix_keys(region, (i + 1) as nat).contains(k) <==> (tlb_prefix_keys(
                region,
                i,
            ).contains(k) || (k.vm == vm && k.gpa == gpa)) by {}
    }
}

/// Odd edge `2*i+1` at the machine level: reclaiming region page `i` is an
/// `hv_reclaim_page_step`; `page_is_quiescent` holds by the discharged s2_map / TLB
/// / sharing conditions.
pub proof fn lemma_remove_reclaim_machine_edge(
    sw1: SoftwareView,
    hw: HardwareView,
    region: Region,
    i: nat,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::remove_region_enabled(sw1, region),
        i < region.count,
    ensures
        MachineState::hv_reclaim_page_step(
            remove_machine_partial(sw1, hw, region, (i + 1) as nat, i),
            remove_machine_partial(sw1, hw, region, (i + 1) as nat, (i + 1) as nat),
            region.vm,
            region.phys_page(i),
        ),
{
    let vm = region.vm;
    let page = region.phys_page(i);
    let s1 = remove_machine_partial(sw1, hw, region, (i + 1) as nat, i);
    lemma_sw_machine_wf_equiv(sw1, hw);
    assert(sw1.wf());
    lemma_remove_reclaim_edge(sw1, region, i);
    lemma_remove_partial_machine_wf(sw1, hw, region, (i + 1) as nat, i);
    lemma_remove_partial_machine_wf(sw1, hw, region, (i + 1) as nat, (i + 1) as nat);
    assert(phys_prefix(region, (i + 1) as nat).contains(page));  // page index i < i+1
    assert(region.pages().contains(page));  // i < count
    assert(s1.page_is_quiescent(page)) by {
        // (1) no surviving s2_map entry targets `page` (it is in the first-(i+1) prefix).
        assert forall|k: VmPageKey| #[trigger] s1.s2_map.contains_key(k) implies s1.s2_map[k].page
            != page by {
            assert(sw1.s2_map.contains_key(k) && !entry_prefix(
                region,
                (i + 1) as nat,
            ).dom().contains(k));
            assert(s1.s2_map[k] == sw1.s2_map[k]);
            lemma_remove_survivor_unreclaimed(sw1, region, (i + 1) as nat, (i + 1) as nat, k);
        }
        // (2) no cached TLB entry targets `page` (tlb_safe routes it through s2_map).
        assert(s1.wf());
        assert forall|kt: TlbKey| #[trigger] s1.tlb.contains_key(kt) implies s1.tlb[kt].page
            != page by {
            let sk = VmPageKey::new(kt.vm, kt.gpa);
            assert(s1.s2_map.contains_key(sk) && s1.tlb[kt].as_s2_entry() == s1.s2_map[sk]);
        }
        // (3) no sharing edge targets `page` (the unshared `remove_region_enabled` clause).
        assert forall|e: SharedPage| #[trigger] s1.shared_pages.contains(e) implies e.page
            != page by {
            assert(sw1.shared_pages.contains(e));
        }
    }
}

/// Edge `j` of the machine remove trace: unmap region entry `i = j/2` (even `j`)
/// then reclaim region page `i` (odd `j`).
pub open spec fn remove_hv_edge(s: MachineState, t: MachineState, region: Region, j: nat) -> bool {
    let i = (j / 2) as nat;
    if j % 2 == 0 {
        MachineState::hv_unmap_step(s, t, region.vm, region.guest_page(i))
    } else {
        MachineState::hv_reclaim_page_step(s, t, region.vm, region.phys_page(i))
    }
}

/// A `remove_region` is realized by a `2*count + 1`-state trace of `MachineState`
/// hypervisor steps (per-page `hv_unmap` / `hv_reclaim_page`), every state `wf`.
/// The trace ends at `sw2` assembled with the fully-flushed TLB.
pub proof fn lemma_remove_region_machine_trace(
    sw1: SoftwareView,
    sw2: SoftwareView,
    hw: HardwareView,
    region: Region,
)
    requires
        MachineState::assemble(sw1, hw).wf(),
        SoftwareView::remove_region_enabled(sw1, region),
        SoftwareView::remove_region_step(sw1, sw2, region),
    ensures
        exists|trace: Seq<MachineState>|
            #![auto]
            {
                &&& trace.len() == 2 * region.count + 1
                &&& trace[0] == MachineState::assemble(sw1, hw)
                &&& trace[trace.len() - 1] == MachineState::assemble(
                    sw2,
                    synced_hw(sw2, hw_after_unmap_region(hw, region)),
                )
                &&& forall|j: int|
                    0 <= j < 2 * region.count ==> #[trigger] remove_hv_edge(
                        trace[j],
                        trace[j + 1],
                        region,
                        j as nat,
                    )
                &&& forall|j: int| 0 <= j < trace.len() ==> (#[trigger] trace[j]).wf()
            },
{
    let n = region.count;
    lemma_sw_machine_wf_equiv(sw1, hw);
    assert(sw1.wf());
    let trace = Seq::new(
        (2 * n + 1) as nat,
        |j: int| remove_machine_partial(sw1, hw, region, ((j + 1) / 2) as nat, (j / 2) as nat),
    );
    assert(phys_prefix(region, 0) =~= Set::<PhysPage>::empty());
    assert(tlb_prefix_keys(region, 0) =~= Set::<TlbKey>::empty());
    assert(entry_prefix(region, 0).dom() =~= Set::<VmPageKey>::empty());
    assert(phys_prefix(region, n) =~= region.pages());
    assert(entry_prefix(region, n).dom() =~= region.entries().dom());
    // trace[0]: empty prefixes ⟹ remove_partial(0,0)==sw1 and hw_unmapped(0)==hw.
    assert(trace[0] == MachineState::assemble(sw1, hw)) by {
        assert(sw1.hypervisor_owned.union(phys_prefix(region, 0)) =~= sw1.hypervisor_owned);
        assert(sw1.vm_owned[region.vm].difference(phys_prefix(region, 0))
            =~= sw1.vm_owned[region.vm]);
        assert(sw1.vm_owned.insert(region.vm, sw1.vm_owned[region.vm]) =~= sw1.vm_owned);
        assert(sw1.s2_map.remove_keys(entry_prefix(region, 0).dom()) =~= sw1.s2_map);
        assert(hw.tlb.remove_keys(tlb_prefix_keys(region, 0)) =~= hw.tlb);
    }
    // trace[last]: full prefixes ⟹ remove_partial(n,n)==sw2 and hw_unmapped(n)==hw'.
    assert(trace[trace.len() - 1] == MachineState::assemble(
        sw2,
        synced_hw(sw2, hw_after_unmap_region(hw, region)),
    )) by {
        assert(trace.len() - 1 == 2 * n);
        assert((2 * n + 1) / 2 == n && (2 * n) / 2 == n) by (nonlinear_arith);
        assert(sw1.hypervisor_owned.union(phys_prefix(region, n)) =~= sw1.hypervisor_owned.union(
            region.pages(),
        ));
        assert(sw1.vm_owned[region.vm].difference(phys_prefix(region, n))
            =~= sw1.vm_owned[region.vm].difference(region.pages()));
        assert(sw1.s2_map.remove_keys(entry_prefix(region, n).dom()) =~= sw1.s2_map.remove_keys(
            region.entries().dom(),
        ));
    }
    // Each edge is the matching unmap / reclaim machine step.
    assert forall|j: int| 0 <= j < 2 * n implies #[trigger] remove_hv_edge(
        trace[j],
        trace[j + 1],
        region,
        j as nat,
    ) by {
        let i = (j / 2) as nat;
        lemma_half_index(j);
        if j % 2 == 0 {
            assert(i < n);
            lemma_remove_unmap_machine_edge(sw1, hw, region, i);
        } else {
            assert(i < n);
            lemma_remove_reclaim_machine_edge(sw1, hw, region, i);
        }
    }
    // Every intermediate state is `wf`.
    assert forall|j: int| 0 <= j < trace.len() implies (#[trigger] trace[j]).wf() by {
        assert(j / 2 <= (j + 1) / 2 <= n) by (nonlinear_arith)
            requires
                0 <= j < 2 * n + 1,
        ;
        lemma_remove_partial_machine_wf(sw1, hw, region, ((j + 1) / 2) as nat, (j / 2) as nat);
    }
    assert(trace.len() == 2 * region.count + 1);
}

// ---------------------------------------------------------------------------
// Sync bridge: synced `MmuSpec`/`BudgetSpec` ⟹ a `wf` machine state.
// ---------------------------------------------------------------------------
/// The MMU and budget states are *synced*: the hardware-reachable map (flattened
/// `MmuSpec.s2map`) equals the software-maintained map (`BudgetSpec`'s projection).
/// This is the per-vm lock invariant aggregated over all vms.
pub open spec fn specs_synced(mmu: MmuSpec::State, budget: BudgetSpec::State) -> bool {
    flatten_s2map(mmu.s2map) == state_s2_map(budget)
}

/// **Synced specs refine a `wf` machine.** Reachable `MmuSpec` / `BudgetSpec` states
/// that are [`specs_synced`] project (via their views) to a `wf` `MachineState` — so
/// the implementation, which forces sync, reaches well-formed (hence secure) states.
pub proof fn lemma_specs_synced_implies_wf_machine(mmu: MmuSpec::State, budget: BudgetSpec::State)
    requires
        mmu.invariant(),
        budget.invariant(),
        specs_synced(mmu, budget),
    ensures
        MachineState::assemble(budget.view(), mmu.view()).wf(),
{
    // Each view is internally well-formed (from its own state machine's invariant).
    budget.inv_implies_wf();
    mmu.inv_implies_wf();
    // view-sync: the two projected stage-2 maps coincide (the `specs_synced` hyp).
    assert(mmu.view().s2map == budget.view().s2_map);
    // The MMU view schedules no vm, so the scheduler clause is vacuous.
    assert(mmu.view().active_vm == Map::<CpuId, VmId>::empty());
    lemma_synced_views_wf(budget.view(), mmu.view());
}

} // verus!
