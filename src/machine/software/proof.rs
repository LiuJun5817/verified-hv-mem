//! Proof obligations for the `SoftwareView` state machine.
//!
//! `wf` is an inductive invariant: per-page, lifecycle, and region steps all
//! preserve it (proved below).  This module is `admit`-free.
//!
//! Families, in dependency order:
//! 1. **per-page `wf`-preservation** — each primitive step keeps `wf` (base cases).
//! 2. **lifecycle `wf`-preservation** — `add_vm` / `remove_vm`.
//! 3. **region `wf`-preservation** — proved directly by set/map algebra.
use vstd::prelude::*;

use super::{Region, SoftwareView};
use crate::machine::types::*;

verus! {

// ─────────────────────────── per-page wf-preservation ───────────────────────
pub proof fn lemma_map_step_preserves_wf(
    s1: SoftwareView,
    s2: SoftwareView,
    vm: VmId,
    gpa: GuestPage,
    entry: S2Entry,
)
    requires
        s1.wf(),
        SoftwareView::map_step(s1, s2, vm, gpa, entry),
    ensures
        s2.wf(),
{
    // Only `s2_map` changes: `ownership_wf` / `sharing_wf` carry over unchanged.
    let key = VmPageKey::new(vm, gpa);
    assert forall|k: VmPageKey| #[trigger] s2.s2_map.contains_key(k) implies (s2.all_vms.contains(
        k.vm,
    ) && s2.owned_or_shared(k.vm, s2.s2_map[k].page)) by {
        if k != key {
            assert(s1.s2_map.contains_key(k));
        }
    }
    // IOMMU contexts and `vm_owned` are unchanged, so `iommu_wf` carries over verbatim.
    assert(s1.iommu_wf());
    assert(s2.iommu_wf());
    assert(s2.wf());
}

pub proof fn lemma_unmap_step_preserves_wf(
    s1: SoftwareView,
    s2: SoftwareView,
    vm: VmId,
    gpa: GuestPage,
)
    requires
        s1.wf(),
        SoftwareView::unmap_step(s1, s2, vm, gpa),
    ensures
        s2.wf(),
{
    // `s2_map` only shrinks; every surviving key kept its (valid) target.
    assert forall|k: VmPageKey| #[trigger] s2.s2_map.contains_key(k) implies (s2.all_vms.contains(
        k.vm,
    ) && s2.owned_or_shared(k.vm, s2.s2_map[k].page)) by {
        assert(s1.s2_map.contains_key(k));
    }
    // IOMMU contexts and `vm_owned` are unchanged, so `iommu_wf` carries over verbatim.
    assert(s1.iommu_wf());
    assert(s2.iommu_wf());
    assert(s2.wf());
}

// ─────────────────── IOMMU per-page iommu_wf-preservation ────────────────────
// The per-page DMA-remap steps touch only `iommu_s2_map`; all of `iommu_owned`,
// `vm_owned`, `all_vms`, `iommu_shared` are framed unchanged, so `iommu_ownership_wf`
// carries over verbatim and only `iommu_translation_wf` needs the new/surviving key
// checked.  No cross-VM guard is needed (unlike the CPU page/region ops, which can
// move ownership): these never change who owns what for DMA.
pub proof fn lemma_iommu_map_step_preserves_iommu_wf(
    s1: SoftwareView,
    s2: SoftwareView,
    vm: VmId,
    gpa: GuestPage,
    entry: S2Entry,
)
    requires
        s1.iommu_wf(),
        SoftwareView::iommu_map_step(s1, s2, vm, gpa, entry),
    ensures
        s2.iommu_wf(),
{
    let key = VmPageKey::new(vm, gpa);
    // ownership_wf: iommu_owned / vm_owned / all_vms / iommu_shared all unchanged.
    assert(s2.iommu_ownership_wf());
    // translation_wf: surviving keys keep their (private-or-shared) target; the new key
    // targets a page `vm` may DMA — private (`iommu_owned`) or shared (`iommu_shared`) —
    // by the step's enabling guard.
    assert forall|k: VmPageKey| #[trigger] s2.iommu_s2_map.contains_key(k) implies (
    s2.all_vms.contains(k.vm) && s2.iommu_owned.contains_key(k.vm)
        && (s2.iommu_owned[k.vm].contains(s2.iommu_s2_map[k].page)
            || s2.iommu_shared.contains(s2.iommu_s2_map[k].page))) by {
        if k != key {
            assert(s1.iommu_s2_map.contains_key(k));
        }
    }
    assert(s2.iommu_translation_wf());
}

pub proof fn lemma_iommu_unmap_step_preserves_iommu_wf(
    s1: SoftwareView,
    s2: SoftwareView,
    vm: VmId,
    gpa: GuestPage,
)
    requires
        s1.iommu_wf(),
        SoftwareView::iommu_unmap_step(s1, s2, vm, gpa),
    ensures
        s2.iommu_wf(),
{
    // `iommu_s2_map` only shrinks; ownership is untouched, so every surviving entry
    // keeps its valid private-or-shared DMA target.
    assert(s2.iommu_ownership_wf());
    assert forall|k: VmPageKey| #[trigger] s2.iommu_s2_map.contains_key(k) implies (
    s2.all_vms.contains(k.vm) && s2.iommu_owned.contains_key(k.vm)
        && (s2.iommu_owned[k.vm].contains(s2.iommu_s2_map[k].page)
            || s2.iommu_shared.contains(s2.iommu_s2_map[k].page))) by {
        assert(s1.iommu_s2_map.contains_key(k));
    }
    assert(s2.iommu_translation_wf());
}

pub proof fn lemma_assign_page_step_preserves_wf(
    s1: SoftwareView,
    s2: SoftwareView,
    vm: VmId,
    page: PhysPage,
)
    requires
        s1.wf(),
        SoftwareView::assign_page_step(s1, s2, vm, page),
    ensures
        s2.wf(),
{
    // `page` is free, so it lies in no VM's ownership set.
    assert(s1.hypervisor_owned.contains(page));
    assert(s2.vm_owned.dom() =~= s2.all_vms);
    assert(forall|w: VmId| #[trigger] s1.all_vms.contains(w) ==> !s1.vm_owned[w].contains(page));
    // Pairwise disjointness: only `vm`'s set grows, and just by the free `page`.
    assert forall|a: VmId, b: VmId| #[trigger]
        s2.all_vms.contains(a) && #[trigger] s2.all_vms.contains(b) && a != b implies (forall|
        p: PhysPage,
    | #[trigger]
        s2.vm_owned[a].contains(p) ==> !s2.vm_owned[b].contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.vm_owned[a].contains(p) implies !s2.vm_owned[b].contains(p) by {
            if a == vm {
                if p != page {
                    assert(s1.vm_owned[vm].contains(p));
                }
            } else if b == vm {
                if p != page {
                    assert(s1.vm_owned[a].contains(p));
                }
            }
        }
    }
    // vm-vs-hypervisor: `vm` gained `page`, which left the pool.
    assert forall|w: VmId| #[trigger] s2.all_vms.contains(w) implies (forall|p: PhysPage|
     #[trigger]
        s2.vm_owned[w].contains(p) ==> !s2.hypervisor_owned.contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.vm_owned[w].contains(p) implies !s2.hypervisor_owned.contains(p) by {
            if w != vm || p != page {
                assert(s1.vm_owned[w].contains(p));
            }
        }
    }
    // `s2_map` unchanged; targets stay owned-or-shared since ownership only grew.
    assert forall|k: VmPageKey| #[trigger] s2.s2_map.contains_key(k) implies (s2.all_vms.contains(
        k.vm,
    ) && s2.owned_or_shared(k.vm, s2.s2_map[k].page)) by {
        assert(s1.s2_map.contains_key(k));
    }
    // IOMMU: only `vm_owned` grew (by the free `page`); `iommu_owned`/`iommu_shared`/
    // `iommu_s2_map` are unchanged, so translation_wf and clauses (1),(3) carry.  Clause
    // (2) (a VM's private DMA page is never another VM's CPU page) uses the step guard:
    // `page` is not any *other* VM's private DMA page.
    assert(s1.iommu_wf());
    assert forall|v1: VmId, v2: VmId| #[trigger]
        s2.all_vms.contains(v1) && #[trigger] s2.all_vms.contains(v2) && v1 != v2 implies (forall|
        p: PhysPage,
    | #[trigger] s2.iommu_owned[v1].contains(p) ==> !s2.vm_owned[v2].contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.iommu_owned[v1].contains(p) implies !s2.vm_owned[v2].contains(p) by {
            if v2 == vm {
                if p == page {
                    // Hypothesis `iommu_owned[v1].contains(page)` (v1 != vm) contradicts the
                    // step guard, so this case is vacuous.
                    assert(!s1.iommu_owned[v1].contains(page));
                    assert(false);
                } else {
                    // `page` is the only new element of `vm_owned[vm]`; s1 clause (2) applies.
                    assert(s1.iommu_owned[v1].contains(p));
                }
            } else {
                assert(s1.iommu_owned[v1].contains(p));  // `vm_owned[v2]` unchanged
            }
        }
    }
    assert(s2.iommu_ownership_wf());
    assert(s2.iommu_translation_wf());
    assert(s2.wf());
}

pub proof fn lemma_reclaim_page_step_preserves_wf(
    s1: SoftwareView,
    s2: SoftwareView,
    vm: VmId,
    page: PhysPage,
)
    requires
        s1.wf(),
        SoftwareView::reclaim_page_step(s1, s2, vm, page),
        // Quiescence: no surviving translation or sharing edge targets `page`.
        forall|k: VmPageKey| #[trigger] s1.s2_map.contains_key(k) ==> s1.s2_map[k].page != page,
        forall|e: SharedPage| #[trigger] s1.shared_pages.contains(e) ==> e.page != page,
    ensures
        s2.wf(),
{
    // `page` was owned by `vm` alone, so it lies in no *other* VM's set.
    assert(s2.vm_owned.dom() =~= s2.all_vms);
    assert(forall|w: VmId| #[trigger]
        s1.all_vms.contains(w) && w != vm ==> !s1.vm_owned[w].contains(page));
    // Pairwise disjointness: ownership only shrinks (`vm` loses `page`).
    assert forall|a: VmId, b: VmId| #[trigger]
        s2.all_vms.contains(a) && #[trigger] s2.all_vms.contains(b) && a != b implies (forall|
        p: PhysPage,
    | #[trigger]
        s2.vm_owned[a].contains(p) ==> !s2.vm_owned[b].contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.vm_owned[a].contains(p) implies !s2.vm_owned[b].contains(p) by {
            assert(s1.vm_owned[a].contains(p));  // s2[a] ⊆ s1[a]
        }
    }
    // vm-vs-hypervisor: `page` re-enters the pool but is owned by no one in `s2`.
    assert forall|w: VmId| #[trigger] s2.all_vms.contains(w) implies (forall|p: PhysPage|
     #[trigger]
        s2.vm_owned[w].contains(p) ==> !s2.hypervisor_owned.contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.vm_owned[w].contains(p) implies !s2.hypervisor_owned.contains(p) by {
            assert(s1.vm_owned[w].contains(p));  // s2[w] ⊆ s1[w]
            assert(p != page);  // `page` is no longer owned by any VM
        }
    }
    // Quiescence: no surviving translation targets `page`, so all targets stay owned.
    assert forall|k: VmPageKey| #[trigger] s2.s2_map.contains_key(k) implies (s2.all_vms.contains(
        k.vm,
    ) && s2.owned_or_shared(k.vm, s2.s2_map[k].page)) by {
        assert(s1.s2_map.contains_key(k));
    }
    // IOMMU: `vm_owned[vm]` only shrinks, `iommu_*` unchanged, so `iommu_wf` carries —
    // clause (2) only relaxes (`vm_owned[v2] ⊆ s1.vm_owned[v2]`).
    assert(s1.iommu_wf());
    assert forall|v1: VmId, v2: VmId| #[trigger]
        s2.all_vms.contains(v1) && #[trigger] s2.all_vms.contains(v2) && v1 != v2 implies (forall|
        p: PhysPage,
    | #[trigger] s2.iommu_owned[v1].contains(p) ==> !s2.vm_owned[v2].contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.iommu_owned[v1].contains(p) implies !s2.vm_owned[v2].contains(p) by {
            if s2.vm_owned[v2].contains(p) {
                assert(s1.vm_owned[v2].contains(p));  // s2[v2] ⊆ s1[v2]
                assert(s1.iommu_owned[v1].contains(p));
            }
        }
    }
    assert(s2.iommu_ownership_wf());
    assert(s2.iommu_translation_wf());
    assert(s2.wf());
}

// ─────────────────────────── sharing wf-preservation ────────────────────────
pub proof fn lemma_share_page_step_preserves_wf(
    s1: SoftwareView,
    s2: SoftwareView,
    left: VmId,
    right: VmId,
    page: PhysPage,
)
    requires
        s1.wf(),
        SoftwareView::share_page_step(s1, s2, left, right, page),
    ensures
        s2.wf(),
{
    let edge = SharedPage { left, right, page };
    let rev = edge.reverse();
    // Ownership and `all_vms` are untouched.
    assert(s2.ownership_wf());
    // sharing_wf: the two new edges are valid and mutually symmetric; old edges persist.
    assert forall|e: SharedPage| #[trigger] s2.shared_pages.contains(e) implies (e.left != e.right
        && s2.all_vms.contains(e.left) && s2.all_vms.contains(e.right) && s2.shared_pages.contains(
        e.reverse(),
    )) by {
        if e != edge && e != rev {
            assert(s1.shared_pages.contains(e));
        }
    }
    // translation_wf: `s2_map` is unchanged and `owned_or_shared` only grew (a sharing
    // edge was added, ownership is the same), so every target stays owned-or-shared.
    assert forall|k: VmPageKey| #[trigger] s2.s2_map.contains_key(k) implies (s2.all_vms.contains(
        k.vm,
    ) && s2.owned_or_shared(k.vm, s2.s2_map[k].page)) by {
        assert(s1.s2_map.contains_key(k));
        assert(s1.owned_or_shared(k.vm, s1.s2_map[k].page));
        if s1.shared_with(k.vm, s1.s2_map[k].page) {
            let w = choose|w: SharedPage| #[trigger]
                s1.shared_pages.contains(w) && w.page == s1.s2_map[k].page && (w.left == k.vm
                    || w.right == k.vm);
            assert(s2.shared_pages.contains(w));
        }
    }
    // IOMMU contexts and `vm_owned` are unchanged, so `iommu_wf` carries over verbatim.
    assert(s1.iommu_wf());
    assert(s2.iommu_wf());
    assert(s2.wf());
}

pub proof fn lemma_unshare_page_step_preserves_wf(
    s1: SoftwareView,
    s2: SoftwareView,
    left: VmId,
    right: VmId,
    page: PhysPage,
)
    requires
        s1.wf(),
        SoftwareView::unshare_page_step(s1, s2, left, right, page),
        // No dangling: any mapping of `page` by an endpoint of the removed edge is
        // backed by *ownership*, so losing the share leaves no stranded translation.
        // (The analogue of `reclaim`'s quiescence, scoped to the edge's endpoints.)
        forall|k: VmPageKey| #[trigger]
            s1.s2_map.contains_key(k) && (k.vm == left || k.vm == right) && s1.s2_map[k].page
                == page ==> s1.vm_owned[k.vm].contains(page),
    ensures
        s2.wf(),
{
    let edge = SharedPage { left, right, page };
    let rev = edge.reverse();
    // Ownership and `all_vms` are untouched.
    assert(s2.ownership_wf());
    // sharing_wf: a surviving edge's reverse can't be one of the two removed (else
    // the edge itself would be removed), so symmetry is preserved.
    assert forall|e: SharedPage| #[trigger] s2.shared_pages.contains(e) implies (e.left != e.right
        && s2.all_vms.contains(e.left) && s2.all_vms.contains(e.right) && s2.shared_pages.contains(
        e.reverse(),
    )) by {
        assert(s1.shared_pages.contains(e));
    }
    // translation_wf: `s2_map` is unchanged; each target stays owned-or-shared.
    assert forall|k: VmPageKey| #[trigger] s2.s2_map.contains_key(k) implies (s2.all_vms.contains(
        k.vm,
    ) && s2.owned_or_shared(k.vm, s2.s2_map[k].page)) by {
        assert(s1.s2_map.contains_key(k));
        assert(s1.owned_or_shared(k.vm, s1.s2_map[k].page));
        let p = s1.s2_map[k].page;
        if !s1.vm_owned[k.vm].contains(p) {
            // Then `k.vm` reaches `p` through some sharing edge `w`, which survives:
            // were `w` one of the removed edges, we'd have `p == page` and
            // `k.vm ∈ {left, right}`, so the no-dangling premise would force
            // `vm_owned[k.vm].contains(page)` — contradicting this branch.
            assert(s1.shared_with(k.vm, p));
            let w = choose|w: SharedPage| #[trigger]
                s1.shared_pages.contains(w) && w.page == p && (w.left == k.vm || w.right == k.vm);
            assert(w != edge && w != rev) by {
                if w == edge || w == rev {
                    assert(s1.vm_owned[k.vm].contains(page));
                    assert(false);
                }
            }
            assert(s2.shared_pages.contains(w));
        }
    }
    // IOMMU contexts and `vm_owned` are unchanged, so `iommu_wf` carries over verbatim.
    assert(s1.iommu_wf());
    assert(s2.iommu_wf());
    assert(s2.wf());
}

// ─────────────────────────── lifecycle wf-preservation ──────────────────────
pub proof fn lemma_add_vm_step_preserves_wf(s1: SoftwareView, s2: SoftwareView, vm: VmId)
    requires
        s1.wf(),
        SoftwareView::add_vm_enabled(s1, vm),
        SoftwareView::add_vm_step(s1, s2, vm),
    ensures
        s2.wf(),
{
    // The new VM owns nothing; `all_vms` only grows.
    assert(s2.vm_owned.dom() =~= s2.all_vms);
    assert forall|a: VmId, b: VmId| #[trigger]
        s2.all_vms.contains(a) && #[trigger] s2.all_vms.contains(b) && a != b implies (forall|
        p: PhysPage,
    | #[trigger]
        s2.vm_owned[a].contains(p) ==> !s2.vm_owned[b].contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.vm_owned[a].contains(p) implies !s2.vm_owned[b].contains(p) by {
            if a != vm && b != vm {
                assert(s1.vm_owned[a].contains(p));
            }
        }
    }
    assert forall|w: VmId| #[trigger] s2.all_vms.contains(w) implies (forall|p: PhysPage|
     #[trigger]
        s2.vm_owned[w].contains(p) ==> !s2.hypervisor_owned.contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.vm_owned[w].contains(p) implies !s2.hypervisor_owned.contains(p) by {
            if w != vm {
                assert(s1.vm_owned[w].contains(p));
            }
        }
    }
    assert forall|e: SharedPage| #[trigger] s2.shared_pages.contains(e) implies (e.left != e.right
        && s2.all_vms.contains(e.left) && s2.all_vms.contains(e.right) && s2.shared_pages.contains(
        e.reverse(),
    )) by {
        assert(s1.shared_pages.contains(e));
    }
    assert forall|k: VmPageKey| #[trigger] s2.s2_map.contains_key(k) implies (s2.all_vms.contains(
        k.vm,
    ) && s2.owned_or_shared(k.vm, s2.s2_map[k].page)) by {
        assert(s1.s2_map.contains_key(k));
    }
    // IOMMU: the fresh VM owns nothing for DMA (`iommu_owned[vm] = ∅`) and has no IOMMU
    // entries, so every `iommu_wf` clause extends to the larger `all_vms`.
    assert(s1.iommu_wf());
    assert(s2.iommu_owned.dom() =~= s2.all_vms);
    assert forall|v1: VmId, v2: VmId| #[trigger]
        s2.all_vms.contains(v1) && #[trigger] s2.all_vms.contains(v2) && v1 != v2 implies ((forall|
        p: PhysPage,
    | #[trigger] s2.iommu_owned[v1].contains(p) ==> !s2.iommu_owned[v2].contains(p)) && (forall|
        p: PhysPage,
    | #[trigger] s2.iommu_owned[v1].contains(p) ==> !s2.vm_owned[v2].contains(p))) by {
        if v1 != vm && v2 != vm {
            assert(s1.all_vms.contains(v1) && s1.all_vms.contains(v2));
        }
    }
    assert forall|w: VmId| #[trigger] s2.all_vms.contains(w) implies (forall|p: PhysPage| #[trigger]
        s2.iommu_owned[w].contains(p) ==> !s2.iommu_shared.contains(p)) by {
        if w != vm {
            assert(s1.all_vms.contains(w));
        }
    }
    assert forall|k: VmPageKey| #[trigger] s2.iommu_s2_map.contains_key(k) implies (
    s2.all_vms.contains(k.vm) && s2.iommu_owned.contains_key(k.vm) && (s2.iommu_owned[k.vm].contains(
        s2.iommu_s2_map[k].page,
    ) || s2.iommu_shared.contains(s2.iommu_s2_map[k].page))) by {
        assert(s1.iommu_s2_map.contains_key(k));  // ⇒ k.vm ∈ s1.all_vms, so k.vm != vm (fresh)
    }
    assert(s2.iommu_wf());
    assert(s2.wf());
}

pub proof fn lemma_remove_vm_step_preserves_wf(s1: SoftwareView, s2: SoftwareView, vm: VmId)
    requires
        s1.wf(),
        SoftwareView::remove_vm_enabled(s1, vm),
        SoftwareView::remove_vm_step(s1, s2, vm),
    ensures
        s2.wf(),
{
    // `vm` (owning nothing, mapping nothing, sharing nothing) is dropped; the rest
    // of the state is unchanged, so every clause carries over to the smaller `all_vms`.
    assert(s2.vm_owned.dom() =~= s2.all_vms);
    assert forall|a: VmId, b: VmId| #[trigger]
        s2.all_vms.contains(a) && #[trigger] s2.all_vms.contains(b) && a != b implies (forall|
        p: PhysPage,
    | #[trigger]
        s2.vm_owned[a].contains(p) ==> !s2.vm_owned[b].contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.vm_owned[a].contains(p) implies !s2.vm_owned[b].contains(p) by {
            assert(s1.vm_owned[a].contains(p));
        }
    }
    assert forall|w: VmId| #[trigger] s2.all_vms.contains(w) implies (forall|p: PhysPage|
     #[trigger]
        s2.vm_owned[w].contains(p) ==> !s2.hypervisor_owned.contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.vm_owned[w].contains(p) implies !s2.hypervisor_owned.contains(p) by {
            assert(s1.vm_owned[w].contains(p));
        }
    }
    assert forall|e: SharedPage| #[trigger] s2.shared_pages.contains(e) implies (e.left != e.right
        && s2.all_vms.contains(e.left) && s2.all_vms.contains(e.right) && s2.shared_pages.contains(
        e.reverse(),
    )) by {
        assert(s1.shared_pages.contains(e));
    }
    assert forall|k: VmPageKey| #[trigger] s2.s2_map.contains_key(k) implies (s2.all_vms.contains(
        k.vm,
    ) && s2.owned_or_shared(k.vm, s2.s2_map[k].page)) by {
        assert(s1.s2_map.contains_key(k));
    }
    // IOMMU: `vm` owns nothing for DMA and maps nothing (enabling), so dropping it keeps
    // every `iommu_wf` clause on the smaller `all_vms`.
    assert(s1.iommu_wf());
    assert(s2.iommu_owned.dom() =~= s2.all_vms);
    assert forall|v1: VmId, v2: VmId| #[trigger]
        s2.all_vms.contains(v1) && #[trigger] s2.all_vms.contains(v2) && v1 != v2 implies ((forall|
        p: PhysPage,
    | #[trigger] s2.iommu_owned[v1].contains(p) ==> !s2.iommu_owned[v2].contains(p)) && (forall|
        p: PhysPage,
    | #[trigger] s2.iommu_owned[v1].contains(p) ==> !s2.vm_owned[v2].contains(p))) by {
        assert(s1.all_vms.contains(v1) && s1.all_vms.contains(v2));
    }
    assert forall|w: VmId| #[trigger] s2.all_vms.contains(w) implies (forall|p: PhysPage| #[trigger]
        s2.iommu_owned[w].contains(p) ==> !s2.iommu_shared.contains(p)) by {
        assert(s1.all_vms.contains(w));
    }
    assert forall|k: VmPageKey| #[trigger] s2.iommu_s2_map.contains_key(k) implies (
    s2.all_vms.contains(k.vm) && s2.iommu_owned.contains_key(k.vm) && (s2.iommu_owned[k.vm].contains(
        s2.iommu_s2_map[k].page,
    ) || s2.iommu_shared.contains(s2.iommu_s2_map[k].page))) by {
        assert(s1.iommu_s2_map.contains_key(k));
        assert(k.vm != vm);  // enabling: no IOMMU entry names `vm`
    }
    assert(s2.iommu_wf());
    assert(s2.wf());
}

} // verus!
