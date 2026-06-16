//! Proof obligations for the `SwView` state machine.
//!
//! `wf` is an inductive invariant: per-page, lifecycle, and region steps all
//! preserve it (proved below).  The only outstanding obligations are the two
//! **region → per-page trace** lemmas, which realize each region step as a trace
//! of atomic per-page steps — the bridge that will let a region operation inherit
//! the machine-level security result proved per-page in `crate::machine::machine`
//! (`SW + HW ⟹ Machine`).  They stay `admit()` until that layer is built.
//!
//! Families, in dependency order:
//! 1. **per-page `wf`-preservation** — each primitive step keeps `wf` (base cases).
//! 2. **lifecycle `wf`-preservation** — `add_vm` / `remove_vm`.
//! 3. **region → per-page trace** — the decomposition (still `admit()`).
//! 4. **region `wf`-preservation** — proved directly by set/map algebra.
use vstd::prelude::*;

use super::{Region, SwView};
use crate::machine::types::*;

verus! {

// ─────────────────────────── per-page wf-preservation ───────────────────────
pub proof fn lemma_map_step_preserves_wf(
    s1: SwView,
    s2: SwView,
    vm: VmId,
    gpa: GuestPage,
    entry: S2Entry,
)
    requires
        s1.wf(),
        SwView::map_step(s1, s2, vm, gpa, entry),
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
    assert(s2.wf());
}

pub proof fn lemma_unmap_step_preserves_wf(s1: SwView, s2: SwView, vm: VmId, gpa: GuestPage)
    requires
        s1.wf(),
        SwView::unmap_step(s1, s2, vm, gpa),
    ensures
        s2.wf(),
{
    // `s2_map` only shrinks; every surviving key kept its (valid) target.
    assert forall|k: VmPageKey| #[trigger] s2.s2_map.contains_key(k) implies (s2.all_vms.contains(
        k.vm,
    ) && s2.owned_or_shared(k.vm, s2.s2_map[k].page)) by {
        assert(s1.s2_map.contains_key(k));
    }
    assert(s2.wf());
}

pub proof fn lemma_assign_page_step_preserves_wf(s1: SwView, s2: SwView, vm: VmId, page: PhysPage)
    requires
        s1.wf(),
        SwView::assign_page_step(s1, s2, vm, page),
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
    assert(s2.wf());
}

pub proof fn lemma_reclaim_page_step_preserves_wf(s1: SwView, s2: SwView, vm: VmId, page: PhysPage)
    requires
        s1.wf(),
        SwView::reclaim_page_step(s1, s2, vm, page),
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
    assert(s2.wf());
}

// ─────────────────────────── sharing wf-preservation ────────────────────────
pub proof fn lemma_share_page_step_preserves_wf(
    s1: SwView,
    s2: SwView,
    left: VmId,
    right: VmId,
    page: PhysPage,
)
    requires
        s1.wf(),
        SwView::share_page_step(s1, s2, left, right, page),
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
            let w = choose|w: SharedPage|
                s1.shared_pages.contains(w) && w.page == s1.s2_map[k].page && (w.left == k.vm
                    || w.right == k.vm);
            assert(s2.shared_pages.contains(w));
        }
    }
    assert(s2.wf());
}

pub proof fn lemma_unshare_page_step_preserves_wf(
    s1: SwView,
    s2: SwView,
    left: VmId,
    right: VmId,
    page: PhysPage,
)
    requires
        s1.wf(),
        SwView::unshare_page_step(s1, s2, left, right, page),
        // No dangling: any mapping of `page` by an endpoint of the removed edge is
        // backed by *ownership*, so losing the share leaves no stranded translation.
        // (The analogue of `reclaim`'s quiescence, scoped to the edge's endpoints.)
        forall|k: VmPageKey|
            #[trigger] s1.s2_map.contains_key(k) && (k.vm == left || k.vm == right) && s1.s2_map[k].page
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
            let w = choose|w: SharedPage|
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
    assert(s2.wf());
}

// ─────────────────────────── lifecycle wf-preservation ──────────────────────
pub proof fn lemma_add_vm_step_preserves_wf(s1: SwView, s2: SwView, vm: VmId)
    requires
        s1.wf(),
        SwView::add_vm_enabled(s1, vm),
        SwView::add_vm_step(s1, s2, vm),
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
    assert(s2.wf());
}

pub proof fn lemma_remove_vm_step_preserves_wf(s1: SwView, s2: SwView, vm: VmId)
    requires
        s1.wf(),
        SwView::remove_vm_enabled(s1, vm),
        SwView::remove_vm_step(s1, s2, vm),
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
    assert(s2.wf());
}

// ───────────────────── region → per-page step trace ─────────────────────────
// A region step is *defined* by set algebra; here we show it is realized by a
// trace of the atomic per-page steps.  Edge `j` of an insert trace is, for
// `i = j / 2`: assign region page `i` (even `j`) then map region entry `i` (odd
// `j`).  Interleaving assign-then-map keeps each `map`'s precondition (the target
// page is owned) discharged by the immediately preceding `assign`.
pub open spec fn insert_page_edge(s: SwView, t: SwView, region: Region, j: nat) -> bool {
    let i = (j / 2) as nat;
    if j % 2 == 0 {
        SwView::assign_page_step(s, t, region.vm, region.phys_page(i))
    } else {
        SwView::map_step(
            s,
            t,
            region.vm,
            region.guest_page(i),
            S2Entry { page: region.phys_page(i), access: region.access, generation: 0 },
        )
    }
}

/// Edge `j` of a remove trace: unmap region entry `i` (even `j`) then reclaim
/// region page `i` (odd `j`).
pub open spec fn remove_page_edge(s: SwView, t: SwView, region: Region, j: nat) -> bool {
    let i = (j / 2) as nat;
    if j % 2 == 0 {
        SwView::unmap_step(s, t, region.vm, region.guest_page(i))
    } else {
        SwView::reclaim_page_step(s, t, region.vm, region.phys_page(i))
    }
}

/// An `insert_region` step is realized by a `2*count + 1`-state trace of atomic
/// per-page steps, every intermediate state `wf`.  This is the bridge that lets
/// `insert_region` inherit the machine-level security result proved per-page in
/// `crate::machine::machine` (each edge refines a `MachineState` hypervisor step).
pub proof fn lemma_insert_region_trace(s1: SwView, s2: SwView, region: Region)
    requires
        s1.wf(),
        SwView::insert_region_enabled(s1, region),
        SwView::insert_region_step(s1, s2, region),
    ensures
        exists|trace: Seq<SwView>|
            #![auto]
            {
                &&& trace.len() == 2 * region.count + 1
                &&& trace[0] == s1
                &&& trace[trace.len() - 1] == s2
                &&& forall|j: int|
                    0 <= j < 2 * region.count ==> #[trigger] insert_page_edge(
                        trace[j],
                        trace[j + 1],
                        region,
                        j as nat,
                    )
                &&& forall|j: int| 0 <= j < trace.len() ==> (#[trigger] trace[j]).wf()
            },
{
    admit();
}

/// A `remove_region` step is realized by a `2*count + 1`-state trace of atomic
/// per-page steps, every intermediate state `wf`.
pub proof fn lemma_remove_region_trace(s1: SwView, s2: SwView, region: Region)
    requires
        s1.wf(),
        SwView::remove_region_enabled(s1, region),
        SwView::remove_region_step(s1, s2, region),
    ensures
        exists|trace: Seq<SwView>|
            #![auto]
            {
                &&& trace.len() == 2 * region.count + 1
                &&& trace[0] == s1
                &&& trace[trace.len() - 1] == s2
                &&& forall|j: int|
                    0 <= j < 2 * region.count ==> #[trigger] remove_page_edge(
                        trace[j],
                        trace[j + 1],
                        region,
                        j as nat,
                    )
                &&& forall|j: int| 0 <= j < trace.len() ==> (#[trigger] trace[j]).wf()
            },
{
    admit();
}

// ─────────────────────────── region wf-preservation ─────────────────────────
// Proved directly by set/map algebra (the trace lemmas are not needed for `wf`).
pub proof fn lemma_insert_region_step_preserves_wf(s1: SwView, s2: SwView, region: Region)
    requires
        s1.wf(),
        SwView::insert_region_enabled(s1, region),
        SwView::insert_region_step(s1, s2, region),
    ensures
        s2.wf(),
{
    let vm = region.vm;
    let pages = region.pages();
    let entries = region.entries();
    // `pages` are free in `s1` (enabled), hence in no VM's ownership set.
    assert forall|w: VmId, p: PhysPage|
        s1.all_vms.contains(w) && pages.contains(p) implies !s1.vm_owned[w].contains(p) by {
        assert(s1.hypervisor_owned.contains(p));  // enabled: pages ⊆ hypervisor_owned
    }
    // Each region entry targets one of `region`'s (now `vm`-owned) pages.
    assert forall|k: VmPageKey| #[trigger] entries.contains_key(k) implies pages.contains(
        entries[k].page,
    ) by {}

    // ownership_wf
    assert(s2.vm_owned.dom() =~= s2.all_vms);
    assert forall|a: VmId, b: VmId| #[trigger]
        s2.all_vms.contains(a) && #[trigger] s2.all_vms.contains(b) && a != b implies (forall|
        p: PhysPage,
    | #[trigger]
        s2.vm_owned[a].contains(p) ==> !s2.vm_owned[b].contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.vm_owned[a].contains(p) implies !s2.vm_owned[b].contains(p) by {
            if a == vm {
                if !pages.contains(p) {
                    assert(s1.vm_owned[vm].contains(p));  // p came from s1's set
                }
            } else if b == vm {
                assert(s1.vm_owned[a].contains(p));
            }
        }
    }
    assert forall|w: VmId| #[trigger] s2.all_vms.contains(w) implies (forall|p: PhysPage|
     #[trigger]
        s2.vm_owned[w].contains(p) ==> !s2.hypervisor_owned.contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.vm_owned[w].contains(p) implies !s2.hypervisor_owned.contains(p) by {
            if w != vm || !pages.contains(p) {
                assert(s1.vm_owned[w].contains(p));
            }
        }
    }
    // sharing_wf: shared_pages and all_vms unchanged.
    assert forall|e: SharedPage| #[trigger] s2.shared_pages.contains(e) implies (e.left != e.right
        && s2.all_vms.contains(e.left) && s2.all_vms.contains(e.right) && s2.shared_pages.contains(
        e.reverse(),
    )) by {
        assert(s1.shared_pages.contains(e));
    }
    // translation_wf
    assert forall|k: VmPageKey| #[trigger] s2.s2_map.contains_key(k) implies (s2.all_vms.contains(
        k.vm,
    ) && s2.owned_or_shared(k.vm, s2.s2_map[k].page)) by {
        if entries.contains_key(k) {
            // new entry: k.vm == vm, target ∈ pages ⊆ s2.vm_owned[vm]
            assert(pages.contains(entries[k].page));
        } else {
            // surviving entry: target stays owned (ownership only grew)
            assert(s1.s2_map.contains_key(k));
        }
    }
    assert(s2.wf());
}

pub proof fn lemma_remove_region_step_preserves_wf(s1: SwView, s2: SwView, region: Region)
    requires
        s1.wf(),
        SwView::remove_region_enabled(s1, region),
        SwView::remove_region_step(s1, s2, region),
    ensures
        s2.wf(),
{
    let vm = region.vm;
    let pages = region.pages();
    // After the reclaim no VM owns any of `pages`: `vm` gave them up, and (by `s1`
    // pairwise disjointness, since `pages ⊆ vm_owned[vm]`) no other VM had them.
    assert forall|w: VmId, p: PhysPage|
        s2.all_vms.contains(w) && pages.contains(p) implies !s2.vm_owned[w].contains(p) by {
        if w != vm {
            assert(s1.vm_owned[vm].contains(p));  // enabled: pages ⊆ vm_owned[vm]
        }
    }
    // ownership_wf
    assert(s2.vm_owned.dom() =~= s2.all_vms);
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
    assert forall|w: VmId| #[trigger] s2.all_vms.contains(w) implies (forall|p: PhysPage|
     #[trigger]
        s2.vm_owned[w].contains(p) ==> !s2.hypervisor_owned.contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.vm_owned[w].contains(p) implies !s2.hypervisor_owned.contains(p) by {
            assert(s1.vm_owned[w].contains(p));  // s2[w] ⊆ s1[w], so p ∉ s1.hypervisor_owned
            // and p ∉ pages (no VM owns a reclaimed page), so p ∉ s1.hyp ∪ pages
        }
    }
    // sharing_wf
    assert forall|e: SharedPage| #[trigger] s2.shared_pages.contains(e) implies (e.left != e.right
        && s2.all_vms.contains(e.left) && s2.all_vms.contains(e.right) && s2.shared_pages.contains(
        e.reverse(),
    )) by {
        assert(s1.shared_pages.contains(e));
    }
    // translation_wf: a surviving key is not in `region.entries()`, so by
    // pmem-exclusivity its target is not a reclaimed page and stays owned.
    assert forall|k: VmPageKey| #[trigger] s2.s2_map.contains_key(k) implies (s2.all_vms.contains(
        k.vm,
    ) && s2.owned_or_shared(k.vm, s2.s2_map[k].page)) by {
        assert(s1.s2_map.contains_key(k) && !region.entries().contains_key(k));
        assert(!pages.contains(s2.s2_map[k].page));  // pmem-exclusivity
    }
    assert(s2.wf());
}

} // verus!
