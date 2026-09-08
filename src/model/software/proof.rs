//! Proof obligations for the `SoftwareView` state machine.
//!
//! `wf` is an inductive invariant for the active per-page and lifecycle steps.
//! Region preservation is discharged by the software-refinement layer. This
//! module is `admit`-free.
//!
//! Families, in dependency order:
//! 1. **per-page `wf`-preservation** — each primitive step keeps `wf` (base cases).
//! 2. **lifecycle `wf`-preservation** — `add_vm` / `remove_vm`.
use vstd::prelude::*;

use super::SoftwareView;
use crate::model::types::{GuestPage, PhysPage, S2Entry, VmId, VmPageKey};

verus! {

// ─────────────────────────── per-page wf-preservation ───────────────────────
/// A combined CPU S2-Private map preserves classification separation and makes the
/// new translation valid by adding its target to the same VM atomically.
pub proof fn lemma_map_s2_private_step_preserves_wf(
    s1: SoftwareView,
    s2: SoftwareView,
    vm: VmId,
    gpa: GuestPage,
    entry: S2Entry,
)
    requires
        s1.wf(),
        SoftwareView::map_s2_private_step(s1, s2, vm, gpa, entry),
    ensures
        s2.wf(),
{
    let key = VmPageKey::new(vm, gpa);
    let page = entry.page;
    assert(s2.s2_private_pages.dom() =~= s2.all_vms);
    assert forall|a: VmId, b: VmId| #[trigger]
        s2.all_vms.contains(a) && #[trigger] s2.all_vms.contains(b) && a != b implies (forall|
        p: PhysPage,
    | #[trigger]
        s2.s2_private_pages[a].contains(p) ==> !s2.s2_private_pages[b].contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.s2_private_pages[a].contains(p) implies !s2.s2_private_pages[b].contains(p) by {
            if a == vm {
                if p != page {
                    assert(s1.s2_private_pages[vm].contains(p));
                }
            } else if b == vm {
                if p != page {
                    assert(s1.s2_private_pages[a].contains(p));
                }
            }
        }
    }
    assert forall|v: VmId| #[trigger] s2.all_vms.contains(v) implies (forall|p: PhysPage|
     #[trigger]
        s2.s2_private_pages[v].contains(p) ==> !s2.s2_shared_pages.contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.s2_private_pages[v].contains(p) implies !s2.s2_shared_pages.contains(p) by {
            if v == vm && p == page {
            } else {
                assert(s1.s2_private_pages[v].contains(p));
            }
        }
    }
    assert(s2.s2_classification_wf());
    assert forall|k: VmPageKey| #[trigger] s2.s2_map.contains_key(k) implies (s2.all_vms.contains(
        k.vm,
    ) && s2.s2_private_or_shared(k.vm, s2.s2_map[k].page)) by {
        if k == key {
            assert(s2.s2_private_pages[vm].contains(page));
        } else {
            assert(s1.s2_map.contains_key(k));
        }
    }
    assert(s2.translation_wf());
    assert forall|v1: VmId, v2: VmId| #[trigger]
        s2.all_vms.contains(v1) && #[trigger] s2.all_vms.contains(v2) && v1 != v2 implies (forall|
        p: PhysPage,
    | #[trigger]
        s2.iommu_private_pages[v1].contains(p) ==> !s2.s2_private_pages[v2].contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.iommu_private_pages[v1].contains(p) implies !s2.s2_private_pages[v2].contains(p) by {
            if v2 == vm && p == page {
                assert(!s1.iommu_private_pages[v1].contains(page));
                assert(false);
            } else if v2 == vm {
                if s2.s2_private_pages[v2].contains(p) {
                    assert(s1.s2_private_pages[vm].contains(p));
                    assert(s1.iommu_private_pages[v1].contains(p));
                }
            }
        }
    }
    assert forall|v: VmId| #[trigger] s2.all_vms.contains(v) implies (forall|p: PhysPage|
     #[trigger]
        s2.s2_private_pages[v].contains(p) ==> !s2.iommu_shared_pages.contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.s2_private_pages[v].contains(p) implies !s2.iommu_shared_pages.contains(p) by {
            if v == vm && p == page {
            } else {
                assert(s1.s2_private_pages[v].contains(p));
            }
        }
    }
    assert(s2.iommu_classification_wf());
    assert(s2.iommu_translation_wf());
}

/// A combined CPU S2-Private unmap preserves `wf`: its Private projection only shrinks,
/// and the no-surviving-alias guard keeps every remaining translation valid.
pub proof fn lemma_unmap_s2_private_step_preserves_wf(
    s1: SoftwareView,
    s2: SoftwareView,
    vm: VmId,
    gpa: GuestPage,
    page: PhysPage,
)
    requires
        s1.wf(),
        SoftwareView::unmap_s2_private_step(s1, s2, vm, gpa, page),
    ensures
        s2.wf(),
{
    assert(s2.s2_private_pages.dom() =~= s2.all_vms);
    assert forall|a: VmId, b: VmId| #[trigger]
        s2.all_vms.contains(a) && #[trigger] s2.all_vms.contains(b) && a != b implies (forall|
        p: PhysPage,
    | #[trigger]
        s2.s2_private_pages[a].contains(p) ==> !s2.s2_private_pages[b].contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.s2_private_pages[a].contains(p) implies !s2.s2_private_pages[b].contains(p) by {
            assert(s1.s2_private_pages[a].contains(p));
        }
    }
    assert forall|v: VmId| #[trigger] s2.all_vms.contains(v) implies (forall|p: PhysPage|
     #[trigger]
        s2.s2_private_pages[v].contains(p) ==> !s2.s2_shared_pages.contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.s2_private_pages[v].contains(p) implies !s2.s2_shared_pages.contains(p) by {
            assert(s1.s2_private_pages[v].contains(p));
        }
    }
    assert(s2.s2_classification_wf());
    assert forall|k: VmPageKey| #[trigger] s2.s2_map.contains_key(k) implies (s2.all_vms.contains(
        k.vm,
    ) && s2.s2_private_or_shared(k.vm, s2.s2_map[k].page)) by {
        assert(s1.s2_map.contains_key(k));
        assert(s2.s2_map[k].page != page);
    }
    assert(s2.translation_wf());
    assert forall|v1: VmId, v2: VmId| #[trigger]
        s2.all_vms.contains(v1) && #[trigger] s2.all_vms.contains(v2) && v1 != v2 implies (forall|
        p: PhysPage,
    | #[trigger]
        s2.iommu_private_pages[v1].contains(p) ==> !s2.s2_private_pages[v2].contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.iommu_private_pages[v1].contains(p) implies !s2.s2_private_pages[v2].contains(p) by {
            if s2.s2_private_pages[v2].contains(p) {
                assert(s1.s2_private_pages[v2].contains(p));
            }
        }
    }
    assert(s2.iommu_classification_wf());
    assert(s2.iommu_translation_wf());
}

/// A combined IOMMU-Private map preserves both CPU and DMA separation and
/// authorizes the new IOMMU translation in the same transition.
pub proof fn lemma_map_iommu_private_step_preserves_wf(
    s1: SoftwareView,
    s2: SoftwareView,
    vm: VmId,
    gpa: GuestPage,
    entry: S2Entry,
)
    requires
        s1.wf(),
        SoftwareView::map_iommu_private_step(s1, s2, vm, gpa, entry),
    ensures
        s2.wf(),
{
    let key = VmPageKey::new(vm, gpa);
    let page = entry.page;
    assert(s2.s2_classification_wf());
    assert(s2.translation_wf());
    assert(s2.iommu_private_pages.dom() =~= s2.all_vms);
    assert forall|a: VmId, b: VmId| #[trigger]
        s2.all_vms.contains(a) && #[trigger] s2.all_vms.contains(b) && a != b implies (forall|
        p: PhysPage,
    | #[trigger]
        s2.iommu_private_pages[a].contains(p) ==> !s2.iommu_private_pages[b].contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.iommu_private_pages[a].contains(p) implies !s2.iommu_private_pages[b].contains(p) by {
            if a == vm {
                if p != page {
                    assert(s1.iommu_private_pages[vm].contains(p));
                }
            } else if b == vm {
                if p != page {
                    assert(s1.iommu_private_pages[a].contains(p));
                }
            }
        }
    }
    assert forall|a: VmId, b: VmId| #[trigger]
        s2.all_vms.contains(a) && #[trigger] s2.all_vms.contains(b) && a != b implies (forall|
        p: PhysPage,
    | #[trigger]
        s2.iommu_private_pages[a].contains(p) ==> !s2.s2_private_pages[b].contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.iommu_private_pages[a].contains(p) implies !s2.s2_private_pages[b].contains(p) by {
            if a == vm && p == page {
            } else {
                assert(s1.iommu_private_pages[a].contains(p));
            }
        }
    }
    assert forall|v: VmId| #[trigger] s2.all_vms.contains(v) implies (forall|p: PhysPage|
     #[trigger]
        s2.iommu_private_pages[v].contains(p) ==> !s2.iommu_shared_pages.contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.iommu_private_pages[v].contains(p) implies !s2.iommu_shared_pages.contains(p) by {
            if v == vm && p == page {
            } else {
                assert(s1.iommu_private_pages[v].contains(p));
            }
        }
    }
    assert(s2.iommu_classification_wf());
    assert forall|k: VmPageKey| #[trigger] s2.iommu_s2_map.contains_key(k) implies (
    s2.all_vms.contains(k.vm) && s2.iommu_private_pages.contains_key(k.vm) && (
    s2.iommu_private_pages[k.vm].contains(s2.iommu_s2_map[k].page) || s2.iommu_shared_pages.contains(
        s2.iommu_s2_map[k].page,
    ))) by {
        if k == key {
            assert(s2.iommu_private_pages[vm].contains(page));
        } else {
            assert(s1.iommu_s2_map.contains_key(k));
        }
    }
    assert(s2.iommu_translation_wf());
}

/// A combined IOMMU-Private unmap preserves `wf`: its Private projection shrinks and
/// no surviving IOMMU translation targets the released page.
pub proof fn lemma_unmap_iommu_private_step_preserves_wf(
    s1: SoftwareView,
    s2: SoftwareView,
    vm: VmId,
    gpa: GuestPage,
    page: PhysPage,
)
    requires
        s1.wf(),
        SoftwareView::unmap_iommu_private_step(s1, s2, vm, gpa, page),
    ensures
        s2.wf(),
{
    assert(s2.s2_classification_wf());
    assert(s2.translation_wf());
    assert(s2.iommu_private_pages.dom() =~= s2.all_vms);
    assert forall|a: VmId, b: VmId| #[trigger]
        s2.all_vms.contains(a) && #[trigger] s2.all_vms.contains(b) && a != b implies ((forall|
        p: PhysPage,
    | #[trigger]
        s2.iommu_private_pages[a].contains(p) ==> !s2.iommu_private_pages[b].contains(p)) && (forall|p: PhysPage|
     #[trigger]
        s2.iommu_private_pages[a].contains(p) ==> !s2.s2_private_pages[b].contains(p))) by {
        assert forall|p: PhysPage| #[trigger]
            s2.iommu_private_pages[a].contains(p) implies !s2.iommu_private_pages[b].contains(p)
                && !s2.s2_private_pages[b].contains(p) by {
            assert(s1.iommu_private_pages[a].contains(p));
            if s2.iommu_private_pages[b].contains(p) {
                assert(s1.iommu_private_pages[b].contains(p));
            }
        }
    }
    assert forall|v: VmId| #[trigger] s2.all_vms.contains(v) implies (forall|p: PhysPage|
     #[trigger]
        s2.iommu_private_pages[v].contains(p) ==> !s2.iommu_shared_pages.contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.iommu_private_pages[v].contains(p) implies !s2.iommu_shared_pages.contains(p) by {
            assert(s1.iommu_private_pages[v].contains(p));
        }
    }
    assert(s2.iommu_classification_wf());
    assert forall|k: VmPageKey| #[trigger] s2.iommu_s2_map.contains_key(k) implies (
    s2.all_vms.contains(k.vm) && s2.iommu_private_pages.contains_key(k.vm) && (
    s2.iommu_private_pages[k.vm].contains(s2.iommu_s2_map[k].page) || s2.iommu_shared_pages.contains(
        s2.iommu_s2_map[k].page,
    ))) by {
        assert(s1.iommu_s2_map.contains_key(k));
        assert(s2.iommu_s2_map[k].page != page);
    }
    assert(s2.iommu_translation_wf());
}

/// Adding a CPU shared mapping preserves `wf`: the target is excluded
/// from every private projection and becomes shared in the same step.
pub proof fn lemma_map_s2_shared_step_preserves_wf(
    s1: SoftwareView,
    s2: SoftwareView,
    vm: VmId,
    gpa: GuestPage,
    entry: S2Entry,
)
    requires
        s1.wf(),
        SoftwareView::map_s2_shared_step(s1, s2, vm, gpa, entry),
    ensures
        s2.wf(),
{
    let key = VmPageKey::new(vm, gpa);
    let page = entry.page;
    assert(s2.s2_private_pages.dom() =~= s2.all_vms);
    assert forall|a: VmId, b: VmId| #[trigger]
        s2.all_vms.contains(a) && #[trigger] s2.all_vms.contains(b) && a != b implies (forall|
        p: PhysPage,
    | #[trigger]
        s2.s2_private_pages[a].contains(p) ==> !s2.s2_private_pages[b].contains(p)) by {}
    assert forall|v: VmId| #[trigger] s2.all_vms.contains(v) implies (forall|p: PhysPage|
     #[trigger]
        s2.s2_private_pages[v].contains(p) ==> !s2.s2_shared_pages.contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.s2_private_pages[v].contains(p) implies !s2.s2_shared_pages.contains(p) by {
            if p == page {
                assert(!s1.s2_private_pages[v].contains(page));
                assert(false);
            }
        }
    }
    assert(s2.s2_classification_wf());
    assert forall|k: VmPageKey| #[trigger] s2.s2_map.contains_key(k) implies (s2.all_vms.contains(
        k.vm,
    ) && s2.s2_private_or_shared(k.vm, s2.s2_map[k].page)) by {
        if k == key {
            assert(s2.s2_shared_pages.contains(page));
        } else {
            assert(s1.s2_map.contains_key(k));
        }
    }
    assert(s2.translation_wf());
    assert(s2.iommu_classification_wf());
    assert(s2.iommu_translation_wf());
}

/// Removing a CPU shared mapping preserves `wf`; the target leaves the
/// shared projection only when no surviving CPU translation needs it.
pub proof fn lemma_unmap_s2_shared_step_preserves_wf(
    s1: SoftwareView,
    s2: SoftwareView,
    vm: VmId,
    gpa: GuestPage,
)
    requires
        s1.wf(),
        SoftwareView::unmap_s2_shared_step(s1, s2, vm, gpa),
    ensures
        s2.wf(),
{
    let key = VmPageKey::new(vm, gpa);
    let page = s1.s2_map[key].page;
    let post_map = s1.s2_map.remove(key);
    let aliased = exists|k: VmPageKey| #[trigger]
        post_map.contains_key(k) && post_map[k].page == page;
    assert(s2.s2_classification_wf());
    assert forall|k: VmPageKey| #[trigger] s2.s2_map.contains_key(k) implies (s2.all_vms.contains(
        k.vm,
    ) && s2.s2_private_or_shared(k.vm, s2.s2_map[k].page)) by {
        assert(s1.s2_map.contains_key(k));
        if s2.s2_map[k].page == page {
            assert(aliased) by {
                assert(post_map.contains_key(k) && post_map[k].page == page);
            }
            assert(s2.s2_shared_pages == s1.s2_shared_pages);
        }
    }
    assert(s2.translation_wf());
    assert(s2.iommu_classification_wf());
    assert(s2.iommu_translation_wf());
}

/// Adding an IOMMU shared mapping preserves `wf`: the target is absent
/// from every private projection and becomes IOMMU-Shared atomically.
pub proof fn lemma_map_iommu_shared_step_preserves_wf(
    s1: SoftwareView,
    s2: SoftwareView,
    vm: VmId,
    gpa: GuestPage,
    entry: S2Entry,
)
    requires
        s1.wf(),
        SoftwareView::map_iommu_shared_step(s1, s2, vm, gpa, entry),
    ensures
        s2.wf(),
{
    let key = VmPageKey::new(vm, gpa);
    let page = entry.page;
    assert(s2.s2_classification_wf());
    assert(s2.translation_wf());
    assert(s2.iommu_private_pages.dom() =~= s2.all_vms);
    assert forall|a: VmId, b: VmId| #[trigger]
        s2.all_vms.contains(a) && #[trigger] s2.all_vms.contains(b) && a != b implies ((forall|
        p: PhysPage,
    | #[trigger]
        s2.iommu_private_pages[a].contains(p) ==> !s2.iommu_private_pages[b].contains(p)) && (forall|p: PhysPage|
     #[trigger]
        s2.iommu_private_pages[a].contains(p) ==> !s2.s2_private_pages[b].contains(p))) by {}
    assert forall|v: VmId| #[trigger] s2.all_vms.contains(v) implies (forall|p: PhysPage|
     #[trigger]
        s2.iommu_private_pages[v].contains(p) ==> !s2.iommu_shared_pages.contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.iommu_private_pages[v].contains(p) implies !s2.iommu_shared_pages.contains(p) by {
            if p == page {
                assert(!s1.iommu_private_pages[v].contains(page));
                assert(false);
            }
        }
    }
    assert forall|v: VmId| #[trigger] s2.all_vms.contains(v) implies (forall|p: PhysPage|
     #[trigger]
        s2.s2_private_pages[v].contains(p) ==> !s2.iommu_shared_pages.contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.s2_private_pages[v].contains(p) implies !s2.iommu_shared_pages.contains(p) by {
            if p == page {
                assert(!s1.s2_private_pages[v].contains(page));
                assert(false);
            }
        }
    }
    assert(s2.iommu_classification_wf());
    assert forall|k: VmPageKey| #[trigger] s2.iommu_s2_map.contains_key(k) implies (
    s2.all_vms.contains(k.vm) && s2.iommu_private_pages.contains_key(k.vm) && (
    s2.iommu_private_pages[k.vm].contains(s2.iommu_s2_map[k].page) || s2.iommu_shared_pages.contains(
        s2.iommu_s2_map[k].page,
    ))) by {
        if k == key {
            assert(s2.iommu_shared_pages.contains(page));
        } else {
            assert(s1.iommu_s2_map.contains_key(k));
        }
    }
    assert(s2.iommu_translation_wf());
}

/// Removing an IOMMU shared mapping preserves `wf`; the target leaves
/// `iommu_shared_pages` only when no surviving IOMMU translation needs it.
pub proof fn lemma_unmap_iommu_shared_step_preserves_wf(
    s1: SoftwareView,
    s2: SoftwareView,
    vm: VmId,
    gpa: GuestPage,
)
    requires
        s1.wf(),
        SoftwareView::unmap_iommu_shared_step(s1, s2, vm, gpa),
    ensures
        s2.wf(),
{
    let key = VmPageKey::new(vm, gpa);
    let page = s1.iommu_s2_map[key].page;
    let post_map = s1.iommu_s2_map.remove(key);
    let aliased = exists|k: VmPageKey| #[trigger]
        post_map.contains_key(k) && post_map[k].page == page;
    assert(s2.s2_classification_wf());
    assert(s2.translation_wf());
    assert(s2.iommu_classification_wf());
    assert forall|k: VmPageKey| #[trigger] s2.iommu_s2_map.contains_key(k) implies (
    s2.all_vms.contains(k.vm) && s2.iommu_private_pages.contains_key(k.vm) && (
    s2.iommu_private_pages[k.vm].contains(s2.iommu_s2_map[k].page) || s2.iommu_shared_pages.contains(
        s2.iommu_s2_map[k].page,
    ))) by {
        assert(s1.iommu_s2_map.contains_key(k));
        if s2.iommu_s2_map[k].page == page {
            assert(aliased) by {
                assert(post_map.contains_key(k) && post_map[k].page == page);
            }
            assert(s2.iommu_shared_pages == s1.iommu_shared_pages);
        }
    }
    assert(s2.iommu_translation_wf());
}

// ─────────────────────────── lifecycle wf-preservation ──────────────────────
/// Adding a fresh, empty VM preserves every classification and translation invariant.
pub proof fn lemma_add_vm_step_preserves_wf(s1: SoftwareView, s2: SoftwareView, vm: VmId)
    requires
        s1.wf(),
        SoftwareView::add_vm_enabled(s1, vm),
        SoftwareView::add_vm_step(s1, s2, vm),
    ensures
        s2.wf(),
{
    // The new VM has no Private pages; `all_vms` only grows.
    assert(s2.s2_private_pages.dom() =~= s2.all_vms);
    assert forall|a: VmId, b: VmId| #[trigger]
        s2.all_vms.contains(a) && #[trigger] s2.all_vms.contains(b) && a != b implies (forall|
        p: PhysPage,
    | #[trigger]
        s2.s2_private_pages[a].contains(p) ==> !s2.s2_private_pages[b].contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.s2_private_pages[a].contains(p) implies !s2.s2_private_pages[b].contains(p) by {
            if a != vm && b != vm {
                assert(s1.s2_private_pages[a].contains(p));
            }
        }
    }
    assert forall|k: VmPageKey| #[trigger] s2.s2_map.contains_key(k) implies (s2.all_vms.contains(
        k.vm,
    ) && s2.s2_private_or_shared(k.vm, s2.s2_map[k].page)) by {
        assert(s1.s2_map.contains_key(k));
    }
    // IOMMU: the fresh VM has no Private pages (`iommu_private_pages[vm] = ∅`) and has no IOMMU
    // entries, so every `iommu_wf` clause extends to the larger `all_vms`.
    assert(s1.iommu_wf());
    assert(s2.iommu_private_pages.dom() =~= s2.all_vms);
    assert forall|v1: VmId, v2: VmId| #[trigger]
        s2.all_vms.contains(v1) && #[trigger] s2.all_vms.contains(v2) && v1 != v2 implies ((forall|
        p: PhysPage,
    | #[trigger]
        s2.iommu_private_pages[v1].contains(p) ==> !s2.iommu_private_pages[v2].contains(p)) && (forall|p: PhysPage|
     #[trigger]
        s2.iommu_private_pages[v1].contains(p) ==> !s2.s2_private_pages[v2].contains(p))) by {
        if v1 != vm && v2 != vm {
            assert(s1.all_vms.contains(v1) && s1.all_vms.contains(v2));
        }
    }
    assert forall|w: VmId| #[trigger] s2.all_vms.contains(w) implies (forall|p: PhysPage|
     #[trigger]
        s2.iommu_private_pages[w].contains(p) ==> !s2.iommu_shared_pages.contains(p)) by {
        if w != vm {
            assert(s1.all_vms.contains(w));
        }
    }
    assert forall|k: VmPageKey| #[trigger] s2.iommu_s2_map.contains_key(k) implies (
    s2.all_vms.contains(k.vm) && s2.iommu_private_pages.contains_key(k.vm) && (
    s2.iommu_private_pages[k.vm].contains(s2.iommu_s2_map[k].page) || s2.iommu_shared_pages.contains(
        s2.iommu_s2_map[k].page,
    ))) by {
        assert(s1.iommu_s2_map.contains_key(k));  // ⇒ k.vm ∈ s1.all_vms, so k.vm != vm (fresh)
    }
    assert(s2.iommu_wf());
    assert(s2.wf());
}

/// Removing a VM with no Private pages or mappings preserves the invariants of
/// all remaining VMs.
pub proof fn lemma_remove_vm_step_preserves_wf(s1: SoftwareView, s2: SoftwareView, vm: VmId)
    requires
        s1.wf(),
        SoftwareView::remove_vm_enabled(s1, vm),
        SoftwareView::remove_vm_step(s1, s2, vm),
    ensures
        s2.wf(),
{
    // `vm` (owning and mapping nothing) is dropped; the rest
    // of the state is unchanged, so every clause carries over to the smaller `all_vms`.
    assert(s2.s2_private_pages.dom() =~= s2.all_vms);
    assert forall|a: VmId, b: VmId| #[trigger]
        s2.all_vms.contains(a) && #[trigger] s2.all_vms.contains(b) && a != b implies (forall|
        p: PhysPage,
    | #[trigger]
        s2.s2_private_pages[a].contains(p) ==> !s2.s2_private_pages[b].contains(p)) by {
        assert forall|p: PhysPage| #[trigger]
            s2.s2_private_pages[a].contains(p) implies !s2.s2_private_pages[b].contains(p) by {
            assert(s1.s2_private_pages[a].contains(p));
        }
    }
    assert forall|k: VmPageKey| #[trigger] s2.s2_map.contains_key(k) implies (s2.all_vms.contains(
        k.vm,
    ) && s2.s2_private_or_shared(k.vm, s2.s2_map[k].page)) by {
        assert(s1.s2_map.contains_key(k));
    }
    // IOMMU: `vm` has no Private pages or mappings (enabledness), so dropping it keeps
    // every `iommu_wf` clause on the smaller `all_vms`.
    assert(s1.iommu_wf());
    assert(s2.iommu_private_pages.dom() =~= s2.all_vms);
    assert forall|v1: VmId, v2: VmId| #[trigger]
        s2.all_vms.contains(v1) && #[trigger] s2.all_vms.contains(v2) && v1 != v2 implies ((forall|
        p: PhysPage,
    | #[trigger]
        s2.iommu_private_pages[v1].contains(p) ==> !s2.iommu_private_pages[v2].contains(p)) && (forall|p: PhysPage|
     #[trigger]
        s2.iommu_private_pages[v1].contains(p) ==> !s2.s2_private_pages[v2].contains(p))) by {
        assert(s1.all_vms.contains(v1) && s1.all_vms.contains(v2));
    }
    assert forall|w: VmId| #[trigger] s2.all_vms.contains(w) implies (forall|p: PhysPage|
     #[trigger]
        s2.iommu_private_pages[w].contains(p) ==> !s2.iommu_shared_pages.contains(p)) by {
        assert(s1.all_vms.contains(w));
    }
    assert forall|k: VmPageKey| #[trigger] s2.iommu_s2_map.contains_key(k) implies (
    s2.all_vms.contains(k.vm) && s2.iommu_private_pages.contains_key(k.vm) && (
    s2.iommu_private_pages[k.vm].contains(s2.iommu_s2_map[k].page) || s2.iommu_shared_pages.contains(
        s2.iommu_s2_map[k].page,
    ))) by {
        assert(s1.iommu_s2_map.contains_key(k));
        assert(k.vm != vm);  // enabling: no IOMMU entry names `vm`
    }
    assert(s2.iommu_wf());
    assert(s2.wf());
}

} // verus!
