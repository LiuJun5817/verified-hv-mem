//! Proof obligations for the `SwView` state machine — **SKETCH**.
//!
//! Statements only: every proof body below is an [`admit`]`()` placeholder, to be
//! discharged in future work.  Only **two** granularities exist — atomic per-page
//! steps and region steps — so there is a single decomposition.  Families, in
//! dependency order:
//!
//! 1. **per-page `wf`-preservation** — each primitive step keeps the `wf`
//!    invariant.  These are the genuine base cases.
//! 2. **region → per-page trace** — each region step (set algebra) is realized by
//!    a trace of atomic per-page steps, every intermediate state `wf`.  This is
//!    the bridge that lets a region operation inherit the machine-level security
//!    result proved per-page in `crate::machine::machine` (`SW + HW ⟹ Machine`).
//! 3. **region `wf`-preservation** — corollary of the trace lemmas.
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
    admit();  // TODO: translation_wf — new entry targets an owned/shared page.
}

pub proof fn lemma_unmap_step_preserves_wf(s1: SwView, s2: SwView, vm: VmId, gpa: GuestPage)
    requires
        s1.wf(),
        SwView::unmap_step(s1, s2, vm, gpa),
    ensures
        s2.wf(),
{
    admit();  // TODO: removing a key only shrinks s2_map.
}

pub proof fn lemma_assign_page_step_preserves_wf(s1: SwView, s2: SwView, vm: VmId, page: PhysPage)
    requires
        s1.wf(),
        SwView::assign_page_step(s1, s2, vm, page),
    ensures
        s2.wf(),
{
    admit();  // TODO: page leaves the pool ⇒ ownership stays disjoint.
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
    admit();  // TODO: quiescence ⇒ translation_wf survives the reclaim.
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
    admit();
}

pub proof fn lemma_remove_vm_step_preserves_wf(s1: SwView, s2: SwView, vm: VmId)
    requires
        s1.wf(),
        SwView::remove_vm_enabled(s1, vm),
        SwView::remove_vm_step(s1, s2, vm),
    ensures
        s2.wf(),
{
    admit();
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
// Corollaries of the trace lemmas: `s2 == trace.last()` and every trace state is
// `wf`, so in particular `s2.wf()`.
pub proof fn lemma_insert_region_step_preserves_wf(s1: SwView, s2: SwView, region: Region)
    requires
        s1.wf(),
        SwView::insert_region_enabled(s1, region),
        SwView::insert_region_step(s1, s2, region),
    ensures
        s2.wf(),
{
    admit();
}

pub proof fn lemma_remove_region_step_preserves_wf(s1: SwView, s2: SwView, region: Region)
    requires
        s1.wf(),
        SwView::remove_region_enabled(s1, region),
        SwView::remove_region_step(s1, s2, region),
    ensures
        s2.wf(),
{
    admit();
}

} // verus!
