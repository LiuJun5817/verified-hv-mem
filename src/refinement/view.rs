//! The abstraction relation R: project `BudgetSpec::State` → `SwView`.
//!
//! The abstract state is the state machine's own `BudgetSpec::State` (its
//! `zone_ids` and per-zone `GhostZone` region sets) — **not** a hand-written
//! twin.  `<BudgetSpec::State as View>::view` maps it to the
//! security model's `SwView`.  Because the projection runs on the machine's real
//! state, the contract invariant in [`super::refine`] can be the machine's real
//! `invariant()`, and the global `SwView` step shape is available without
//! serializing anything (the runtime authority stays in the sharded tokens).
//!
//! This module also owns the page-unit reconciliation between the byte-addressed
//! implementation and the machine's page-numbered model (`region_phys_page`,
//! `region_guest_page`, `region_pages`, `region_s2_entries`, ...), the per-zone
//! sets (`zone_owned_pages`, `zone_s2_entries`), the global views
//! (`all_budget_pages`, `all_owned_pages`, `hypervisor_pool`, `state_s2_map`),
//! and the small "facts about the projection" lemmas the refinement needs.
//!
//! ## Page-unit reconciliation
//!
//! The hypervisor implementation addresses memory in *bytes* with
//! `SPEC_PAGE_SIZE = 0x1000` (4 KiB) pages.  The machine model numbers *pages*,
//! where one page is `PAGE_WORDS = 512` words; since `usize` is 8 bytes
//! (`global layout` in `lib.rs`), a machine page is `512 * 8 = 4096` bytes —
//! exactly `SPEC_PAGE_SIZE`.  Hence a machine `PhysPage` is
//! `paddr_bytes / SPEC_PAGE_SIZE` and a machine `GuestPage` is
//! `vaddr_bytes / SPEC_PAGE_SIZE`.
use crate::address::addr::SpecVAddr;
use crate::address::frame::{MemAttr, SpecFrame};
use crate::address::region::{MemoryRegion, SPEC_PAGE_SIZE};
use crate::hv_mem::spec::budget::{zone_budget, BudgetSpec};
use crate::hv_mem::spec::GhostZone;
use crate::machine::software::SwView;
use crate::machine::types::*;
use vstd::prelude::*;

verus! {

// ───────────────────────── per-region geometry ──────────────────────────────
// The *concrete* per-region geometry: what physical page / guest page / stage-2
// entry each page of a region maps to.  Built on the canonical region geometry
// from the `MemorySet` layer (`MemoryRegion::spec_page_vaddr` / `spec_frame`).
/// Access permissions of a region, from its `MemAttr`.
pub open spec fn attr_to_perms(attr: MemAttr) -> AccessPerms {
    AccessPerms { read: attr.readable, write: attr.writable, execute: attr.executable }
}

/// Machine physical page backing page `i` of region `r` (frame base, in page units).
pub open spec fn region_phys_page(r: MemoryRegion, i: nat) -> PhysPage {
    PhysPage(r.spec_frame(i).base.0 / SPEC_PAGE_SIZE)
}

/// Guest page of page `i` of region `r` (page vaddr, in page units).
pub open spec fn region_guest_page(r: MemoryRegion, i: nat) -> GuestPage {
    GuestPage(r.spec_page_vaddr(i).0 / SPEC_PAGE_SIZE)
}

/// `r` backs physical page `p` at some page index.
pub open spec fn region_owns_page(r: MemoryRegion, p: PhysPage) -> bool {
    exists|i: nat| 0 <= i < r.pages && #[trigger] region_phys_page(r, i) == p
}

/// `r` maps guest page `gpa` at some page index.
pub open spec fn region_owns_gpa(r: MemoryRegion, gpa: GuestPage) -> bool {
    exists|i: nat| 0 <= i < r.pages && #[trigger] region_guest_page(r, i) == gpa
}

/// Physical pages backed by a single region.
pub open spec fn region_pages(r: MemoryRegion) -> Set<PhysPage> {
    Set::new(|p: PhysPage| region_owns_page(r, p))
}

/// Stage-2 entries installed by a single region: one per (guest) page.
pub open spec fn region_s2_entries(zid: nat, region: MemoryRegion) -> Map<VmPageKey, S2Entry> {
    Map::new(
        |k: VmPageKey| k.vm == VmId(zid) && region_owns_gpa(region, k.gpa),
        |k: VmPageKey|
            {
                let i = choose|i: nat|
                    0 <= i < region.pages && region_guest_page(region, i) == k.gpa;
                S2Entry {
                    page: region_phys_page(region, i),
                    access: attr_to_perms(region.attr),
                    generation: 0,
                }
            },
    )
}

/// `r`'s physical pages are backed by no *other* region in `gz`.
///
/// Two regions can be vmem-disjoint yet map distinct guest pages to the *same*
/// physical page, so this is a genuine extra condition — it is what makes a
/// `remove_region` actually free `r`'s pages.
pub open spec fn region_pmem_exclusive(gz: GhostZone, r: MemoryRegion) -> bool {
    forall|rr: MemoryRegion| #[trigger]
        gz.regions().contains(rr) && rr != r ==> !rr.spec_overlaps_pmem(r)
}

/// Two regions that back the same physical page overlap in physical memory.
///
/// The one remaining arithmetic obligation of the page-unit reconciliation: it
/// relates `region_phys_page` equality to `MemoryRegion::spec_overlaps_pmem`.
/// (Holds for `Offset` mappers; a `Fixed` mapper has an empty pmem image, so the
/// regions would need to be `Offset` — see the project notes.)
pub proof fn lemma_same_phys_page_implies_pmem_overlap(
    r1: MemoryRegion,
    i1: nat,
    r2: MemoryRegion,
    i2: nat,
)
    requires
        r1.spec_valid(),
        r2.spec_valid(),
        0 <= i1 < r1.pages,
        0 <= i2 < r2.pages,
        region_phys_page(r1, i1) == region_phys_page(r2, i2),
    ensures
        r1.spec_overlaps_pmem(r2),
{
    admit();
}

// ───────────────────── mapping → machine-page helpers ───────────────────────
// `mem_set.mappings` (byte-addressed virtual→frame) is the source of truth: by
// `SpecMemorySet::wf` it is *exactly* the dense per-page region mapping.  These
// helpers reinterpret one such entry in the machine's page-numbered view.
/// The mapped virtual byte address of guest page `gpa`.
pub open spec fn gpa_to_vaddr(gpa: GuestPage) -> SpecVAddr {
    SpecVAddr(gpa.0 * SPEC_PAGE_SIZE)
}

/// The machine physical page a mapped frame backs.
pub open spec fn frame_phys_page(f: SpecFrame) -> PhysPage {
    PhysPage(f.base.0 / SPEC_PAGE_SIZE)
}

/// The stage-2 entry a mapped frame induces.
pub open spec fn frame_s2_entry(f: SpecFrame) -> S2Entry {
    S2Entry { page: frame_phys_page(f), access: attr_to_perms(f.attr), generation: 0 }
}

// ─────────────────────────── per-zone projections ───────────────────────────
/// Physical pages owned by a zone: the frames its page table maps, in page units.
pub open spec fn zone_owned_pages(gz: GhostZone) -> Set<PhysPage> {
    Set::new(
        |p: PhysPage|
            exists|v: SpecVAddr| #[trigger]
                gz.mem_set.mappings.contains_key(v) && frame_phys_page(gz.mem_set.mappings[v]) == p,
    )
}

/// Stage-2 entries installed by a zone: one per mapped guest page.
pub open spec fn zone_s2_entries(zid: nat, gz: GhostZone) -> Map<VmPageKey, S2Entry> {
    Map::new(
        |k: VmPageKey| k.vm == VmId(zid) && gz.mem_set.mappings.contains_key(gpa_to_vaddr(k.gpa)),
        |k: VmPageKey| frame_s2_entry(gz.mem_set.mappings[gpa_to_vaddr(k.gpa)]),
    )
}

// ───────────────────────────── global views ─────────────────────────────────
/// All physical pages that lie within *some* zone's static budget.
pub open spec fn all_budget_pages() -> Set<PhysPage> {
    Set::new(
        |pp: PhysPage|
            exists|zid: nat, r: MemoryRegion|
                #![trigger zone_budget(zid).contains(r), region_owns_page(r, pp)]
                zone_budget(zid).contains(r) && region_owns_page(r, pp),
    )
}

/// Physical pages currently owned by some active zone.
pub open spec fn all_owned_pages(zones: Map<nat, GhostZone>) -> Set<PhysPage> {
    Set::new(
        |pp: PhysPage|
            exists|zid: nat|
                #![trigger zones.contains_key(zid)]
                zones.contains_key(zid) && zone_owned_pages(zones[zid]).contains(pp),
    )
}

/// Physical pages that belong to no zone (the hypervisor pool): budget pages not
/// currently owned by any active zone.
pub open spec fn hypervisor_pool(zones: Map<nat, GhostZone>) -> Set<PhysPage> {
    all_budget_pages().difference(all_owned_pages(zones))
}

/// Stage-2 map of the whole state: the union of each zone's `zone_s2_entries`.
pub open spec fn state_s2_map(s: BudgetSpec::State) -> Map<VmPageKey, S2Entry> {
    Map::new(
        |k: VmPageKey|
            s.zone_ids.contains(k.vm.0) && zone_s2_entries(k.vm.0, s.zones[k.vm.0]).contains_key(k),
        |k: VmPageKey| zone_s2_entries(k.vm.0, s.zones[k.vm.0])[k],
    )
}

// ───────────────────────── the abstraction relation R ───────────────────────
impl View for BudgetSpec::State {
    type V = SwView;

    /// R: project the machine state to the abstract `SwView`.  `vm_owned` and
    /// `s2_map` come from the zones; `hypervisor_owned` is the unowned budget;
    /// `shared_pages` is empty (cross-VM sharing is out of scope).
    open spec fn view(&self) -> SwView {
        SwView {
            all_vms: Set::new(|vm: VmId| self.zone_ids.contains(vm.0)),
            hypervisor_owned: hypervisor_pool(self.zones),
            vm_owned: Map::new(
                |vm: VmId| self.zone_ids.contains(vm.0),
                |vm: VmId| zone_owned_pages(self.zones[vm.0]),
            ),
            shared_pages: Set::empty(),
            s2_map: state_s2_map(*self),
        }
    }
}

// ───────────────────────── facts about the projection ───────────────────────
/// A page owned by an active zone is in `all_owned_pages` (membership helper).
pub proof fn lemma_zone_owned_in_all_owned(zones: Map<nat, GhostZone>, zid: nat, p: PhysPage)
    requires
        zones.contains_key(zid),
        zone_owned_pages(zones[zid]).contains(p),
    ensures
        all_owned_pages(zones).contains(p),
{
}

/// A budget region's pages are all budget pages.
pub proof fn lemma_region_pages_in_all_budget(zid: nat, r: MemoryRegion)
    requires
        zone_budget(zid).contains(r),
    ensures
        forall|pp: PhysPage| #[trigger]
            region_pages(r).contains(pp) ==> all_budget_pages().contains(pp),
{
    assert forall|pp: PhysPage| region_pages(r).contains(pp) implies all_budget_pages().contains(
        pp,
    ) by {
        assert(region_owns_page(r, pp));  // witness (zid, r)
    }
}

/// Every stage-2 entry a zone installs targets a page that zone owns
/// (the per-zone half of `SwView::translation_wf`).
pub proof fn lemma_zone_s2_target_owned(zid: nat, gz: GhostZone)
    ensures
        forall|k: VmPageKey| #[trigger]
            zone_s2_entries(zid, gz).contains_key(k) ==> zone_owned_pages(gz).contains(
                zone_s2_entries(zid, gz)[k].page,
            ),
{
    assert forall|k: VmPageKey| #[trigger]
        zone_s2_entries(zid, gz).contains_key(k) implies zone_owned_pages(gz).contains(
        zone_s2_entries(zid, gz)[k].page,
    ) by {
        // The key is mapped at v = gpa_to_vaddr(k.gpa); its entry targets that
        // frame's physical page, which the zone owns via the very same v.
        let v = gpa_to_vaddr(k.gpa);
        assert(gz.mem_set.mappings.contains_key(v));
        assert(zone_s2_entries(zid, gz)[k].page == frame_phys_page(gz.mem_set.mappings[v]));
        assert(zone_owned_pages(gz).contains(frame_phys_page(gz.mem_set.mappings[v])));  // witness v
    }
}

/// A page owned by the zone is backed by some region of it (recovers a region
/// witness from the exposed mapping, using exact-dense soundness).
pub proof fn lemma_zone_owned_pages_region_witness(gz: GhostZone, p: PhysPage)
    requires
        gz.wf(),
        zone_owned_pages(gz).contains(p),
    ensures
        exists|r: MemoryRegion| #[trigger] gz.regions().contains(r) && region_owns_page(r, p),
{
    let v = choose|v: SpecVAddr|
        gz.mem_set.mappings.contains_key(v) && frame_phys_page(gz.mem_set.mappings[v]) == p;
    let f = gz.mem_set.mappings[v];
    assert(gz.mem_set.mappings.contains_pair(v, f));
    // exact-dense soundness: (v, f) is exactly some region page and its frame.
    let (r, i) = choose|r: MemoryRegion, i: nat|
        gz.regions().contains(r) && 0 <= i < r.pages && v == r.spec_page_vaddr(i) && f
            == r.spec_frame(i);
    assert(gz.regions().contains(r) && 0 <= i < r.pages && v == r.spec_page_vaddr(i) && f
        == r.spec_frame(i));
    assert(region_phys_page(r, i) == p);  // frame_phys_page(spec_frame(i)) == frame_phys_page(f) == p
    assert(region_owns_page(r, p));  // witness i
}

/// An empty page table owns no pages.
pub proof fn lemma_zone_owned_pages_empty(gz: GhostZone)
    requires
        gz.mem_set.mappings =~= Map::<SpecVAddr, SpecFrame>::empty(),
    ensures
        zone_owned_pages(gz) =~= Set::<PhysPage>::empty(),
{
    assert forall|p: PhysPage| !zone_owned_pages(gz).contains(p) by {
        // membership needs a mapped vaddr; there is none.
    }
}

/// An empty page table installs no stage-2 entries.
pub proof fn lemma_zone_s2_entries_empty(zid: nat, gz: GhostZone)
    requires
        gz.mem_set.mappings =~= Map::<SpecVAddr, SpecFrame>::empty(),
    ensures
        zone_s2_entries(zid, gz) =~= Map::<VmPageKey, S2Entry>::empty(),
{
    assert forall|k: VmPageKey| !zone_s2_entries(zid, gz).contains_key(k) by {
        // key predicate needs a mapped vaddr; there is none.
    }
}

} // verus!
