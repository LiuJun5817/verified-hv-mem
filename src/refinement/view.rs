//! The abstraction relation R: project `BudgetSpec::State` → `SwView`.
//!
//! `<BudgetSpec::State as View>::view` maps the state machine's own state (its
//! `zone_ids` and per-zone `GhostZone` region sets) to the security model's
//! `SwView`.  Projecting the machine's real state lets [`super::refine`] use the
//! machine's real `invariant()` as the contract invariant.
//!
//! This module defines the projection and its building blocks:
//! - per-region geometry (`region_phys_page`, `region_guest_page`,
//!   `region_pages`, `region_s2_entries`);
//! - per-zone projections (`zone_owned_pages`, `zone_s2_entries`);
//! - global views (`all_budget_pages`, `all_owned_pages`, `hypervisor_pool`,
//!   `state_s2_map`);
//! - the `View` impl and the supporting projection lemmas.
//!
//! ## Page-unit reconciliation
//!
//! The implementation addresses memory in *bytes* (`SPEC_PAGE_SIZE = 0x1000`); the
//! machine model numbers *pages* of `PAGE_WORDS = 512` words = 4096 bytes =
//! `SPEC_PAGE_SIZE`.  So a `PhysPage` is `paddr / SPEC_PAGE_SIZE` and a `GuestPage`
//! is `vaddr / SPEC_PAGE_SIZE`.  Because the page size is a *constant*, the
//! page↔byte arithmetic below is linear and Verus discharges it with no proof body.
use crate::address::addr::SpecVAddr;
use crate::address::frame::{MemAttr, SpecFrame};
use crate::address::region::{MemoryRegion, SPEC_PAGE_SIZE};
use crate::hv_mem::spec::budget::{
    zone_budget, zone_budget_in_all_regions, zone_budget_pairwise_disjoint, BudgetSpec,
};
use crate::hv_mem::spec::{all_regions, all_regions_disjoint, GhostZone};
use crate::machine::software::{Region, SwView};
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

/// `r`'s physical pages are backed by no *other* region in `gz` — the condition
/// under which removing `r` actually frees its pages.
pub open spec fn region_pmem_exclusive(gz: GhostZone, r: MemoryRegion) -> bool {
    forall|rr: MemoryRegion| #[trigger]
        gz.regions().contains(rr) && rr != r ==> !rr.spec_overlaps_pmem(r)
}

// ───────────────────────── per-region page arithmetic ───────────────────────
// Page index ↔ physical/guest page is linear in the *constant* page size, so the
// facts below are linear arithmetic that Verus discharges with no proof body.
/// The physical page backing region page `i` is **linear** in `i`: the region's
/// page-aligned base page (`pstart / ps`) plus `i`.
pub proof fn lemma_region_phys_page_linear(r: MemoryRegion, i: nat)
    requires
        r.spec_valid(),
        0 <= i < r.pages,
    ensures
        r.pstart@.0 == (r.pstart@.0 / SPEC_PAGE_SIZE) * SPEC_PAGE_SIZE,
        region_phys_page(r, i).0 == r.pstart@.0 / SPEC_PAGE_SIZE + i,
{
}

/// The guest-page twin of [`lemma_region_phys_page_linear`].
pub proof fn lemma_region_guest_page_linear(r: MemoryRegion, i: nat)
    requires
        r.spec_valid(),
        0 <= i < r.pages,
    ensures
        r.vstart@.0 == (r.vstart@.0 / SPEC_PAGE_SIZE) * SPEC_PAGE_SIZE,
        region_guest_page(r, i).0 == r.vstart@.0 / SPEC_PAGE_SIZE + i,
{
}

/// Two regions that back the same physical page overlap in physical memory.
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
}

// ───────────────────────── budget region → machine Region ───────────────────
/// Project a budget `MemoryRegion` of zone `zid` to the machine-level [`Region`].
///
/// This is the argument-side bridge for the `insert_region` / `remove_region`
/// contract: the software-refinement proof turns the BudgetSpec region it fires
/// into the `Region` the [`SwView`] step consumes.
pub open spec fn region_to_abstract(zid: nat, r: MemoryRegion) -> Region {
    Region {
        vm: VmId(zid),
        gpa_base: r.vstart@.0 / SPEC_PAGE_SIZE,
        phys_base: r.pstart@.0 / SPEC_PAGE_SIZE,
        count: r.pages as nat,
        access: attr_to_perms(r.attr),
    }
}

/// The abstract region's page set matches the projection.
pub proof fn lemma_region_to_abstract_pages(zid: nat, r: MemoryRegion)
    requires
        r.spec_valid(),
    ensures
        region_to_abstract(zid, r).pages() == region_pages(r),
{
    let ar = region_to_abstract(zid, r);
    let pb = r.pstart@.0 / SPEC_PAGE_SIZE;
    assert forall|p: PhysPage| ar.pages().contains(p) <==> region_pages(r).contains(p) by {
        if ar.pages().contains(p) {
            // pb <= p.0 < pb + count; witness i = p.0 - pb.
            let i = (p.0 - pb) as nat;
            assert(0 <= i < r.pages);
            lemma_region_phys_page_linear(r, i);
            assert(region_phys_page(r, i).0 == p.0);
            assert(region_owns_page(r, p));  // witness i
        }
        if region_pages(r).contains(p) {
            let i = choose|i: nat| 0 <= i < r.pages && region_phys_page(r, i) == p;
            lemma_region_phys_page_linear(r, i);
            assert(p.0 == pb + i);
        }
    }
    assert(ar.pages() =~= region_pages(r));
}

/// The abstract region's stage-2 entries match the projection.
pub proof fn lemma_region_to_abstract_entries(zid: nat, r: MemoryRegion)
    requires
        r.spec_valid(),
    ensures
        region_to_abstract(zid, r).entries() == region_s2_entries(zid, r),
{
    let ar = region_to_abstract(zid, r);
    let gb = r.vstart@.0 / SPEC_PAGE_SIZE;
    let pb = r.pstart@.0 / SPEC_PAGE_SIZE;
    let lhs = ar.entries();
    let rhs = region_s2_entries(zid, r);

    assert forall|k: VmPageKey| lhs.contains_key(k) <==> rhs.contains_key(k) by {
        if lhs.contains_key(k) {
            // k.vm == VmId(zid) && gb <= k.gpa.0 < gb + count; witness i = k.gpa.0 - gb.
            let i = (k.gpa.0 - gb) as nat;
            assert(0 <= i < r.pages);
            lemma_region_guest_page_linear(r, i);
            assert(region_guest_page(r, i).0 == k.gpa.0);
            assert(region_owns_gpa(r, k.gpa));  // witness i
        }
        if rhs.contains_key(k) {
            let i = choose|i: nat| 0 <= i < r.pages && region_guest_page(r, i) == k.gpa;
            lemma_region_guest_page_linear(r, i);
            assert(k.gpa.0 == gb + i);
        }
    }
    assert forall|k: VmPageKey| #[trigger] lhs.contains_key(k) implies lhs[k] == rhs[k] by {
        let i = (k.gpa.0 - gb) as nat;
        assert(0 <= i < r.pages);
        lemma_region_guest_page_linear(r, i);
        assert(region_guest_page(r, i) == k.gpa);
        // rhs value chooses j with region_guest_page(r, j) == k.gpa; linearity ⇒ j == i.
        let j = choose|j: nat| 0 <= j < r.pages && region_guest_page(r, j) == k.gpa;
        lemma_region_guest_page_linear(r, j);
        assert(j == i);
        lemma_region_phys_page_linear(r, i);
        assert(lhs[k].page.0 == pb + i);
        assert(rhs[k].page == region_phys_page(r, i));
        assert(lhs[k].page == rhs[k].page);
    }
    assert(lhs =~= rhs);
}

/// **Trusted bridge.** If `region` is assignable in a BudgetSpec state, it is
/// realized by a region in that VM's budget.  This is where the static region
/// budget enters — as an *implementation-level* assumption relating the abstract,
/// state-dependent `SwView::is_region_assignable` to `zone_budget`, *not* as a
/// machine-model assumption.  An axiom, not a deferred proof: `is_region_assignable`
/// is uninterpreted, so this is a stated platform fact about the trusted interface.
pub axiom fn axiom_assignable_from_budget(s: BudgetSpec::State, region: Region)
    requires
        s@.is_region_assignable(region),
    ensures
        exists|r: MemoryRegion| #[trigger]
            zone_budget(region.vm.0).contains(r) && region_to_abstract(region.vm.0, r) == region,
;

// ───────────────────── mapping → machine-page helpers ───────────────────────
// Reinterpret a byte-addressed `mem_set.mappings` entry in the machine's
// page-numbered view.  `gpa_to_vaddr` is multiplication by the constant page
// size, so its round-trip and injectivity need no proof body.
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

/// Round-trip: the mapped vaddr of a region page is the page-aligned image of its
/// guest page — `gpa_to_vaddr ∘ region_guest_page = spec_page_vaddr`.
pub proof fn lemma_gpa_vaddr_roundtrip(r: MemoryRegion, i: nat)
    requires
        r.spec_valid(),
        0 <= i < r.pages,
    ensures
        gpa_to_vaddr(region_guest_page(r, i)) == r.spec_page_vaddr(i),
{
}

/// `gpa_to_vaddr` is injective (it is multiplication by the page size).
pub proof fn lemma_gpa_to_vaddr_injective(g1: GuestPage, g2: GuestPage)
    requires
        gpa_to_vaddr(g1) == gpa_to_vaddr(g2),
    ensures
        g1 == g2,
{
}

/// A region maps guest page `gpa` iff its dense page table has a key at the
/// corresponding vaddr — the bridge between the gpa-keyed `region_s2_entries` and
/// the vaddr-keyed `spec_mappings`.
pub proof fn lemma_region_gpa_mapped_iff(r: MemoryRegion, gpa: GuestPage)
    requires
        r.spec_valid(),
    ensures
        r.spec_mappings().contains_key(gpa_to_vaddr(gpa)) <==> region_owns_gpa(r, gpa),
{
    let v = gpa_to_vaddr(gpa);
    if region_owns_gpa(r, gpa) {
        let i = choose|i: nat| 0 <= i < r.pages && region_guest_page(r, i) == gpa;
        lemma_gpa_vaddr_roundtrip(r, i);
        assert(v == r.spec_page_vaddr(i));
        r.lemma_mappings_contains_pair(i);
    }
    if r.spec_mappings().contains_key(v) {
        r.lemma_mappings_sound(v);
        let i = choose|i: nat|
            0 <= i < r.pages && v == r.spec_page_vaddr(i) && r.spec_mappings()[v] == r.spec_frame(
                i,
            );
        lemma_gpa_vaddr_roundtrip(r, i);  // gpa_to_vaddr(region_guest_page(r,i)) == v == gpa_to_vaddr(gpa)
        lemma_gpa_to_vaddr_injective(region_guest_page(r, i), gpa);
        assert(region_owns_gpa(r, gpa));  // witness i
    }
}

/// The stage-2 entry a region installs for `k` equals the entry induced by the
/// frame its dense page table maps at `k`'s vaddr.
pub proof fn lemma_region_s2_value(zid: nat, r: MemoryRegion, k: VmPageKey)
    requires
        r.spec_valid(),
        k.vm == VmId(zid),
        region_owns_gpa(r, k.gpa),
    ensures
        region_s2_entries(zid, r).contains_key(k),
        region_s2_entries(zid, r)[k] == frame_s2_entry(r.spec_mappings()[gpa_to_vaddr(k.gpa)]),
{
    let v = gpa_to_vaddr(k.gpa);
    assert(region_s2_entries(zid, r).contains_key(k));
    let j = choose|j: nat| 0 <= j < r.pages && region_guest_page(r, j) == k.gpa;
    assert(0 <= j < r.pages && region_guest_page(r, j) == k.gpa);
    assert(region_s2_entries(zid, r)[k] == frame_s2_entry(r.spec_frame(j)));
    lemma_gpa_vaddr_roundtrip(r, j);
    assert(v == r.spec_page_vaddr(j));
    r.lemma_mappings_contains_pair(j);
    assert(r.spec_mappings()[v] == r.spec_frame(j));
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

/// A page owned by the zone is backed by some region of it.
pub proof fn lemma_zone_owned_pages_region_witness(gz: GhostZone, p: PhysPage)
    requires
        gz.wf(),
        zone_owned_pages(gz).contains(p),
    ensures
        exists|r: MemoryRegion| #[trigger] gz.regions().contains(r) && region_owns_page(r, p),
{
    let v = choose|v: SpecVAddr| #[trigger]
        gz.mem_set.mappings.contains_key(v) && frame_phys_page(gz.mem_set.mappings[v]) == p;
    let f = gz.mem_set.mappings[v];
    assert(gz.mem_set.mappings.contains_pair(v, f));
    // exact-dense soundness: (v, f) is exactly some region page and its frame.
    let (r, i) = choose|r: MemoryRegion, i: nat|
        gz.regions().contains(r) && 0 <= i < r.pages && v == r.spec_page_vaddr(i) && f
            == r.spec_frame(i);
    assert(gz.regions().contains(r) && 0 <= i < r.pages && v == r.spec_page_vaddr(i) && f
        == r.spec_frame(i));
    assert(region_phys_page(r, i) == p);
    assert(region_owns_page(r, p));  // witness i
}

/// An empty page table owns no pages.
pub proof fn lemma_zone_owned_pages_empty(gz: GhostZone)
    requires
        gz.mem_set.mappings =~= Map::<SpecVAddr, SpecFrame>::empty(),
    ensures
        zone_owned_pages(gz) =~= Set::<PhysPage>::empty(),
{
}

/// An empty page table installs no stage-2 entries.
pub proof fn lemma_zone_s2_entries_empty(zid: nat, gz: GhostZone)
    requires
        gz.mem_set.mappings =~= Map::<SpecVAddr, SpecFrame>::empty(),
    ensures
        zone_s2_entries(zid, gz) =~= Map::<VmPageKey, S2Entry>::empty(),
{
}

/// Cross-zone physical-page disjointness: distinct active zones own disjoint
/// physical pages.
pub proof fn lemma_state_owned_pages_disjoint(s: BudgetSpec::State)
    requires
        s.invariant(),
    ensures
        forall|zid1: nat, zid2: nat, p: PhysPage|
            #![trigger zone_owned_pages(s.zones[zid1]).contains(p), s.zones[zid2]]
            s.zones.contains_key(zid1) && s.zones.contains_key(zid2) && zid1 != zid2
                && zone_owned_pages(s.zones[zid1]).contains(p) ==> !zone_owned_pages(
                s.zones[zid2],
            ).contains(p),
{
    assert forall|zid1: nat, zid2: nat, p: PhysPage|
        #![trigger zone_owned_pages(s.zones[zid1]).contains(p), s.zones[zid2]]
        s.zones.contains_key(zid1) && s.zones.contains_key(zid2) && zid1 != zid2
            && zone_owned_pages(s.zones[zid1]).contains(p) implies !zone_owned_pages(
        s.zones[zid2],
    ).contains(p) by {
        if zone_owned_pages(s.zones[zid2]).contains(p) {
            let gz1 = s.zones[zid1];
            let gz2 = s.zones[zid2];
            assert(gz1.wf());
            assert(gz2.wf());

            // Recover backing regions from the exposed mappings (exact-dense soundness).
            lemma_zone_owned_pages_region_witness(gz1, p);
            lemma_zone_owned_pages_region_witness(gz2, p);

            let r1 = choose|r: MemoryRegion|
                #![trigger gz1.regions().contains(r)]
                gz1.regions().contains(r) && region_owns_page(r, p);
            assert(gz1.regions().contains(r1) && region_owns_page(r1, p));
            let i1 = choose|i: nat| 0 <= i < r1.pages && region_phys_page(r1, i) == p;
            assert(0 <= i1 < r1.pages && region_phys_page(r1, i1) == p);

            let r2 = choose|r: MemoryRegion|
                #![trigger gz2.regions().contains(r)]
                gz2.regions().contains(r) && region_owns_page(r, p);
            assert(gz2.regions().contains(r2) && region_owns_page(r2, p));
            let i2 = choose|i: nat| 0 <= i < r2.pages && region_phys_page(r2, i) == p;
            assert(0 <= i2 < r2.pages && region_phys_page(r2, i2) == p);

            assert(r1.spec_valid());
            assert(r2.spec_valid());

            assert(gz1.contains_region(r1));
            assert(gz2.contains_region(r2));
            assert(zone_budget(zid1).contains(r1));
            assert(zone_budget(zid2).contains(r2));

            zone_budget_pairwise_disjoint();
            assert(!zone_budget(zid2).contains(r1));
            assert(r1 != r2);
            zone_budget_in_all_regions();
            assert(all_regions().contains(r1) && all_regions().contains(r2));
            all_regions_disjoint();
            assert(!r1.spec_overlaps_pmem(r2));

            lemma_same_phys_page_implies_pmem_overlap(r1, i1, r2, i2);
            assert(r1.spec_overlaps_pmem(r2));
            assert(false);
        }
    }
}

// ───────────── guard derivations for the software-refinement proof ───────────
/// Every page of a region present in a zone is owned by that zone.
pub proof fn lemma_region_in_zone_owns_pages(gz: GhostZone, r: MemoryRegion)
    requires
        gz.wf(),
        gz.contains_region(r),
    ensures
        forall|p: PhysPage| #[trigger]
            region_pages(r).contains(p) ==> zone_owned_pages(gz).contains(p),
{
    assert(r.spec_valid());  // r ∈ regions, gz.wf() ⇒ valid
    assert forall|p: PhysPage| region_pages(r).contains(p) implies zone_owned_pages(gz).contains(
        p,
    ) by {
        let i = choose|i: nat| 0 <= i < r.pages && region_phys_page(r, i) == p;
        let v = r.spec_page_vaddr(i);
        assert(gz.regions().contains(r));
        assert(gz.mem_set.mappings.contains_pair(v, r.spec_frame(i)));  // completeness clause
        assert(frame_phys_page(gz.mem_set.mappings[v]) == p);
        assert(zone_owned_pages(gz).contains(p));  // witness v
    }
}

/// A guest page owned by a region present in a zone is mapped by that zone.
pub proof fn lemma_region_in_zone_maps_gpa(gz: GhostZone, r: MemoryRegion, g: GuestPage)
    requires
        gz.wf(),
        gz.contains_region(r),
        region_owns_gpa(r, g),
    ensures
        gz.mem_set.mappings.contains_key(gpa_to_vaddr(g)),
{
    assert(r.spec_valid());  // r ∈ regions, gz.wf() ⇒ valid
    let i = choose|i: nat| 0 <= i < r.pages && region_guest_page(r, i) == g;
    let v = r.spec_page_vaddr(i);
    assert(gz.regions().contains(r));
    assert(gz.mem_set.mappings.contains_pair(v, r.spec_frame(i)));  // completeness clause
    lemma_gpa_vaddr_roundtrip(r, i);  // gpa_to_vaddr(region_guest_page(r,i)) == spec_page_vaddr(i)
    assert(gpa_to_vaddr(g) == v);
}

/// Two valid, vmem-overlapping regions share a guest page — the vmem analogue of
/// [`lemma_same_phys_page_implies_pmem_overlap`].
pub proof fn lemma_vmem_overlap_implies_shared_gpa(r1: MemoryRegion, r2: MemoryRegion)
    requires
        r1.spec_valid(),
        r2.spec_valid(),
        r1.spec_overlaps_vmem(r2),
    ensures
        exists|g: GuestPage| region_owns_gpa(r1, g) && region_owns_gpa(r2, g),
{
    let ps = SPEC_PAGE_SIZE;
    let s1 = r1.vstart@.0;
    let s2 = r2.vstart@.0;
    let n1 = r1.pages as nat;
    let n2 = r2.pages as nat;
    let q1 = s1 / ps;
    let q2 = s2 / ps;
    lemma_region_guest_page_linear(r1, 0);  // s1 == q1*ps, region_guest_page(r1,0).0 == q1
    lemma_region_guest_page_linear(r2, 0);  // s2 == q2*ps, region_guest_page(r2,0).0 == q2
    if s1 <= s2 {
        assert(s2 < s1 + n1 * ps);  // overlap, base1 <= base2 branch
        assert(q1 <= q2);
        assert(q2 < q1 + n1);
        let i1 = (q2 - q1) as nat;
        let g = GuestPage(q2);
        lemma_region_guest_page_linear(r1, i1);  // region_guest_page(r1,i1).0 == q1 + i1 == q2
        assert(region_guest_page(r1, i1) == g);
        assert(region_owns_gpa(r1, g));  // witness i1
        assert(region_guest_page(r2, 0) == g);  // q2 + 0 == q2
        assert(region_owns_gpa(r2, g));  // witness 0
    } else {
        assert(s1 < s2 + n2 * ps);  // overlap, base1 > base2 branch
        assert(q2 <= q1);
        assert(q1 < q2 + n2);
        let i2 = (q1 - q2) as nat;
        let g = GuestPage(q1);
        lemma_region_guest_page_linear(r2, i2);  // region_guest_page(r2,i2).0 == q2 + i2 == q1
        assert(region_guest_page(r2, i2) == g);
        assert(region_owns_gpa(r2, g));  // witness i2
        assert(region_guest_page(r1, 0) == g);  // q1 + 0 == q1
        assert(region_owns_gpa(r1, g));  // witness 0
    }
}

} // verus!
