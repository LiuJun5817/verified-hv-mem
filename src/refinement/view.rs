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
use crate::hv_mem::spec::budget::{
    zone_budget, zone_budget_in_all_regions, zone_budget_pairwise_disjoint, BudgetSpec,
};
use crate::hv_mem::spec::{all_regions, all_regions_disjoint, GhostZone};
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
/// Relates `region_phys_page` equality to `MemoryRegion::spec_overlaps_pmem`.
/// The new `MemoryRegion` lays its frames out linearly from a page-aligned
/// physical base (`spec_page_paddr(i) == pstart + i*ps`), so a shared physical
/// page index means the two page-aligned physical blocks share a whole page,
/// hence their byte intervals overlap.  No linearity axiom is needed — it is a
/// structural property of `pstart` + `spec_valid` (page-aligned base).
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
    let ps = SPEC_PAGE_SIZE;
    let a1 = r1.pstart@.0;
    let a2 = r2.pstart@.0;

    // Frame bases are linear by construction: spec_frame(i).base == pstart + i*ps.
    assert(r1.spec_frame(i1).base.0 == a1 + i1 * ps);
    assert(r2.spec_frame(i2).base.0 == a2 + i2 * ps);

    // Page-aligned physical bases (spec_valid): a = q*ps.
    let q1 = a1 / ps;
    let q2 = a2 / ps;
    assert(a1 % ps == 0 && a2 % ps == 0);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a1 as int, ps as int);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a2 as int, ps as int);
    assert(a1 == q1 * ps);
    assert(a2 == q2 * ps);

    // region_phys_page(r, i).0 == q + i, and the hypothesis gives q1+i1 == q2+i2.
    assert((a1 + i1 * ps) / ps == q1 + i1) by (nonlinear_arith)
        requires
            a1 == q1 * ps,
            ps > 0,
    ;
    assert((a2 + i2 * ps) / ps == q2 + i2) by (nonlinear_arith)
        requires
            a2 == q2 * ps,
            ps > 0,
    ;
    assert(region_phys_page(r1, i1).0 == q1 + i1);
    assert(region_phys_page(r2, i2).0 == q2 + i2);
    assert(q1 + i1 == q2 + i2);

    // spec_overlaps_pmem compares the byte intervals [pstart, pstart + pages*ps).
    let ss = a1;
    let se = a1 + r1.pages as nat * ps;
    let os = a2;
    let oe = a2 + r2.pages as nat * ps;
    if ss <= os {
        assert(se > os) by (nonlinear_arith)
            requires
                se == a1 + r1.pages as nat * ps,
                os == a2,
                a1 == q1 * ps,
                a2 == q2 * ps,
                ps > 0,
                q1 + i1 == q2 + i2,
                i1 < r1.pages,
                i2 >= 0,
        ;
    } else {
        assert(oe > ss) by (nonlinear_arith)
            requires
                oe == a2 + r2.pages as nat * ps,
                ss == a1,
                a1 == q1 * ps,
                a2 == q2 * ps,
                ps > 0,
                q1 + i1 == q2 + i2,
                i2 < r2.pages,
                i1 >= 0,
        ;
    }
    assert(r1.spec_overlaps_pmem(r2));
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

/// Round-trip: the mapped vaddr of a region page is the page-aligned image of its
/// guest page — `gpa_to_vaddr ∘ region_guest_page = spec_page_vaddr`.  Holds
/// because a valid region starts page-aligned, so every page vaddr is a multiple
/// of `SPEC_PAGE_SIZE`.
pub proof fn lemma_gpa_vaddr_roundtrip(r: MemoryRegion, i: nat)
    requires
        r.spec_valid(),
        0 <= i < r.pages,
    ensures
        gpa_to_vaddr(region_guest_page(r, i)) == r.spec_page_vaddr(i),
{
    let ps = SPEC_PAGE_SIZE;
    let s = r.vstart@.0;
    let x = r.spec_page_vaddr(i).0;
    assert(r.vstart@.aligned(ps));  // spec_valid ⇒ start page-aligned
    assert(s % ps == 0);
    assert(x == s + i * ps);  // spec_page_vaddr(i) = start.offset(i*ps)
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(s as int, ps as int);
    assert(s == ps * (s / ps));
    assert(x == (s / ps + i) * ps) by (nonlinear_arith)
        requires
            x == s + i * ps,
            s == ps * (s / ps),
    ;
    assert((x / ps) == s / ps + i) by (nonlinear_arith)
        requires
            x == (s / ps + i) * ps,
            ps > 0,
    ;
    assert((x / ps) * ps == x) by (nonlinear_arith)
        requires
            x == (s / ps + i) * ps,
            (x / ps) == s / ps + i,
    ;
    // region_guest_page(r,i).0 == x/ps and gpa_to_vaddr(g).0 == g.0*ps
    assert(gpa_to_vaddr(region_guest_page(r, i)).0 == x);
}

/// `gpa_to_vaddr` is injective (it is multiplication by the page size).
pub proof fn lemma_gpa_to_vaddr_injective(g1: GuestPage, g2: GuestPage)
    requires
        gpa_to_vaddr(g1) == gpa_to_vaddr(g2),
    ensures
        g1 == g2,
{
    assert(g1.0 * SPEC_PAGE_SIZE == g2.0 * SPEC_PAGE_SIZE);
    assert(g1.0 == g2.0) by (nonlinear_arith)
        requires
            g1.0 * SPEC_PAGE_SIZE == g2.0 * SPEC_PAGE_SIZE,
            SPEC_PAGE_SIZE == 0x1000nat,
    ;
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
    // the map value chooses j with region_guest_page(r, j) == k.gpa.
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

/// A page owned by the zone is backed by some region of it (recovers a region
/// witness from the exposed mapping, using exact-dense soundness).
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

/// Cross-zone physical-page disjointness, proven from the **real** `invariant()`
/// (`inv_zone_within_budget` + `inv_zones_wf`) plus the budget axioms.
///
/// Lives here (rather than in [`super::refine`]) so both the contract proof and
/// the [`super::transition`] deltas can use it.
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

            // pmem-linearity is now structural (page-aligned `pstart` + linear frames).
            lemma_same_phys_page_implies_pmem_overlap(r1, i1, r2, i2);
            assert(r1.spec_overlaps_pmem(r2));
            assert(false);
        }
    }
}

} // verus!
