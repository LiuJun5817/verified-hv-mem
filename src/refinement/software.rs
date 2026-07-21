//! Software-refinement layer: `SoftwareSpec` (the wrapped `BudgetSpec::State`)
//! -> `SoftwareView` plus `impl SoftwareRefinement for SoftwareSpec`.
//!
//! This module owns the software-side abstraction relation and the refinement
//! contract.  The projection maps the tokenized state machine's own state
//! (`zone_ids` and per-zone `GhostZone` region sets) to the security model's
//! `SoftwareView`; `invariants()` is the machine's real `invariant()`, so
//! `inv_implies_wf` proves every reachable state projects to a `wf` (hence
//! secure) `SoftwareView`.
//!
//! Each transition method fires the matching `BudgetSpec` macro transition via
//! `BudgetSpec::take_step::*` (which supplies `post.invariant()`) and then proves
//! the corresponding `SoftwareView` step.  `insert_region` / `remove_region` take a
//! machine-level [`Region`] argument: the trusted bridge
//! [`axiom_assignable_from_budget`] recovers the budget `MemoryRegion` it
//! abstracts, the projection-equality lemmas identify their pages/entries, and
//! the projection-delta lemmas assemble the step.  The transition guards
//! (`!contains_region` / `!overlaps_vmem` for insert, `contains_region` /
//! pmem-exclusivity for remove) are *derived* from the closed
//! `SoftwareView::*_enabled` preconditions.
//!
//! # Layout
//!
//! | §  | contents                                                            |
//! |----|---------------------------------------------------------------------|
//! | §1 | per-region geometry (pages/entries a `MemoryRegion` induces)        |
//! | §2 | budget region → machine [`Region`] + the trusted assignability axiom |
//! | §3 | state projections (zone/global page sets and stage-2 maps)          |
//! | §4 | [`SoftwareSpec`] — the abstraction relation R                       |
//! | §5 | facts about the projection (disjointness, framing, `iommu_wf`)      |
//! | §6 | transition-guard derivations                                        |
//! | §7 | per-op projection-delta lemmas (consumed by the §8 impl)            |
//! | §8 | the [`SoftwareRefinement`] contract + `impl for SoftwareSpec`       |
use vstd::prelude::*;

verus! {

use crate::address::addr::SpecVAddr;
use crate::address::frame::SpecFrame;
use crate::address::region::*;
use crate::hv_mem::spec::budget::*;
use crate::hv_mem::spec::GhostZone;
use crate::model::convert::*;
use crate::model::software::{Region, SoftwareView};
use crate::model::types::{GuestPage, PhysPage, S2Entry, SharedPage, VmId, VmPageKey};
use crate::memory_set::SpecMemorySet;

// ---------------------------------------------------------------------------
// §1  Per-region geometry
//
// The *concrete* per-region geometry: what physical page / guest page / stage-2
// entry each page of a `MemoryRegion` maps to.  Built on the canonical region
// geometry (`MemoryRegion::spec_page_vaddr` / `spec_frame`) and the page-number
// primitives from [`crate::model::convert`].
// ---------------------------------------------------------------------------
/// Machine physical page backing page `i` of region `r`.
pub open spec fn region_phys_page(r: MemoryRegion, i: nat) -> PhysPage {
    phys_page_of_paddr(r.spec_frame(i).base)
}

/// Guest page of page `i` of region `r`.
pub open spec fn region_guest_page(r: MemoryRegion, i: nat) -> GuestPage {
    gpa_of_vaddr(r.spec_page_vaddr(i))
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
        gz.cpu_mem_set.regions.contains(rr) && rr != r ==> !rr.spec_overlaps_pmem(r)
}

/// No IOMMU region other than `r` pmem-overlaps `r` (the DMA analog of
/// `region_pmem_exclusive`).
pub open spec fn region_iommu_pmem_exclusive(gz: GhostZone, r: MemoryRegion) -> bool {
    forall|rr: MemoryRegion| #[trigger]
        gz.iommu_mem_set.regions.contains(rr) && rr != r ==> !rr.spec_overlaps_pmem(r)
}

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

/// Round-trip: the mapped vaddr of a region page is the page-aligned image of its
/// guest page — `vaddr_of_gpa ∘ region_guest_page = spec_page_vaddr`.
pub proof fn lemma_gpa_vaddr_roundtrip(r: MemoryRegion, i: nat)
    requires
        r.spec_valid(),
        0 <= i < r.pages,
    ensures
        vaddr_of_gpa(region_guest_page(r, i)) == r.spec_page_vaddr(i),
{
}

/// A region maps guest page `gpa` iff its dense page table has a key at the
/// corresponding vaddr — the bridge between the gpa-keyed `region_s2_entries` and
/// the vaddr-keyed `spec_mappings`.
pub proof fn lemma_region_gpa_mapped_iff(r: MemoryRegion, gpa: GuestPage)
    requires
        r.spec_valid(),
    ensures
        r.spec_mappings().contains_key(vaddr_of_gpa(gpa)) <==> region_owns_gpa(r, gpa),
{
    let v = vaddr_of_gpa(gpa);
    if region_owns_gpa(r, gpa) {
        let i = choose|i: nat| 0 <= i < r.pages && region_guest_page(r, i) == gpa;
        lemma_gpa_vaddr_roundtrip(r, i);
        r.lemma_mappings_contains_pair(i);
    }
    if r.spec_mappings().contains_key(v) {
        r.lemma_mappings_sound(v);
        let i = choose|i: nat|
            0 <= i < r.pages && v == r.spec_page_vaddr(i) && r.spec_mappings()[v] == r.spec_frame(
                i,
            );
        lemma_gpa_vaddr_roundtrip(r, i);  // vaddr_of_gpa(region_guest_page(r,i)) == v == vaddr_of_gpa(gpa)
        lemma_vaddr_of_gpa_injective(region_guest_page(r, i), gpa);
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
        region_s2_entries(zid, r)[k] == frame_to_s2(r.spec_mappings()[vaddr_of_gpa(k.gpa)]),
{
    let v = vaddr_of_gpa(k.gpa);
    let j = choose|j: nat| 0 <= j < r.pages && region_guest_page(r, j) == k.gpa;
    lemma_gpa_vaddr_roundtrip(r, j);
    r.lemma_mappings_contains_pair(j);
}

// ---------------------------------------------------------------------------
// §2  Budget region → machine `Region` + the trusted assignability axiom
//
// `region_to_abstract` renders a budget `MemoryRegion` as the machine-level
// [`Region`] the model steps speak about; the two `lemma_region_to_abstract_*`
// prove the renderings induce the same pages/entries.  The axiom is the single
// trusted seam of this file (see its doc).
// ---------------------------------------------------------------------------
/// Project a budget `MemoryRegion` of zone `zid` to the machine-level [`Region`].
///
/// This is the argument-side bridge for the `insert_region` / `remove_region`
/// contract: the software-refinement proof turns the BudgetSpec region it fires
/// into the `Region` the [`SoftwareView`] step consumes.
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
    assert forall|p: PhysPage| ar.pages().contains(p) <==> region_pages(r).contains(p) by {
        if ar.pages().contains(p) {
            // Use the page offset from the region's physical base as the witness.
            let i = (p.0 - r.pstart@.0 / SPEC_PAGE_SIZE) as nat;
            lemma_region_phys_page_linear(r, i);
        }
        if region_pages(r).contains(p) {
            let i = choose|i: nat| 0 <= i < r.pages && region_phys_page(r, i) == p;
            lemma_region_phys_page_linear(r, i);
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
    let lhs = ar.entries();
    let rhs = region_s2_entries(zid, r);

    assert forall|k: VmPageKey| lhs.contains_key(k) <==> rhs.contains_key(k) by {
        if lhs.contains_key(k) {
            // k.vm == VmId(zid) && gb <= k.gpa.0 < gb + count; witness i = k.gpa.0 - gb.
            let i = (k.gpa.0 - gb) as nat;
            lemma_region_guest_page_linear(r, i);
        }
        if rhs.contains_key(k) {
            let i = choose|i: nat| 0 <= i < r.pages && region_guest_page(r, i) == k.gpa;
            lemma_region_guest_page_linear(r, i);
        }
    }
    assert forall|k: VmPageKey| #[trigger] lhs.contains_key(k) implies lhs[k] == rhs[k] by {
        let i = (k.gpa.0 - gb) as nat;
        lemma_region_guest_page_linear(r, i);
        // rhs value chooses j with region_guest_page(r, j) == k.gpa; linearity => j == i.
        let j = choose|j: nat| 0 <= j < r.pages && region_guest_page(r, j) == k.gpa;
        lemma_region_guest_page_linear(r, j);
        lemma_region_phys_page_linear(r, i);
    }
    assert(lhs =~= rhs);
}

/// **Trusted bridge.** If `region` is assignable in a BudgetSpec state, it is
/// realized by a region in that VM's budget.  This is where the static region
/// budget enters — as an *implementation-level* assumption relating the abstract,
/// state-dependent `SoftwareView::is_region_assignable` to `zone_regions`, *not* as a
/// machine-model assumption.  An axiom, not a deferred proof: `is_region_assignable`
/// is uninterpreted, so this is a stated platform fact about the trusted interface.
pub axiom fn axiom_assignable_from_budget(s: SoftwareSpec, region: Region)
    requires
        s@.is_region_assignable(region),
    ensures
        exists|r: MemoryRegion| #[trigger]
            zone_regions(region.vm.0).contains(r) && region_to_abstract(region.vm.0, r) == region,
;

// ---------------------------------------------------------------------------
// §3  State projections
//
// Per-zone and whole-state projections of `BudgetSpec::State`: CPU ownership
// (`zone_owned_pages` / `all_owned_pages` / `hypervisor_pool`) and stage-2 maps
// (`zone_s2_entries` / `state_s2_map`), plus their IOMMU counterparts and the
// static GIC sharing set.
// ---------------------------------------------------------------------------
/// Physical pages owned by a zone: the frames its page table maps, in page units.
pub open spec fn zone_owned_pages(gz: GhostZone) -> Set<PhysPage> {
    Set::new(
        |p: PhysPage|
            exists|v: SpecVAddr| #[trigger]
                gz.cpu_mem_set.mappings.contains_key(v) && frame_phys_page(
                    gz.cpu_mem_set.mappings[v],
                ) == p,
    )
}

/// Stage-2 entries installed by a zone: one per mapped guest page.
pub open spec fn zone_s2_entries(zid: nat, gz: GhostZone) -> Map<VmPageKey, S2Entry> {
    Map::new(
        |k: VmPageKey|
            k.vm == VmId(zid) && gz.cpu_mem_set.mappings.contains_key(vaddr_of_gpa(k.gpa)),
        |k: VmPageKey| frame_to_s2(gz.cpu_mem_set.mappings[vaddr_of_gpa(k.gpa)]),
    )
}

/// All physical pages that lie within *some* zone's static budget.
pub open spec fn all_budget_pages() -> Set<PhysPage> {
    Set::new(
        |pp: PhysPage|
            exists|zid: nat, r: MemoryRegion|
                #![trigger zone_regions(zid).contains(r), region_owns_page(r, pp)]
                zone_regions(zid).contains(r) && region_owns_page(r, pp),
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

/// Physical pages a zone owns **privately** for IOMMU/DMA: pages mapped by its
/// `iommu_mem_set` that are *not* part of the shared GIC region.  The shared GIC pages
/// are tracked separately (`gic_shared_pages_set` / `iommu_shared`), so a VM's private
/// DMA set is exactly its zone-disjoint DMA memory — genuinely private, with no GIC
/// overlap.
pub open spec fn zone_iommu_private_pages(gz: GhostZone) -> Set<PhysPage> {
    Set::new(
        |p: PhysPage|
            !is_gic_page(p) && exists|v: SpecVAddr| #[trigger]
                gz.iommu_mem_set.mappings.contains_key(v) && frame_phys_page(
                    gz.iommu_mem_set.mappings[v],
                ) == p,
    )
}

/// IOMMU stage-2 entries installed by a zone: one per mapped guest page.
pub open spec fn zone_iommu_s2_entries(zid: nat, gz: GhostZone) -> Map<VmPageKey, S2Entry> {
    Map::new(
        |k: VmPageKey|
            k.vm == VmId(zid) && gz.iommu_mem_set.mappings.contains_key(vaddr_of_gpa(k.gpa)),
        |k: VmPageKey| frame_to_s2(gz.iommu_mem_set.mappings[vaddr_of_gpa(k.gpa)]),
    )
}

/// IOMMU stage-2 map of the whole state: the union of each zone's IOMMU entries.
pub open spec fn state_iommu_s2_map(s: BudgetSpec::State) -> Map<VmPageKey, S2Entry> {
    Map::new(
        |k: VmPageKey|
            s.zone_ids.contains(k.vm.0) && zone_iommu_s2_entries(
                k.vm.0,
                s.zones[k.vm.0],
            ).contains_key(k),
        |k: VmPageKey| zone_iommu_s2_entries(k.vm.0, s.zones[k.vm.0])[k],
    )
}

/// Whether `p` is a page of the (shared) GIC region.
pub open spec fn is_gic_page(p: PhysPage) -> bool {
    region_owns_page(gic_region(), p)
}

/// The pages that may be IOMMU-shared across all VMs: exactly the GIC region's
/// pages.  VM-independent (does not grow/shrink as VMs come and go), so it is a
/// stable projection target.
pub open spec fn gic_shared_pages_set() -> Set<PhysPage> {
    Set::new(|p: PhysPage| is_gic_page(p))
}

// ---------------------------------------------------------------------------
// §4  `SoftwareSpec` — the abstraction relation R
// ---------------------------------------------------------------------------
/// The software-side refinement carrier: the `BudgetSpec` state, wrapped as a
/// newtype — symmetric to [`HardwareSpec`](super::hardware::HardwareSpec) on the
/// hardware side (which pairs the two `MmuSpec` instances).  `View` and
/// [`SoftwareRefinement`] live here, not on the naked `BudgetSpec::State`, so the
/// refinement boundary is `SoftwareSpec ↔ HardwareSpec` on both sides.
pub ghost struct SoftwareSpec {
    pub budget: BudgetSpec::State,
}

impl View for SoftwareSpec {
    type V = SoftwareView;

    /// R: project the budget state to the abstract `SoftwareView`.  `vm_owned` and
    /// `s2_map` come from the zones; `hypervisor_owned` is the unowned budget;
    /// `shared_pages` is empty (cross-VM sharing is out of scope).
    open spec fn view(&self) -> SoftwareView {
        SoftwareView {
            all_vms: Set::new(|vm: VmId| self.budget.zone_ids.contains(vm.0)),
            hypervisor_owned: hypervisor_pool(self.budget.zones),
            vm_owned: Map::new(
                |vm: VmId| self.budget.zone_ids.contains(vm.0),
                |vm: VmId| zone_owned_pages(self.budget.zones[vm.0]),
            ),
            shared_pages: Set::empty(),
            s2_map: state_s2_map(self.budget),
            iommu_s2_map: state_iommu_s2_map(self.budget),
            iommu_owned: Map::new(
                |vm: VmId| self.budget.zone_ids.contains(vm.0),
                |vm: VmId| zone_iommu_private_pages(self.budget.zones[vm.0]),
            ),
            iommu_shared: gic_shared_pages_set(),
        }
    }
}

// ---------------------------------------------------------------------------
// §5  Facts about the projection
//
// Membership/witness helpers, empty-zone collapses, the cross-zone disjointness
// theorems (CPU, DMA-private, DMA-vs-CPU), the two framing lemmas (a CPU-side
// op leaves the IOMMU projection unchanged and vice versa), and the capstone
// [`lemma_reachable_iommu_separation`]: every invariant state projects to
// `iommu_wf`.
// ---------------------------------------------------------------------------
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
        zone_regions(zid).contains(r),
    ensures
        forall|pp: PhysPage| #[trigger]
            region_pages(r).contains(pp) ==> all_budget_pages().contains(pp),
{
}

/// Every stage-2 entry a zone installs targets a page that zone owns
/// (the per-zone half of `SoftwareView::translation_wf`).
pub proof fn lemma_zone_s2_target_owned(zid: nat, gz: GhostZone)
    ensures
        forall|k: VmPageKey| #[trigger]
            zone_s2_entries(zid, gz).contains_key(k) ==> zone_owned_pages(gz).contains(
                zone_s2_entries(zid, gz)[k].page,
            ),
{
}

/// A page owned by the zone is backed by some region of it.
pub proof fn lemma_zone_owned_pages_region_witness(gz: GhostZone, p: PhysPage)
    requires
        gz.wf(),
        zone_owned_pages(gz).contains(p),
    ensures
        exists|r: MemoryRegion| #[trigger]
            gz.cpu_mem_set.regions.contains(r) && region_owns_page(r, p),
{
    let v = choose|v: SpecVAddr| #[trigger]
        gz.cpu_mem_set.mappings.contains_key(v) && frame_phys_page(gz.cpu_mem_set.mappings[v]) == p;
    let f = gz.cpu_mem_set.mappings[v];
    assert(gz.cpu_mem_set.mappings.contains_pair(v, f));
    // exact-dense soundness: (v, f) is exactly some region page and its frame.
    let (r, i) = choose|r: MemoryRegion, i: nat|
        gz.cpu_mem_set.regions.contains(r) && 0 <= i < r.pages && v == r.spec_page_vaddr(i) && f
            == r.spec_frame(i);
    assert(gz.cpu_mem_set.regions.contains(r) && 0 <= i < r.pages && v == r.spec_page_vaddr(i) && f
        == r.spec_frame(i));
    assert(region_phys_page(r, i) == p);
    assert(region_owns_page(r, p));  // witness i
}

/// IOMMU analog of `lemma_zone_s2_target_owned`: every IOMMU stage-2 entry a zone
/// installs targets a page the zone may DMA — a **private** DMA page
/// (`zone_iommu_private_pages`) or a **shared** GIC page (`is_gic_page`).
pub proof fn lemma_zone_iommu_s2_target_owned(zid: nat, gz: GhostZone)
    ensures
        forall|k: VmPageKey| #[trigger]
            zone_iommu_s2_entries(zid, gz).contains_key(k) ==> zone_iommu_private_pages(
                gz,
            ).contains(zone_iommu_s2_entries(zid, gz)[k].page) || is_gic_page(
                zone_iommu_s2_entries(zid, gz)[k].page,
            ),
{
}

/// IOMMU analog of `lemma_zone_owned_pages_region_witness`: a **private** DMA page of a
/// zone is backed by some *non-GIC* region of its `iommu_mem_set` (the GIC is excluded
/// from private pages, so a region backing a private page cannot be the GIC region).
pub proof fn lemma_zone_iommu_private_pages_region_witness(gz: GhostZone, p: PhysPage)
    requires
        gz.wf(),
        zone_iommu_private_pages(gz).contains(p),
    ensures
        exists|r: MemoryRegion| #[trigger]
            gz.iommu_mem_set.regions.contains(r) && region_owns_page(r, p) && r != gic_region(),
{
    let v = choose|v: SpecVAddr| #[trigger]
        gz.iommu_mem_set.mappings.contains_key(v) && frame_phys_page(gz.iommu_mem_set.mappings[v])
            == p;
    let f = gz.iommu_mem_set.mappings[v];
    assert(gz.iommu_mem_set.mappings.contains_pair(v, f));
    let (r, i) = choose|r: MemoryRegion, i: nat|
        gz.iommu_mem_set.regions.contains(r) && 0 <= i < r.pages && v == r.spec_page_vaddr(i) && f
            == r.spec_frame(i);
    assert(gz.iommu_mem_set.regions.contains(r) && 0 <= i < r.pages && v == r.spec_page_vaddr(i)
        && f == r.spec_frame(i));
    assert(region_phys_page(r, i) == p);
    assert(region_owns_page(r, p));  // witness i
    // `p` is private => not a GIC page, so its backing region is not the GIC region
    // (the GIC region owns only GIC pages).
    assert(!is_gic_page(p));
    assert(r != gic_region()) by {
        if r == gic_region() {
            assert(region_owns_page(gic_region(), p));  // == is_gic_page(p)
            assert(false);
        }
    }
}

/// An empty page table owns no pages.
pub proof fn lemma_zone_owned_pages_empty(gz: GhostZone)
    requires
        gz.cpu_mem_set.mappings =~= Map::<SpecVAddr, SpecFrame>::empty(),
    ensures
        zone_owned_pages(gz) =~= Set::<PhysPage>::empty(),
{
}

/// An empty page table installs no stage-2 entries.
pub proof fn lemma_zone_s2_entries_empty(zid: nat, gz: GhostZone)
    requires
        gz.cpu_mem_set.mappings =~= Map::<SpecVAddr, SpecFrame>::empty(),
    ensures
        zone_s2_entries(zid, gz) =~= Map::<VmPageKey, S2Entry>::empty(),
{
}

/// An empty IOMMU page table owns no private DMA pages.
pub proof fn lemma_zone_iommu_private_pages_empty(gz: GhostZone)
    requires
        gz.iommu_mem_set.mappings =~= Map::<SpecVAddr, SpecFrame>::empty(),
    ensures
        zone_iommu_private_pages(gz) =~= Set::<PhysPage>::empty(),
{
}

/// An empty IOMMU page table installs no IOMMU stage-2 entries.
pub proof fn lemma_zone_iommu_s2_entries_empty(zid: nat, gz: GhostZone)
    requires
        gz.iommu_mem_set.mappings =~= Map::<SpecVAddr, SpecFrame>::empty(),
    ensures
        zone_iommu_s2_entries(zid, gz) =~= Map::<VmPageKey, S2Entry>::empty(),
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

            // Recover backing regions from the exposed mappings (exact-dense soundness).
            lemma_zone_owned_pages_region_witness(gz1, p);
            lemma_zone_owned_pages_region_witness(gz2, p);

            let r1 = choose|r: MemoryRegion|
                #![trigger gz1.cpu_mem_set.regions.contains(r)]
                gz1.cpu_mem_set.regions.contains(r) && region_owns_page(r, p);
            let i1 = choose|i: nat| 0 <= i < r1.pages && region_phys_page(r1, i) == p;

            let r2 = choose|r: MemoryRegion|
                #![trigger gz2.cpu_mem_set.regions.contains(r)]
                gz2.cpu_mem_set.regions.contains(r) && region_owns_page(r, p);
            let i2 = choose|i: nat| 0 <= i < r2.pages && region_phys_page(r2, i) == p;

            assert(r1.spec_valid());
            assert(r2.spec_valid());

            assert(gz1.cpu_mem_set.regions.contains(r1));
            assert(gz2.cpu_mem_set.regions.contains(r2));
            assert(zone_regions(zid1).contains(r1));
            assert(zone_regions(zid2).contains(r2));

            zone_regions_pairwise_disjoint();
            lemma_same_phys_page_implies_pmem_overlap(r1, i1, r2, i2);
        }
    }
}

/// **IOMMU private separation.** Two *distinct* zones never share a private DMA page:
/// a private DMA page is backed by a non-GIC region, and those (being private
/// zone-budget regions) are pairwise pmem-disjoint across zones.
pub proof fn lemma_state_iommu_private_disjoint(s: BudgetSpec::State)
    requires
        s.invariant(),
    ensures
        forall|zid1: nat, zid2: nat, p: PhysPage|
            #![trigger zone_iommu_private_pages(s.zones[zid1]).contains(p), s.zones[zid2]]
            s.zones.contains_key(zid1) && s.zones.contains_key(zid2) && zid1 != zid2
                && zone_iommu_private_pages(s.zones[zid1]).contains(p)
                ==> !zone_iommu_private_pages(s.zones[zid2]).contains(p),
{
    assert forall|zid1: nat, zid2: nat, p: PhysPage|
        #![trigger zone_iommu_private_pages(s.zones[zid1]).contains(p), s.zones[zid2]]
        s.zones.contains_key(zid1) && s.zones.contains_key(zid2) && zid1 != zid2
            && zone_iommu_private_pages(s.zones[zid1]).contains(
            p,
        ) implies !zone_iommu_private_pages(s.zones[zid2]).contains(p) by {
        if zone_iommu_private_pages(s.zones[zid2]).contains(p) {
            let gz1 = s.zones[zid1];
            let gz2 = s.zones[zid2];
            lemma_zone_iommu_private_pages_region_witness(gz1, p);
            lemma_zone_iommu_private_pages_region_witness(gz2, p);
            let r1 = choose|r: MemoryRegion|
                #![trigger gz1.iommu_mem_set.regions.contains(r)]
                gz1.iommu_mem_set.regions.contains(r) && region_owns_page(r, p) && r
                    != gic_region();
            let r2 = choose|r: MemoryRegion|
                #![trigger gz2.iommu_mem_set.regions.contains(r)]
                gz2.iommu_mem_set.regions.contains(r) && region_owns_page(r, p) && r
                    != gic_region();
            // inv_iommu_in_zone_regions + non-GIC => both are private zone regions.
            assert(zone_regions(zid1).contains(r1) || r1 == gic_region());
            assert(zone_regions(zid2).contains(r2) || r2 == gic_region());
            assert(zone_regions(zid1).contains(r1));
            assert(zone_regions(zid2).contains(r2));
            let i1 = choose|i: nat| 0 <= i < r1.pages && region_phys_page(r1, i) == p;
            let i2 = choose|i: nat| 0 <= i < r2.pages && region_phys_page(r2, i) == p;
            assert(r1.spec_valid() && r2.spec_valid());
            zone_regions_pairwise_disjoint();
            lemma_same_phys_page_implies_pmem_overlap(r1, i1, r2, i2);
        }
    }
}

/// **IOMMU vs CPU separation.** A **private** DMA page of one zone is never CPU-owned
/// by a *different* zone: private DMA regions and CPU regions are both zone-private and
/// pairwise pmem-disjoint across zones.  (A private DMA page is non-GIC, so its backing
/// region is a zone region, not the GIC — no GIC case arises here.)
pub proof fn lemma_state_iommu_cpu_disjoint(s: BudgetSpec::State)
    requires
        s.invariant(),
    ensures
        forall|zid1: nat, zid2: nat, p: PhysPage|
            #![trigger zone_iommu_private_pages(s.zones[zid1]).contains(p), s.zones[zid2]]
            s.zones.contains_key(zid1) && s.zones.contains_key(zid2) && zid1 != zid2
                && zone_iommu_private_pages(s.zones[zid1]).contains(p) ==> !zone_owned_pages(
                s.zones[zid2],
            ).contains(p),
{
    assert forall|zid1: nat, zid2: nat, p: PhysPage|
        #![trigger zone_iommu_private_pages(s.zones[zid1]).contains(p), s.zones[zid2]]
        s.zones.contains_key(zid1) && s.zones.contains_key(zid2) && zid1 != zid2
            && zone_iommu_private_pages(s.zones[zid1]).contains(p) implies !zone_owned_pages(
        s.zones[zid2],
    ).contains(p) by {
        if zone_owned_pages(s.zones[zid2]).contains(p) {
            let gz1 = s.zones[zid1];
            let gz2 = s.zones[zid2];
            lemma_zone_iommu_private_pages_region_witness(gz1, p);
            lemma_zone_owned_pages_region_witness(gz2, p);
            let r1 = choose|r: MemoryRegion|
                #![trigger gz1.iommu_mem_set.regions.contains(r)]
                gz1.iommu_mem_set.regions.contains(r) && region_owns_page(r, p) && r
                    != gic_region();
            let r2 = choose|r: MemoryRegion|
                #![trigger gz2.cpu_mem_set.regions.contains(r)]
                gz2.cpu_mem_set.regions.contains(r) && region_owns_page(r, p);
            // r1 is a private (non-GIC) region in zone_regions(zid1); r2 is a CPU
            // region in zone_regions(zid2).
            assert(zone_regions(zid1).contains(r1) || r1 == gic_region());
            assert(zone_regions(zid1).contains(r1));
            assert(zone_regions(zid2).contains(r2));
            let i1 = choose|i: nat| 0 <= i < r1.pages && region_phys_page(r1, i) == p;
            let i2 = choose|i: nat| 0 <= i < r2.pages && region_phys_page(r2, i) == p;
            assert(r1.spec_valid() && r2.spec_valid());
            zone_regions_pairwise_disjoint();
            lemma_same_phys_page_implies_pmem_overlap(r1, i1, r2, i2);
        }
    }
}

/// A state change that leaves every zone's `iommu_mem_set` (and the zone set)
/// untouched — e.g. any CPU-side region op — leaves the whole IOMMU projection
/// (`iommu_s2_map`, `iommu_owned`, `iommu_shared`) unchanged.
pub proof fn lemma_state_iommu_proj_unchanged(s1: SoftwareSpec, s2: SoftwareSpec)
    requires
        s1.budget.invariant(),
        s2.budget.invariant(),
        s2.budget.zone_ids == s1.budget.zone_ids,
        forall|zid: nat| #[trigger]
            s1.budget.zones.contains_key(zid) ==> s2.budget.zones[zid].iommu_mem_set
                == s1.budget.zones[zid].iommu_mem_set,
    ensures
        s2@.iommu_s2_map =~= s1@.iommu_s2_map,
        s2@.iommu_owned =~= s1@.iommu_owned,
        s2@.iommu_shared =~= s1@.iommu_shared,
{
    assert forall|k: VmPageKey|
        s2@.iommu_s2_map.contains_key(k) == s1@.iommu_s2_map.contains_key(k) && (
        s1@.iommu_s2_map.contains_key(k) ==> s2@.iommu_s2_map[k] == s1@.iommu_s2_map[k]) by {}
    assert forall|vm: VmId|
        s2@.iommu_owned.contains_key(vm) == s1@.iommu_owned.contains_key(vm) && (
        s1@.iommu_owned.contains_key(vm) ==> s2@.iommu_owned[vm] =~= s1@.iommu_owned[vm]) by {}
}

/// The dual of [`lemma_state_iommu_proj_unchanged`]: an op that leaves every zone's
/// `cpu_mem_set` (and the zone set) untouched leaves the whole CPU projection
/// (`all_vms`, `vm_owned`, `s2_map`, `hypervisor_owned`, `shared_pages`) unchanged.
pub proof fn lemma_state_cpu_proj_unchanged(s1: SoftwareSpec, s2: SoftwareSpec)
    requires
        s1.budget.invariant(),
        s2.budget.invariant(),
        s2.budget.zone_ids == s1.budget.zone_ids,
        forall|zid: nat| #[trigger]
            s1.budget.zones.contains_key(zid) ==> s2.budget.zones[zid].cpu_mem_set
                == s1.budget.zones[zid].cpu_mem_set,
    ensures
        s2@.all_vms =~= s1@.all_vms,
        s2@.vm_owned =~= s1@.vm_owned,
        s2@.s2_map =~= s1@.s2_map,
        s2@.hypervisor_owned =~= s1@.hypervisor_owned,
        s2@.shared_pages =~= s1@.shared_pages,
{
    assert forall|vm: VmId|
        s2@.vm_owned.contains_key(vm) == s1@.vm_owned.contains_key(vm) && (
        s1@.vm_owned.contains_key(vm) ==> s2@.vm_owned[vm] =~= s1@.vm_owned[vm]) by {}
    assert forall|k: VmPageKey|
        s2@.s2_map.contains_key(k) == s1@.s2_map.contains_key(k) && (s1@.s2_map.contains_key(k)
            ==> s2@.s2_map[k] == s1@.s2_map[k]) by {}
    // hypervisor_owned = all_budget \ all_owned; all_owned is the union of each zone's
    // `zone_owned_pages` (a function of `cpu_mem_set` only), so it is unchanged.
    assert(all_owned_pages(s2.budget.zones) =~= all_owned_pages(s1.budget.zones)) by {
        assert forall|p: PhysPage|
            all_owned_pages(s2.budget.zones).contains(p) <==> all_owned_pages(
                s1.budget.zones,
            ).contains(p) by {
            if all_owned_pages(s2.budget.zones).contains(p) {
                let z = choose|z: nat| #[trigger]
                    s2.budget.zones.contains_key(z) && zone_owned_pages(
                        s2.budget.zones[z],
                    ).contains(p);
                lemma_zone_owned_in_all_owned(s1.budget.zones, z, p);
            }
            if all_owned_pages(s1.budget.zones).contains(p) {
                let z = choose|z: nat| #[trigger]
                    s1.budget.zones.contains_key(z) && zone_owned_pages(
                        s1.budget.zones[z],
                    ).contains(p);
                lemma_zone_owned_in_all_owned(s2.budget.zones, z, p);
            }
        }
    }
}

/// **IOMMU memory separation + sharing for the implementation (step 3).** Every
/// reachable `BudgetSpec` state projects to a `SoftwareView` whose IOMMU model is
/// well-formed (`iommu_wf`): each VM's DMA is confined to its private, zone-disjoint
/// pages plus the shared GIC, and the GIC is the *only* page co-owned across VMs.
/// This is the model-level statement that the hypervisor's IOMMU/SMMU management
/// follows the intended separation-and-sharing design.
pub proof fn lemma_reachable_iommu_separation(s: SoftwareSpec)
    requires
        s.budget.invariant(),
    ensures
        s@.iommu_wf(),
{
    let sw = s@;
    assert(sw.iommu_owned.dom() =~= sw.all_vms);
    assert(sw.iommu_shared == gic_shared_pages_set());
    // Bridge: for an active VM, its projected `iommu_owned` set is exactly its private
    // DMA pages, and `iommu_shared` membership is exactly GIC-membership.
    assert forall|vm: VmId| sw.all_vms.contains(vm) implies #[trigger] sw.iommu_owned[vm]
        == zone_iommu_private_pages(s.budget.zones[vm.0]) by {}

    // iommu_translation_wf: every IOMMU entry targets a private DMA page or a shared GIC page.
    assert forall|key: VmPageKey| #[trigger] sw.iommu_s2_map.contains_key(key) implies (
    sw.all_vms.contains(key.vm) && sw.iommu_owned.contains_key(key.vm) && (
    sw.iommu_owned[key.vm].contains(sw.iommu_s2_map[key].page) || sw.iommu_shared.contains(
        sw.iommu_s2_map[key].page,
    ))) by {
        lemma_zone_iommu_s2_target_owned(key.vm.0, s.budget.zones[key.vm.0]);
        let p = sw.iommu_s2_map[key].page;
        // The entry's target is private (⇒ `iommu_owned[key.vm]`) or a GIC page (⇒ `iommu_shared`).
        if is_gic_page(p) {
        } else {
        }
    }
    assert(sw.iommu_translation_wf());

    // iommu_ownership_wf: (1) private DMA pages cross-VM disjoint; (2) never another VM's
    // CPU pages; (3) private DMA pages are disjoint from the shared GIC.
    lemma_state_iommu_private_disjoint(s.budget);
    lemma_state_iommu_cpu_disjoint(s.budget);
    // (1)
    assert forall|vm1: VmId, vm2: VmId| #[trigger]
        sw.all_vms.contains(vm1) && #[trigger] sw.all_vms.contains(vm2) && vm1 != vm2 implies (
    forall|page: PhysPage| #[trigger]
        sw.iommu_owned[vm1].contains(page) ==> !sw.iommu_owned[vm2].contains(page)) by {}
    // (2)
    assert forall|vm1: VmId, vm2: VmId| #[trigger]
        sw.all_vms.contains(vm1) && #[trigger] sw.all_vms.contains(vm2) && vm1 != vm2 implies (
    forall|page: PhysPage| #[trigger]
        sw.iommu_owned[vm1].contains(page) ==> !sw.vm_owned[vm2].contains(page)) by {}
    // (3) private pages are non-GIC by construction, so disjoint from `iommu_shared`.
    assert forall|vm: VmId| #[trigger] sw.all_vms.contains(vm) implies (forall|page: PhysPage|
     #[trigger]
        sw.iommu_owned[vm].contains(page) ==> !sw.iommu_shared.contains(page)) by {
        assert forall|page: PhysPage| #[trigger]
            sw.iommu_owned[vm].contains(page) implies !sw.iommu_shared.contains(page) by {
            assert(zone_iommu_private_pages(s.budget.zones[vm.0]).contains(page));
        }
    }
    // (4) CPU-owned pages are disjoint from the shared GIC: a CPU page is backed by a zone
    // region, and the GIC is pmem-disjoint from every zone's regions.
    assert forall|vm: VmId| #[trigger] sw.all_vms.contains(vm) implies (forall|page: PhysPage|
     #[trigger]
        sw.vm_owned[vm].contains(page) ==> !sw.iommu_shared.contains(page)) by {
        assert forall|page: PhysPage| #[trigger]
            sw.vm_owned[vm].contains(page) implies !sw.iommu_shared.contains(page) by {
            let gz = s.budget.zones[vm.0];
            lemma_zone_owned_pages_region_witness(gz, page);
            let r = choose|rr: MemoryRegion| #[trigger]
                gz.cpu_mem_set.regions.contains(rr) && region_owns_page(rr, page);
            assert(gz.cpu_mem_set.regions.contains(r));
            assert(zone_regions(vm.0).contains(r));
            configured_regions_valid();
            assert(r.spec_valid());
            if is_gic_page(page) {
                let i = choose|i: nat| 0 <= i < r.pages && region_phys_page(r, i) == page;
                let ig = choose|ig: nat|
                    0 <= ig < gic_region().pages && region_phys_page(gic_region(), ig) == page;
                gic_region_disjoint_from_zones();
                lemma_same_phys_page_implies_pmem_overlap(gic_region(), ig, r, i);
            }
        }
    }
    assert(sw.iommu_ownership_wf());
}

// ---------------------------------------------------------------------------
// §6  Transition-guard derivations
//
// The `BudgetSpec` transition guards (`!overlaps_vmem`, gpa-freshness, ...)
// derived from the closed `SoftwareView::*_enabled` preconditions.
// ---------------------------------------------------------------------------
/// Every page of a region present in a zone is owned by that zone.
pub proof fn lemma_region_in_zone_owns_pages(gz: GhostZone, r: MemoryRegion)
    requires
        gz.wf(),
        gz.cpu_mem_set.regions.contains(r),
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
    }
}

/// A guest page owned by a region present in a zone is mapped by that zone.
pub proof fn lemma_region_in_zone_maps_gpa(gz: GhostZone, r: MemoryRegion, g: GuestPage)
    requires
        gz.wf(),
        gz.cpu_mem_set.regions.contains(r),
        region_owns_gpa(r, g),
    ensures
        gz.cpu_mem_set.mappings.contains_key(vaddr_of_gpa(g)),
{
    assert(r.spec_valid());  // r ∈ regions, gz.wf() ⇒ valid
    let i = choose|i: nat| 0 <= i < r.pages && region_guest_page(r, i) == g;
    lemma_gpa_vaddr_roundtrip(r, i);  // vaddr_of_gpa(region_guest_page(r,i)) == spec_page_vaddr(i)
}

/// A guest page owned by an IOMMU region present in a zone is IOMMU-mapped by it.
pub proof fn lemma_iommu_region_in_zone_maps_gpa(gz: GhostZone, r: MemoryRegion, g: GuestPage)
    requires
        gz.wf(),
        gz.iommu_mem_set.regions.contains(r),
        region_owns_gpa(r, g),
    ensures
        gz.iommu_mem_set.mappings.contains_key(vaddr_of_gpa(g)),
{
    assert(r.spec_valid());
    let i = choose|i: nat| 0 <= i < r.pages && region_guest_page(r, i) == g;
    lemma_gpa_vaddr_roundtrip(r, i);
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

// ---------------------------------------------------------------------------
// §7  Per-op projection-delta lemmas
//
// For each region operation: how one zone's mutation (`gz ↦ gz.…_region(r)`)
// moves the §3 projections — owned pages, `all_owned_pages`, per-zone stage-2
// entries, and the whole-state stage-2 map.  Consumed exclusively by the §8
// transition methods.
// ---------------------------------------------------------------------------
// ── insert_region (gz ↦ gz.cpu_insert_region(r)) ────────────────────────────
/// Inserting `r` extends a zone's owned-page set by exactly `r`'s pages.
pub proof fn lemma_insert_region_owned_pages(gz: GhostZone, region: MemoryRegion)
    requires
        gz.wf(),
        region.spec_valid(),
        !gz.cpu_mem_set.overlaps_vmem(region),
    ensures
        zone_owned_pages(gz.cpu_insert_region(region)) =~= zone_owned_pages(gz).union(
            region_pages(region),
        ),
{
    let new_gz = gz.cpu_insert_region(region);
    let om = gz.cpu_mem_set.mappings;
    let rm = region.spec_mappings();

    // Key domains are disjoint.
    assert forall|v: SpecVAddr| om.contains_key(v) implies !rm.contains_key(v) by {
        if rm.contains_key(v) {
            region.lemma_mappings_sound(v);
            let j = choose|j: nat| 0 <= j < region.pages && v == region.spec_page_vaddr(j);
            let f = om[v];
            assert(om.contains_pair(v, f));
            let (r2, i2) = choose|r2: MemoryRegion, i2: nat|
                gz.cpu_mem_set.regions.contains(r2) && 0 <= i2 < r2.pages && v
                    == r2.spec_page_vaddr(i2) && f == r2.spec_frame(i2);
            assert(gz.cpu_mem_set.regions.contains(r2));
            assert(!r2.spec_overlaps_vmem(region));
            MemoryRegion::lemma_pages_disjoint(r2, region, i2, j);  // r2 page i2 != region page j == v
        }
    }

    assert forall|p: PhysPage|
        zone_owned_pages(new_gz).contains(p) <==> (zone_owned_pages(gz).contains(p) || region_pages(
            region,
        ).contains(p)) by {
        // (⟹)
        if zone_owned_pages(new_gz).contains(p) {
            let v = choose|v: SpecVAddr| #[trigger]
                new_gz.cpu_mem_set.mappings.contains_key(v) && frame_phys_page(
                    new_gz.cpu_mem_set.mappings[v],
                ) == p;
            if rm.contains_key(v) {
                region.lemma_mappings_sound(v);
                let i = choose|i: nat|
                    0 <= i < region.pages && v == region.spec_page_vaddr(i) && rm[v]
                        == region.spec_frame(i);
                assert(new_gz.cpu_mem_set.mappings[v] == rm[v]);
                assert(region_phys_page(region, i) == p);
                assert(region_owns_page(region, p));  // witness i
            } else {
                assert(om.contains_key(v) && new_gz.cpu_mem_set.mappings[v] == om[v]);
                assert(zone_owned_pages(gz).contains(p));  // witness v
            }
        }
        // (⟸ old)

        if zone_owned_pages(gz).contains(p) {
            let v = choose|v: SpecVAddr| #[trigger]
                om.contains_key(v) && frame_phys_page(om[v]) == p;
            assert(!rm.contains_key(v));
            assert(new_gz.cpu_mem_set.mappings.contains_key(v) && new_gz.cpu_mem_set.mappings[v]
                == om[v]);
            assert(zone_owned_pages(new_gz).contains(p));  // witness v
        }
        // (⟸ region)

        if region_pages(region).contains(p) {
            let i = choose|i: nat| 0 <= i < region.pages && region_phys_page(region, i) == p;
            region.lemma_mappings_contains_pair(i);
            let v = region.spec_page_vaddr(i);
            assert(rm.contains_pair(v, region.spec_frame(i)));
            assert(new_gz.cpu_mem_set.mappings.contains_key(v) && new_gz.cpu_mem_set.mappings[v]
                == region.spec_frame(i));
            assert(frame_phys_page(region.spec_frame(i)) == p);
            assert(zone_owned_pages(new_gz).contains(p));  // witness v
        }
    }
}

/// `all_owned_pages` grows by exactly the inserted region's pages (the
/// whole-state lift of [`lemma_insert_region_owned_pages`]).
pub proof fn lemma_insert_region_all_owned(zones: Map<nat, GhostZone>, zid: nat, r: MemoryRegion)
    requires
        zones.contains_key(zid),
        zones[zid].wf(),
        r.spec_valid(),
        !zones[zid].cpu_mem_set.overlaps_vmem(r),
    ensures
        all_owned_pages(zones.insert(zid, zones[zid].cpu_insert_region(r))) =~= all_owned_pages(
            zones,
        ).union(region_pages(r)),
{
    let zones2 = zones.insert(zid, zones[zid].cpu_insert_region(r));
    lemma_insert_region_owned_pages(zones[zid], r);

    assert forall|p: PhysPage|
        all_owned_pages(zones2).contains(p) <==> (all_owned_pages(zones).contains(p)
            || region_pages(r).contains(p)) by {
        // (⟹)
        if all_owned_pages(zones2).contains(p) {
            let z = choose|z: nat| #[trigger]
                zones2.contains_key(z) && zone_owned_pages(zones2[z]).contains(p);
            if z == zid {
                if zone_owned_pages(zones[zid]).contains(p) {
                    lemma_zone_owned_in_all_owned(zones, zid, p);
                }  // else p ∈ region_pages(r) directly

            } else {
                lemma_zone_owned_in_all_owned(zones, z, p);
            }
        }
        // (⟸ old)

        if all_owned_pages(zones).contains(p) {
            let z = choose|z: nat| #[trigger]
                zones.contains_key(z) && zone_owned_pages(zones[z]).contains(p);
            if z == zid {
                lemma_zone_owned_in_all_owned(zones2, zid, p);
            } else {
                lemma_zone_owned_in_all_owned(zones2, z, p);
            }
        }
        // (⟸ region)

        if region_pages(r).contains(p) {
            lemma_zone_owned_in_all_owned(zones2, zid, p);
        }
    }
}

/// A zone's stage-2 entries gain exactly the inserted region's entries.
pub proof fn lemma_insert_region_s2_entries(zid: nat, gz: GhostZone, r: MemoryRegion)
    requires
        gz.wf(),
        r.spec_valid(),
        !gz.cpu_mem_set.overlaps_vmem(r),
    ensures
        zone_s2_entries(zid, gz.cpu_insert_region(r)) =~= zone_s2_entries(
            zid,
            gz,
        ).union_prefer_right(region_s2_entries(zid, r)),
{
    let new_gz = gz.cpu_insert_region(r);
    let om = gz.cpu_mem_set.mappings;
    let rm = r.spec_mappings();
    let nm = new_gz.cpu_mem_set.mappings;
    let zg = zone_s2_entries(zid, gz);
    let re = region_s2_entries(zid, r);
    let lhs = zone_s2_entries(zid, new_gz);
    let rhs = zg.union_prefer_right(re);

    assert forall|k: VmPageKey| #[trigger] lhs.contains_key(k) <==> rhs.contains_key(k) by {
        lemma_region_gpa_mapped_iff(r, k.gpa);  // rm.contains_key(v) <==> region_owns_gpa(r, k.gpa)
    }
    assert forall|k: VmPageKey|
        #![trigger lhs[k]]
        #![trigger rhs[k]]
        lhs.contains_key(k) implies lhs[k] == rhs[k] by {
        let v = vaddr_of_gpa(k.gpa);
        lemma_region_gpa_mapped_iff(r, k.gpa);
        if rm.contains_key(v) {
            lemma_region_s2_value(zid, r, k);  // re.contains_key(k), re[k] == frame_to_s2(rm[v])
        } else {
        }
    }
}

/// The state's `s2_map` gains exactly the inserted region's entries.
pub proof fn lemma_insert_region_state_s2_map(
    pre: BudgetSpec::State,
    post: BudgetSpec::State,
    zid: nat,
    r: MemoryRegion,
)
    requires
        pre.invariant(),
        pre.zones.contains_key(zid),
        r.spec_valid(),
        !pre.zones[zid].cpu_mem_set.overlaps_vmem(r),
        post.zone_ids == pre.zone_ids,
        post.zones == pre.zones.insert(zid, pre.zones[zid].cpu_insert_region(r)),
    ensures
        state_s2_map(post) =~= state_s2_map(pre).union_prefer_right(region_s2_entries(zid, r)),
{
    let pre_z = pre.zones[zid];
    lemma_insert_region_s2_entries(zid, pre_z, r);
    // zone_s2_entries(zid, post.zones[zid]) == zone_s2_entries(zid, pre_z) ∪ region_s2_entries(zid, r)
    let re = region_s2_entries(zid, r);
    let lhs = state_s2_map(post);
    let rhs = state_s2_map(pre).union_prefer_right(re);

    assert forall|k: VmPageKey| #[trigger] lhs.contains_key(k) <==> rhs.contains_key(k) by {
        let z = k.vm.0;
        if z != zid {
        }
    }
    assert forall|k: VmPageKey|
        #![trigger lhs[k]]
        #![trigger rhs[k]]
        lhs.contains_key(k) implies lhs[k] == rhs[k] by {
        let z = k.vm.0;
        if z != zid {
        }
    }
}

// ── remove_region (gz ↦ gz.cpu_remove_region(r)) ────────────────────────────
/// Owned pages shrink by exactly the removed region's pages (needs
/// `region_pmem_exclusive`).
pub proof fn lemma_remove_region_owned_pages(gz: GhostZone, r: MemoryRegion)
    requires
        gz.wf(),
        gz.cpu_mem_set.regions.contains(r),
        region_pmem_exclusive(gz, r),
    ensures
        zone_owned_pages(gz.cpu_remove_region(r)) =~= zone_owned_pages(gz).difference(
            region_pages(r),
        ),
{
    let new_gz = gz.cpu_remove_region(r);
    let om = gz.cpu_mem_set.mappings;
    let rm = r.spec_mappings();
    let nm = new_gz.cpu_mem_set.mappings;
    assert(nm == om.remove_keys(rm.dom()));
    assert(r.spec_valid());  // r ∈ regions, gz.wf() ⇒ valid

    assert forall|p: PhysPage|
        zone_owned_pages(new_gz).contains(p) <==> (zone_owned_pages(gz).contains(p)
            && !region_pages(r).contains(p)) by {
        // (⟹)
        if zone_owned_pages(new_gz).contains(p) {
            let v = choose|v: SpecVAddr| #[trigger]
                nm.contains_key(v) && frame_phys_page(nm[v]) == p;
            assert(om.contains_key(v) && !rm.contains_key(v) && nm[v] == om[v]);
            assert(zone_owned_pages(gz).contains(p));  // witness v
            if region_pages(r).contains(p) {
                let i = choose|i: nat| 0 <= i < r.pages && region_phys_page(r, i) == p;
                let f = om[v];
                assert(om.contains_pair(v, f));
                let (r2, i2) = choose|r2: MemoryRegion, i2: nat|
                    gz.cpu_mem_set.regions.contains(r2) && 0 <= i2 < r2.pages && v
                        == r2.spec_page_vaddr(i2) && f == r2.spec_frame(i2);
                assert(gz.cpu_mem_set.regions.contains(r2));
                assert(region_phys_page(r2, i2) == p);
                if r2 == r {
                    r.lemma_mappings_contains_pair(i2);  // ⇒ v ∈ rm.dom(): contradiction
                }
                assert(r2 != r);
                assert(r2.spec_valid());
                assert(!r2.spec_overlaps_pmem(r));  // region_pmem_exclusive
                assert(gz.cpu_mem_set.regions.contains(r));  // from contains_region(r)
                lemma_same_phys_page_implies_pmem_overlap(r2, i2, r, i);
            }
        }
        // (⟸)

        if zone_owned_pages(gz).contains(p) && !region_pages(r).contains(p) {
            let v = choose|v: SpecVAddr| #[trigger]
                om.contains_key(v) && frame_phys_page(om[v]) == p;
            if rm.contains_key(v) {
                r.lemma_mappings_sound(v);
                let i = choose|i: nat|
                    0 <= i < r.pages && v == r.spec_page_vaddr(i) && rm[v] == r.spec_frame(i);
                // gz.wf() completeness pins om[v] to r's frame, so p is one of r's pages.
                assert(gz.cpu_mem_set.regions.contains(r));
                assert(om.contains_pair(r.spec_page_vaddr(i), r.spec_frame(i)));
                assert(om[v] == r.spec_frame(i));
                assert(region_phys_page(r, i) == p);
                assert(region_pages(r).contains(p));  // witness i: contradiction
                assert(false);
            }
            assert(nm.contains_key(v) && nm[v] == om[v]);
            assert(zone_owned_pages(new_gz).contains(p));  // witness v
        }
    }
}

/// `all_owned_pages` shrinks by exactly the removed region's pages (the
/// whole-state lift of [`lemma_remove_region_owned_pages`]).
pub proof fn lemma_remove_region_all_owned(pre: BudgetSpec::State, zid: nat, r: MemoryRegion)
    requires
        pre.invariant(),
        pre.zones.contains_key(zid),
        pre.zones[zid].cpu_mem_set.regions.contains(r),
        region_pmem_exclusive(pre.zones[zid], r),
    ensures
        all_owned_pages(pre.zones.insert(zid, pre.zones[zid].cpu_remove_region(r)))
            =~= all_owned_pages(pre.zones).difference(region_pages(r)),
{
    let zones = pre.zones;
    let zones2 = zones.insert(zid, zones[zid].cpu_remove_region(r));
    lemma_remove_region_owned_pages(zones[zid], r);
    lemma_state_owned_pages_disjoint(pre);

    // Every page of `r` is owned by `zid`.
    lemma_region_in_zone_owns_pages(zones[zid], r);

    assert forall|p: PhysPage|
        all_owned_pages(zones2).contains(p) <==> (all_owned_pages(zones).contains(p)
            && !region_pages(r).contains(p)) by {
        // (⟹)
        if all_owned_pages(zones2).contains(p) {
            let z = choose|z: nat| #[trigger]
                zones2.contains_key(z) && zone_owned_pages(zones2[z]).contains(p);
            if z == zid {
                // p ∈ zone_owned(zones[zid]) \ region_pages(r): owned & not r's.
                lemma_zone_owned_in_all_owned(zones, zid, p);
            } else {
                lemma_zone_owned_in_all_owned(zones, z, p);
                // p ∉ region_pages(r): else `zid` and `z` would both own p.
                if region_pages(r).contains(p) {
                    assert(zone_owned_pages(zones[zid]).contains(p));
                    assert(zone_owned_pages(zones[z]).contains(p));
                    assert(false);  // cross-zone disjointness
                }
            }
        }
        // (⟸)

        if all_owned_pages(zones).contains(p) && !region_pages(r).contains(p) {
            let z = choose|z: nat| #[trigger]
                zones.contains_key(z) && zone_owned_pages(zones[z]).contains(p);
            if z == zid {
                lemma_zone_owned_in_all_owned(zones2, zid, p);
            } else {
                lemma_zone_owned_in_all_owned(zones2, z, p);
            }
        }
    }
}

/// A zone's stage-2 entries lose exactly the removed region's keys.
pub proof fn lemma_remove_region_s2_entries(zid: nat, gz: GhostZone, r: MemoryRegion)
    requires
        gz.wf(),
        gz.cpu_mem_set.regions.contains(r),
    ensures
        zone_s2_entries(zid, gz.cpu_remove_region(r)) =~= zone_s2_entries(zid, gz).remove_keys(
            region_s2_entries(zid, r).dom(),
        ),
{
    let new_gz = gz.cpu_remove_region(r);
    let om = gz.cpu_mem_set.mappings;
    let rm = r.spec_mappings();
    let nm = new_gz.cpu_mem_set.mappings;
    assert(nm == om.remove_keys(rm.dom()));
    assert(r.spec_valid());  // r ∈ regions, gz.wf() ⇒ valid
    let zg = zone_s2_entries(zid, gz);
    let re = region_s2_entries(zid, r);
    let lhs = zone_s2_entries(zid, new_gz);
    let rhs = zg.remove_keys(re.dom());

    assert forall|k: VmPageKey| #[trigger] lhs.contains_key(k) <==> rhs.contains_key(k) by {
        lemma_region_gpa_mapped_iff(r, k.gpa);  // rm.contains_key(v) <==> region_owns_gpa(r, k.gpa)
    }
    assert forall|k: VmPageKey|
        #![trigger lhs[k]]
        #![trigger rhs[k]]
        lhs.contains_key(k) implies lhs[k] == rhs[k] by {
        let v = vaddr_of_gpa(k.gpa);
    }
}

/// The state's `s2_map` loses exactly the removed region's keys.
pub proof fn lemma_remove_region_state_s2_map(
    pre: BudgetSpec::State,
    post: BudgetSpec::State,
    zid: nat,
    r: MemoryRegion,
)
    requires
        pre.invariant(),
        pre.zones.contains_key(zid),
        pre.zones[zid].cpu_mem_set.regions.contains(r),
        post.zone_ids == pre.zone_ids,
        post.zones == pre.zones.insert(zid, pre.zones[zid].cpu_remove_region(r)),
    ensures
        state_s2_map(post) =~= state_s2_map(pre).remove_keys(region_s2_entries(zid, r).dom()),
{
    let pre_z = pre.zones[zid];
    lemma_remove_region_s2_entries(zid, pre_z, r);
    // zone_s2_entries(zid, post.zones[zid]) == zone_s2_entries(zid, pre_z).remove_keys(re.dom())
    let re = region_s2_entries(zid, r);
    let lhs = state_s2_map(post);
    let rhs = state_s2_map(pre).remove_keys(re.dom());

    assert forall|k: VmPageKey| #[trigger] lhs.contains_key(k) <==> rhs.contains_key(k) by {
        let z = k.vm.0;
        if z != zid {
        }
    }
    assert forall|k: VmPageKey|
        #![trigger lhs[k]]
        #![trigger rhs[k]]
        lhs.contains_key(k) implies lhs[k] == rhs[k] by {
        let z = k.vm.0;
        if z != zid {
        }
    }
}

// ── iommu_insert_region (gz ↦ gz.iommu_insert_region(r)) ────────────────────
/// Private DMA pages grow by exactly the inserted region's pages (which are all
/// non-GIC, so none is excluded by the `is_gic_page` filter).
pub proof fn lemma_iommu_insert_region_private_pages(gz: GhostZone, region: MemoryRegion)
    requires
        gz.wf(),
        region.spec_valid(),
        !gz.iommu_mem_set.overlaps_vmem(region),
        forall|p: PhysPage| #[trigger] region_pages(region).contains(p) ==> !is_gic_page(p),
    ensures
        zone_iommu_private_pages(gz.iommu_insert_region(region)) =~= zone_iommu_private_pages(
            gz,
        ).union(region_pages(region)),
{
    let new_gz = gz.iommu_insert_region(region);
    let om = gz.iommu_mem_set.mappings;
    let rm = region.spec_mappings();

    assert forall|v: SpecVAddr| om.contains_key(v) implies !rm.contains_key(v) by {
        if rm.contains_key(v) {
            region.lemma_mappings_sound(v);
            let j = choose|j: nat| 0 <= j < region.pages && v == region.spec_page_vaddr(j);
            let f = om[v];
            assert(om.contains_pair(v, f));
            let (r2, i2) = choose|r2: MemoryRegion, i2: nat|
                gz.iommu_mem_set.regions.contains(r2) && 0 <= i2 < r2.pages && v
                    == r2.spec_page_vaddr(i2) && f == r2.spec_frame(i2);
            assert(gz.iommu_mem_set.regions.contains(r2));
            assert(!r2.spec_overlaps_vmem(region));
            MemoryRegion::lemma_pages_disjoint(r2, region, i2, j);
        }
    }

    assert forall|p: PhysPage|
        zone_iommu_private_pages(new_gz).contains(p) <==> (zone_iommu_private_pages(gz).contains(p)
            || region_pages(region).contains(p)) by {
        // (⟹)
        if zone_iommu_private_pages(new_gz).contains(p) {
            let v = choose|v: SpecVAddr| #[trigger]
                new_gz.iommu_mem_set.mappings.contains_key(v) && frame_phys_page(
                    new_gz.iommu_mem_set.mappings[v],
                ) == p;
            if rm.contains_key(v) {
                region.lemma_mappings_sound(v);
                let i = choose|i: nat|
                    0 <= i < region.pages && v == region.spec_page_vaddr(i) && rm[v]
                        == region.spec_frame(i);
                assert(new_gz.iommu_mem_set.mappings[v] == rm[v]);
                assert(region_phys_page(region, i) == p);
                assert(region_owns_page(region, p));  // witness i
            } else {
                assert(om.contains_key(v) && new_gz.iommu_mem_set.mappings[v] == om[v]);
                assert(zone_iommu_private_pages(gz).contains(p));  // witness v
            }
        }
        // (⟸ old)

        if zone_iommu_private_pages(gz).contains(p) {
            assert(!is_gic_page(p));
            let v = choose|v: SpecVAddr| #[trigger]
                om.contains_key(v) && frame_phys_page(om[v]) == p;
            assert(!rm.contains_key(v));
            assert(new_gz.iommu_mem_set.mappings.contains_key(v) && new_gz.iommu_mem_set.mappings[v]
                == om[v]);
            assert(zone_iommu_private_pages(new_gz).contains(p));  // witness v
        }
        // (⟸ region)

        if region_pages(region).contains(p) {
            assert(!is_gic_page(p));  // hypothesis
            let i = choose|i: nat| 0 <= i < region.pages && region_phys_page(region, i) == p;
            region.lemma_mappings_contains_pair(i);
            let v = region.spec_page_vaddr(i);
            assert(rm.contains_pair(v, region.spec_frame(i)));
            assert(new_gz.iommu_mem_set.mappings.contains_key(v) && new_gz.iommu_mem_set.mappings[v]
                == region.spec_frame(i));
            assert(frame_phys_page(region.spec_frame(i)) == p);
            assert(zone_iommu_private_pages(new_gz).contains(p));  // witness v
        }
    }
}

/// A zone's IOMMU stage-2 entries gain exactly the inserted region's entries.
pub proof fn lemma_iommu_insert_region_s2_entries(zid: nat, gz: GhostZone, r: MemoryRegion)
    requires
        gz.wf(),
        r.spec_valid(),
        !gz.iommu_mem_set.overlaps_vmem(r),
    ensures
        zone_iommu_s2_entries(zid, gz.iommu_insert_region(r)) =~= zone_iommu_s2_entries(
            zid,
            gz,
        ).union_prefer_right(region_s2_entries(zid, r)),
{
    let new_gz = gz.iommu_insert_region(r);
    let om = gz.iommu_mem_set.mappings;
    let rm = r.spec_mappings();
    let nm = new_gz.iommu_mem_set.mappings;
    let zg = zone_iommu_s2_entries(zid, gz);
    let re = region_s2_entries(zid, r);
    let lhs = zone_iommu_s2_entries(zid, new_gz);
    let rhs = zg.union_prefer_right(re);

    assert forall|k: VmPageKey| #[trigger] lhs.contains_key(k) <==> rhs.contains_key(k) by {
        lemma_region_gpa_mapped_iff(r, k.gpa);
    }
    assert forall|k: VmPageKey|
        #![trigger lhs[k]]
        #![trigger rhs[k]]
        lhs.contains_key(k) implies lhs[k] == rhs[k] by {
        let v = vaddr_of_gpa(k.gpa);
        lemma_region_gpa_mapped_iff(r, k.gpa);
        if rm.contains_key(v) {
            lemma_region_s2_value(zid, r, k);
        } else {
        }
    }
}

/// The state's IOMMU `iommu_s2_map` gains exactly the inserted region's entries.
pub proof fn lemma_iommu_insert_region_state_iommu_s2_map(
    pre: BudgetSpec::State,
    post: BudgetSpec::State,
    zid: nat,
    r: MemoryRegion,
)
    requires
        pre.invariant(),
        pre.zones.contains_key(zid),
        r.spec_valid(),
        !pre.zones[zid].iommu_mem_set.overlaps_vmem(r),
        post.zone_ids == pre.zone_ids,
        post.zones == pre.zones.insert(zid, pre.zones[zid].iommu_insert_region(r)),
    ensures
        state_iommu_s2_map(post) =~= state_iommu_s2_map(pre).union_prefer_right(
            region_s2_entries(zid, r),
        ),
{
    let pre_z = pre.zones[zid];
    lemma_iommu_insert_region_s2_entries(zid, pre_z, r);
    let re = region_s2_entries(zid, r);
    let lhs = state_iommu_s2_map(post);
    let rhs = state_iommu_s2_map(pre).union_prefer_right(re);

    assert forall|k: VmPageKey| #[trigger] lhs.contains_key(k) <==> rhs.contains_key(k) by {
        let z = k.vm.0;
        if z != zid {
        }
    }
    assert forall|k: VmPageKey|
        #![trigger lhs[k]]
        #![trigger rhs[k]]
        lhs.contains_key(k) implies lhs[k] == rhs[k] by {
        let z = k.vm.0;
        if z != zid {
        }
    }
}

// ── iommu_remove_region (gz ↦ gz.iommu_remove_region(r)) ────────────────────
/// Private DMA pages shrink by exactly the removed region's pages.
pub proof fn lemma_iommu_remove_region_private_pages(gz: GhostZone, r: MemoryRegion)
    requires
        gz.wf(),
        gz.iommu_mem_set.regions.contains(r),
        region_iommu_pmem_exclusive(gz, r),
    ensures
        zone_iommu_private_pages(gz.iommu_remove_region(r)) =~= zone_iommu_private_pages(
            gz,
        ).difference(region_pages(r)),
{
    let new_gz = gz.iommu_remove_region(r);
    let om = gz.iommu_mem_set.mappings;
    let rm = r.spec_mappings();
    let nm = new_gz.iommu_mem_set.mappings;
    assert(nm == om.remove_keys(rm.dom()));
    assert(r.spec_valid());

    assert forall|p: PhysPage|
        zone_iommu_private_pages(new_gz).contains(p) <==> (zone_iommu_private_pages(gz).contains(p)
            && !region_pages(r).contains(p)) by {
        // (⟹)
        if zone_iommu_private_pages(new_gz).contains(p) {
            assert(!is_gic_page(p));
            let v = choose|v: SpecVAddr| #[trigger]
                nm.contains_key(v) && frame_phys_page(nm[v]) == p;
            assert(om.contains_key(v) && !rm.contains_key(v) && nm[v] == om[v]);
            assert(zone_iommu_private_pages(gz).contains(p));  // witness v
            if region_pages(r).contains(p) {
                let i = choose|i: nat| 0 <= i < r.pages && region_phys_page(r, i) == p;
                let f = om[v];
                assert(om.contains_pair(v, f));
                let (r2, i2) = choose|r2: MemoryRegion, i2: nat|
                    gz.iommu_mem_set.regions.contains(r2) && 0 <= i2 < r2.pages && v
                        == r2.spec_page_vaddr(i2) && f == r2.spec_frame(i2);
                assert(gz.iommu_mem_set.regions.contains(r2));
                assert(region_phys_page(r2, i2) == p);
                if r2 == r {
                    r.lemma_mappings_contains_pair(i2);
                }
                assert(r2 != r);
                assert(r2.spec_valid());
                assert(!r2.spec_overlaps_pmem(r));  // region_iommu_pmem_exclusive
                assert(gz.iommu_mem_set.regions.contains(r));
                lemma_same_phys_page_implies_pmem_overlap(r2, i2, r, i);
            }
        }
        // (⟸)

        if zone_iommu_private_pages(gz).contains(p) && !region_pages(r).contains(p) {
            assert(!is_gic_page(p));
            let v = choose|v: SpecVAddr| #[trigger]
                om.contains_key(v) && frame_phys_page(om[v]) == p;
            if rm.contains_key(v) {
                r.lemma_mappings_sound(v);
                let i = choose|i: nat|
                    0 <= i < r.pages && v == r.spec_page_vaddr(i) && rm[v] == r.spec_frame(i);
                assert(gz.iommu_mem_set.regions.contains(r));
                assert(om.contains_pair(r.spec_page_vaddr(i), r.spec_frame(i)));
                assert(om[v] == r.spec_frame(i));
                assert(region_phys_page(r, i) == p);
                assert(region_pages(r).contains(p));  // contradiction
                assert(false);
            }
            assert(nm.contains_key(v) && nm[v] == om[v]);
            assert(zone_iommu_private_pages(new_gz).contains(p));  // witness v
        }
    }
}

/// A zone's IOMMU stage-2 entries lose exactly the removed region's keys.
pub proof fn lemma_iommu_remove_region_s2_entries(zid: nat, gz: GhostZone, r: MemoryRegion)
    requires
        gz.wf(),
        gz.iommu_mem_set.regions.contains(r),
    ensures
        zone_iommu_s2_entries(zid, gz.iommu_remove_region(r)) =~= zone_iommu_s2_entries(
            zid,
            gz,
        ).remove_keys(region_s2_entries(zid, r).dom()),
{
    let new_gz = gz.iommu_remove_region(r);
    let om = gz.iommu_mem_set.mappings;
    let rm = r.spec_mappings();
    let nm = new_gz.iommu_mem_set.mappings;
    assert(nm == om.remove_keys(rm.dom()));
    assert(r.spec_valid());
    let zg = zone_iommu_s2_entries(zid, gz);
    let re = region_s2_entries(zid, r);
    let lhs = zone_iommu_s2_entries(zid, new_gz);
    let rhs = zg.remove_keys(re.dom());

    assert forall|k: VmPageKey| #[trigger] lhs.contains_key(k) <==> rhs.contains_key(k) by {
        lemma_region_gpa_mapped_iff(r, k.gpa);
    }
    assert forall|k: VmPageKey|
        #![trigger lhs[k]]
        #![trigger rhs[k]]
        lhs.contains_key(k) implies lhs[k] == rhs[k] by {
        let v = vaddr_of_gpa(k.gpa);
    }
}

/// The state's IOMMU `iommu_s2_map` loses exactly the removed region's keys.
pub proof fn lemma_iommu_remove_region_state_iommu_s2_map(
    pre: BudgetSpec::State,
    post: BudgetSpec::State,
    zid: nat,
    r: MemoryRegion,
)
    requires
        pre.invariant(),
        pre.zones.contains_key(zid),
        pre.zones[zid].iommu_mem_set.regions.contains(r),
        post.zone_ids == pre.zone_ids,
        post.zones == pre.zones.insert(zid, pre.zones[zid].iommu_remove_region(r)),
    ensures
        state_iommu_s2_map(post) =~= state_iommu_s2_map(pre).remove_keys(
            region_s2_entries(zid, r).dom(),
        ),
{
    let pre_z = pre.zones[zid];
    lemma_iommu_remove_region_s2_entries(zid, pre_z, r);
    let re = region_s2_entries(zid, r);
    let lhs = state_iommu_s2_map(post);
    let rhs = state_iommu_s2_map(pre).remove_keys(re.dom());

    assert forall|k: VmPageKey| #[trigger] lhs.contains_key(k) <==> rhs.contains_key(k) by {
        let z = k.vm.0;
        if z != zid {
        }
    }
    assert forall|k: VmPageKey|
        #![trigger lhs[k]]
        #![trigger rhs[k]]
        lhs.contains_key(k) implies lhs[k] == rhs[k] by {
        let z = k.vm.0;
        if z != zid {
        }
    }
}

// ---------------------------------------------------------------------------
// §8  The refinement contract + its implementation
// ---------------------------------------------------------------------------
/// Specification trait for hypervisor software state management — the refinement
/// contract whose methods fire the matching [`SoftwareView`] transitions.
///
/// A **ghost contract**: a concrete `T: View<V = SoftwareView>` represents the
/// hypervisor's abstract memory state, and each transition is a `proof fn` taking
/// `self` by value whose effect on the view is the matching `SoftwareView` step.
/// The implementing type is [`SoftwareSpec`] (impl below), so `invariants()` is
/// the wrapped state machine's real, inductively-proven `invariant()`.
/// Each precondition is the closed `SoftwareView::*_enabled` predicate, owned by the
/// trusted model.
pub trait SoftwareRefinement: View<V = SoftwareView> + Sized {
    /// Internal consistency predicate, established at construction and preserved.
    spec fn invariants(&self) -> bool;

    /// Invariants imply the abstract state is well-formed.
    broadcast proof fn inv_implies_wf(&self)
        requires
            #[trigger] self.invariants(),
        ensures
            self@.wf(),
    ;

    /// Invariants imply the IOMMU model is well-formed (cross-VM DMA separation +
    /// translation confinement).  Kept separate from [`inv_implies_wf`](Self::inv_implies_wf)
    /// so consumers can use the DMA-isolation fact directly at the refinement
    /// boundary.
    broadcast proof fn inv_implies_iommu_wf(&self)
        requires
            #[trigger] self.invariants(),
        ensures
            self@.iommu_wf(),
    ;

    /// Register a fresh, empty VM.
    proof fn add_vm(self, vm: VmId) -> (post: Self)
        requires
            self.invariants(),
            SoftwareView::add_vm_enabled(self@, vm),
        ensures
            post.invariants(),
            SoftwareView::add_vm_step(self@, post@, vm),
    ;

    /// Deregister a VM that owns no pages, has no mappings, and shares nothing.
    proof fn remove_vm(self, vm: VmId) -> (post: Self)
        requires
            self.invariants(),
            SoftwareView::remove_vm_enabled(self@, vm),
        ensures
            post.invariants(),
            SoftwareView::remove_vm_step(self@, post@, vm),
    ;

    /// Assign `region`'s pages to its VM and install its stage-2 entries.
    proof fn insert_region(self, region: Region) -> (post: Self)
        requires
            self.invariants(),
            SoftwareView::insert_region_enabled(self@, region),
        ensures
            post.invariants(),
            SoftwareView::insert_region_step(self@, post@, region),
    ;

    /// Unmap `region`'s entries and reclaim its pages back to the hypervisor pool.
    proof fn remove_region(self, region: Region) -> (post: Self)
        requires
            self.invariants(),
            SoftwareView::remove_region_enabled(self@, region),
        ensures
            post.invariants(),
            SoftwareView::remove_region_step(self@, post@, region),
    ;

    /// Grant `region`'s pages to its VM for DMA and install its IOMMU stage-2 entries.
    proof fn iommu_insert_region(self, region: Region) -> (post: Self)
        requires
            self.invariants(),
            SoftwareView::iommu_insert_region_enabled(self@, region),
        ensures
            post.invariants(),
            SoftwareView::iommu_insert_region_step(self@, post@, region),
    ;

    /// Unmap `region`'s IOMMU entries and reclaim its pages from the VM's DMA ownership.
    proof fn iommu_remove_region(self, region: Region) -> (post: Self)
        requires
            self.invariants(),
            SoftwareView::iommu_remove_region_enabled(self@, region),
        ensures
            post.invariants(),
            SoftwareView::iommu_remove_region_step(self@, post@, region),
    ;
}

impl SoftwareRefinement for SoftwareSpec {
    /// The contract invariant is the wrapped state machine's real invariant.
    open spec fn invariants(&self) -> bool {
        self.budget.invariant()
    }

    broadcast proof fn inv_implies_wf(&self)
        ensures
            #[trigger] self@.wf(),
    {
        let sw = self.view();
        // sharing_wf: vacuous (the CPU sharing graph is empty; GIC sharing is modeled
        // separately via `iommu_shared`, see `lemma_reachable_iommu_separation`).
        assert(sw.shared_pages =~= Set::<SharedPage>::empty());
        assert(sw.sharing_wf());

        // ownership_wf: dom; cross-zone disjointness; vm-vs-hypervisor disjointness.
        assert(sw.vm_owned.dom() =~= sw.all_vms);
        lemma_state_owned_pages_disjoint(self.budget);
        assert forall|vm: VmId, page: PhysPage|
            sw.all_vms.contains(vm) && #[trigger] sw.vm_owned[vm].contains(
                page,
            ) implies !sw.hypervisor_owned.contains(page) by {
            // vm.0 ∈ zones.dom (inv_zone_ids) and page ∈ zone_owned ⇒ all_owned ⇒ not in pool.
            lemma_zone_owned_in_all_owned(self.budget.zones, vm.0, page);
        }
        assert(sw.ownership_wf());

        // translation_wf.
        assert forall|key: VmPageKey| #[trigger] sw.s2_map.contains_key(key) implies (
        sw.all_vms.contains(key.vm) && sw.owned_or_shared(key.vm, sw.s2_map[key].page)) by {
            lemma_zone_s2_target_owned(key.vm.0, self.budget.zones[key.vm.0]);
        }
        assert(sw.translation_wf());

        // iommu_wf (now part of `wf`): DMA separation for every reachable state.
        lemma_reachable_iommu_separation(*self);
    }

    broadcast proof fn inv_implies_iommu_wf(&self)
        ensures
            #[trigger] self@.iommu_wf(),
    {
        lemma_reachable_iommu_separation(*self);
    }

    proof fn add_vm(self, vm: VmId) -> (post: Self) {
        // Fire the `add_zone` macro transition; `post.invariant()` comes from the macro.
        let empty_zone = GhostZone {
            cpu_mem_set: SpecMemorySet {
                regions: Set::<MemoryRegion>::empty(),
                mappings: Map::empty(),
            },
            iommu_mem_set: SpecMemorySet {
                regions: Set::<MemoryRegion>::empty(),
                mappings: Map::empty(),
            },
        };
        let post = SoftwareSpec { budget: BudgetSpec::take_step::add_zone(self.budget, vm.0) };
        assert(post.budget.zones == self.budget.zones.insert(vm.0, empty_zone));
        lemma_zone_owned_pages_empty(empty_zone);
        lemma_zone_s2_entries_empty(vm.0, empty_zone);
        // The new zone owns nothing, so all_owned is unchanged.
        assert(all_owned_pages(post.budget.zones) =~= all_owned_pages(self.budget.zones)) by {
            assert forall|pp: PhysPage|
                all_owned_pages(post.budget.zones).contains(pp) implies all_owned_pages(
                self.budget.zones,
            ).contains(pp) by {
                let zid = choose|zid: nat|
                    #![auto]
                    post.budget.zones.contains_key(zid) && zone_owned_pages(
                        post.budget.zones[zid],
                    ).contains(pp);
                lemma_zone_owned_in_all_owned(self.budget.zones, zid, pp);
            }
            assert forall|pp: PhysPage|
                all_owned_pages(self.budget.zones).contains(pp) implies all_owned_pages(
                post.budget.zones,
            ).contains(pp) by {
                let zid = choose|zid: nat|
                    #![auto]
                    self.budget.zones.contains_key(zid) && zone_owned_pages(
                        self.budget.zones[zid],
                    ).contains(pp);
                lemma_zone_owned_in_all_owned(post.budget.zones, zid, pp);
            }
        }
        assert(post@.hypervisor_owned =~= self@.hypervisor_owned);
        assert(post@.all_vms =~= self@.all_vms.insert(vm));
        assert(post@.vm_owned =~= self@.vm_owned.insert(vm, Set::empty()));
        assert(post@.s2_map =~= self@.s2_map);
        // IOMMU projection: the fresh zone has an empty `iommu_mem_set`, so it adds an
        // empty private-DMA set and no IOMMU entries; the shared GIC set is VM-independent.
        lemma_zone_iommu_private_pages_empty(empty_zone);
        lemma_zone_iommu_s2_entries_empty(vm.0, empty_zone);
        assert(post@.iommu_owned =~= self@.iommu_owned.insert(vm, Set::empty()));
        assert(post@.iommu_s2_map =~= self@.iommu_s2_map);
        post
    }

    proof fn remove_vm(self, vm: VmId) -> (post: Self) {
        // Fire the `remove_zone` macro transition; `post.invariant()` comes from the macro.
        let post = SoftwareSpec { budget: BudgetSpec::take_step::remove_zone(self.budget, vm.0) };
        assert(post.budget.zone_ids == self.budget.zone_ids.remove(vm.0));
        assert(post.budget.zones == self.budget.zones.remove(vm.0));
        // The removed zone owned nothing (precondition), so all_owned is unchanged.
        assert(zone_owned_pages(self.budget.zones[vm.0]) =~= Set::<PhysPage>::empty());
        assert(all_owned_pages(post.budget.zones) =~= all_owned_pages(self.budget.zones)) by {
            assert forall|pp: PhysPage|
                all_owned_pages(self.budget.zones).contains(pp) implies all_owned_pages(
                post.budget.zones,
            ).contains(pp) by {
                let zid = choose|zid: nat|
                    #![auto]
                    self.budget.zones.contains_key(zid) && zone_owned_pages(
                        self.budget.zones[zid],
                    ).contains(pp);
                lemma_zone_owned_in_all_owned(post.budget.zones, zid, pp);
            }
            assert forall|pp: PhysPage|
                all_owned_pages(post.budget.zones).contains(pp) implies all_owned_pages(
                self.budget.zones,
            ).contains(pp) by {
                let zid = choose|zid: nat|
                    #![auto]
                    post.budget.zones.contains_key(zid) && zone_owned_pages(
                        post.budget.zones[zid],
                    ).contains(pp);
                lemma_zone_owned_in_all_owned(self.budget.zones, zid, pp);
            }
        }
        assert(post@.hypervisor_owned =~= self@.hypervisor_owned);
        assert(post@.all_vms =~= self@.all_vms.remove(vm));
        assert(post@.vm_owned =~= self@.vm_owned.remove(vm));
        assert(post@.s2_map =~= self@.s2_map);
        // IOMMU projection: `vm` owned nothing for DMA and mapped nothing (enabling), so
        // dropping the zone removes an empty private-DMA set and no IOMMU entries.
        assert(post@.iommu_owned =~= self@.iommu_owned.remove(vm));
        assert(post@.iommu_s2_map =~= self@.iommu_s2_map);
        post
    }

    proof fn insert_region(self, region: Region) -> (post: Self) {
        let vm = region.vm;
        let zid = vm.0;

        // (1) Recover the budget region via the trusted environment bridge.
        axiom_assignable_from_budget(self, region);
        let r = choose|r: MemoryRegion| #[trigger]
            zone_regions(zid).contains(r) && region_to_abstract(zid, r) == region;
        configured_regions_valid();
        assert(r.spec_valid());

        // (2) Projection equalities: the abstract region projects to `r`'s pages/entries.
        lemma_region_to_abstract_pages(zid, r);
        lemma_region_to_abstract_entries(zid, r);

        // (3) The transition guards, derived from `insert_region_enabled`.
        let gz = self.budget.zones[zid];
        assert(gz.wf());  // inv_zones_wf
        let p0 = region.phys_page(0);
        assert(region.wf());  // enabled ⇒ count > 0
        assert(region.pages().contains(p0));
        // !contains_region(r): r's pages are free, but a contained region's pages are owned.
        if gz.cpu_mem_set.regions.contains(r) {
            lemma_region_in_zone_owns_pages(gz, r);
            assert(zone_owned_pages(gz).contains(p0));
            lemma_zone_owned_in_all_owned(self.budget.zones, zid, p0);  // p0 ∈ all_owned
            assert(self@.hypervisor_owned.contains(p0));  // enabled
            assert(self@.hypervisor_owned == hypervisor_pool(self.budget.zones));  // pool = budget \ owned
            assert(false);
        }
        // !overlaps_vmem(r): an overlapping zone region shares a gpa, which is mapped.

        if gz.cpu_mem_set.overlaps_vmem(r) {
            let r2 = choose|r2: MemoryRegion| #[trigger]
                gz.cpu_mem_set.regions.contains(r2) && r2.spec_overlaps_vmem(r);
            assert(r2.spec_valid());  // mem_set.wf ⇒ regions valid
            lemma_vmem_overlap_implies_shared_gpa(r2, r);
            let g = choose|g: GuestPage| region_owns_gpa(r2, g) && region_owns_gpa(r, g);
            assert(gz.cpu_mem_set.regions.contains(r2));
            lemma_region_in_zone_maps_gpa(gz, r2, g);
            let k = VmPageKey { vm, gpa: g };
            assert(zone_s2_entries(zid, gz).contains_key(k));  // => k in self@.s2_map
            assert(region.entries().contains_key(k));  // region_owns_gpa(r, g)
            assert(!self@.s2_map.contains_key(k));  // enabled freshness - contradiction
            assert(false);
        }
        // (4) Fire the `insert_region` macro transition; `post.invariant()` from the macro.

        let post = SoftwareSpec {
            budget: BudgetSpec::take_step::cpu_insert_region(self.budget, zid, r),
        };
        assert(post.budget.zone_ids == self.budget.zone_ids);
        assert(post.budget.zones == self.budget.zones.insert(
            zid,
            self.budget.zones[zid].cpu_insert_region(r),
        ));

        // (5) Projection deltas ⇒ the SoftwareView step.
        lemma_insert_region_owned_pages(self.budget.zones[zid], r);
        lemma_insert_region_all_owned(self.budget.zones, zid, r);
        lemma_insert_region_state_s2_map(self.budget, post.budget, zid, r);
        assert(post@.all_vms =~= self@.all_vms);
        assert(post@.vm_owned =~= self@.vm_owned.insert(
            vm,
            self@.vm_owned[vm].union(region.pages()),
        ));
        assert(post@.s2_map =~= self@.s2_map.union_prefer_right(region.entries()));
        assert(post@.hypervisor_owned =~= self@.hypervisor_owned.difference(region.pages()));
        // CPU insert leaves every zone's iommu_mem_set untouched ⇒ IOMMU view unchanged.
        lemma_state_iommu_proj_unchanged(self, post);
        post
    }

    proof fn remove_region(self, region: Region) -> (post: Self) {
        let vm = region.vm;
        let zid = vm.0;

        // (1) Recover the budget region via the trusted environment bridge.
        axiom_assignable_from_budget(self, region);
        let r = choose|r: MemoryRegion| #[trigger]
            zone_regions(zid).contains(r) && region_to_abstract(zid, r) == region;
        configured_regions_valid();
        zone_regions_internal_disjoint();
        assert(r.spec_valid());

        // (2) Projection equalities.
        lemma_region_to_abstract_pages(zid, r);
        lemma_region_to_abstract_entries(zid, r);

        // (3) `r` is present in the zone: one of its (owned) pages is backed by a zone
        // region, which must be `r` itself since distinct `all_regions` are pmem-disjoint.
        let gz = self.budget.zones[zid];
        let p0 = region.phys_page(0);
        assert(region.wf());
        assert(region.pages().contains(p0));
        assert(self@.vm_owned[vm].contains(p0));  // enabled ⇒ region.pages() ⊆ vm_owned
        assert(self@.vm_owned[vm] == zone_owned_pages(gz));  // view
        lemma_zone_owned_pages_region_witness(gz, p0);
        let r2 = choose|rr: MemoryRegion| #[trigger]
            gz.cpu_mem_set.regions.contains(rr) && region_owns_page(rr, p0);
        assert(gz.cpu_mem_set.regions.contains(r2));
        assert(zone_regions(zid).contains(r2));  // inv: zone regions ⊆ budget
        assert(r2.spec_valid());
        if r2 != r {
            let i2 = choose|i: nat| 0 <= i < r2.pages && region_phys_page(r2, i) == p0;
            let ir = choose|i: nat| 0 <= i < r.pages && region_phys_page(r, i) == p0;
            lemma_same_phys_page_implies_pmem_overlap(r2, i2, r, ir);
            assert(!r2.spec_overlaps_pmem(r));  // zone_regions_internal_disjoint
            assert(false);
        }
        assert(gz.cpu_mem_set.regions.contains(r));

        // pmem-exclusivity holds for any budget region: distinct `all_regions` are disjoint.
        assert(region_pmem_exclusive(gz, r)) by {
            assert forall|rr: MemoryRegion| #[trigger]
                gz.cpu_mem_set.regions.contains(rr) && rr != r implies !rr.spec_overlaps_pmem(
                r,
            ) by {
                assert(gz.cpu_mem_set.regions.contains(rr));  // fires the budget inv
                assert(zone_regions(zid).contains(rr));  // inv
                zone_regions_internal_disjoint();
            }
        }

        // (4) Fire the `remove_region` macro transition; `post.invariant()` from the macro.
        let post = SoftwareSpec {
            budget: BudgetSpec::take_step::cpu_remove_region(self.budget, zid, r),
        };
        assert(post.budget.zone_ids == self.budget.zone_ids);
        assert(post.budget.zones == self.budget.zones.insert(
            zid,
            self.budget.zones[zid].cpu_remove_region(r),
        ));

        // (5) Projection deltas ⇒ the SoftwareView step.
        lemma_region_pages_in_all_budget(zid, r);  // r's pages are budget pages (pool algebra)
        lemma_remove_region_owned_pages(self.budget.zones[zid], r);
        lemma_remove_region_all_owned(self.budget, zid, r);
        lemma_remove_region_state_s2_map(self.budget, post.budget, zid, r);
        assert(post@.all_vms =~= self@.all_vms);
        assert(post@.vm_owned =~= self@.vm_owned.insert(
            vm,
            self@.vm_owned[vm].difference(region.pages()),
        ));
        assert(post@.s2_map =~= self@.s2_map.remove_keys(region.entries().dom()));
        assert(post@.hypervisor_owned =~= self@.hypervisor_owned.union(region.pages()));
        // CPU remove leaves every zone's iommu_mem_set untouched ⇒ IOMMU view unchanged.
        lemma_state_iommu_proj_unchanged(self, post);
        post
    }

    proof fn iommu_insert_region(self, region: Region) -> (post: Self) {
        let vm = region.vm;
        let zid = vm.0;

        // (1) Recover the budget region.
        axiom_assignable_from_budget(self, region);
        let r = choose|r: MemoryRegion| #[trigger]
            zone_regions(zid).contains(r) && region_to_abstract(zid, r) == region;
        configured_regions_valid();
        assert(r.spec_valid());

        // (2) Projection equalities.
        lemma_region_to_abstract_pages(zid, r);
        lemma_region_to_abstract_entries(zid, r);

        // The region is private: its pages are non-GIC (`r ∈ zone_regions`, disjoint from GIC).
        assert forall|p: PhysPage| region_pages(r).contains(p) implies !is_gic_page(p) by {
            if is_gic_page(p) {
                let i = choose|i: nat| 0 <= i < r.pages && region_phys_page(r, i) == p;
                let ig = choose|ig: nat|
                    0 <= ig < gic_region().pages && region_phys_page(gic_region(), ig) == p;
                gic_region_disjoint_from_zones();
                lemma_same_phys_page_implies_pmem_overlap(gic_region(), ig, r, i);
            }
        }

        // (3) Transition guards, derived from `iommu_insert_region_enabled` via freshness.
        let gz = self.budget.zones[zid];
        assert(gz.wf());
        assert(region.wf());  // count > 0
        // !contains_region(r): r's `gpa_base` would already be IOMMU-mapped.
        if gz.iommu_mem_set.regions.contains(r) {
            let g0 = region_guest_page(r, 0);
            assert(region_owns_gpa(r, g0));  // witness 0
            lemma_iommu_region_in_zone_maps_gpa(gz, r, g0);
            let k0 = VmPageKey { vm, gpa: g0 };
            assert(zone_iommu_s2_entries(zid, gz).contains_key(k0));  // => k0 in self@.iommu_s2_map
            lemma_region_gpa_mapped_iff(r, g0);
            assert(region.entries().contains_key(k0));
            assert(!self@.iommu_s2_map.contains_key(k0));  // freshness - contradiction
            assert(false);
        }
        // !overlaps_vmem(r): an overlapping IOMMU region shares a mapped gpa.

        if gz.iommu_mem_set.overlaps_vmem(r) {
            let r2 = choose|r2: MemoryRegion| #[trigger]
                gz.iommu_mem_set.regions.contains(r2) && r2.spec_overlaps_vmem(r);
            assert(r2.spec_valid());
            lemma_vmem_overlap_implies_shared_gpa(r2, r);
            let g = choose|g: GuestPage| region_owns_gpa(r2, g) && region_owns_gpa(r, g);
            assert(gz.iommu_mem_set.regions.contains(r2));
            lemma_iommu_region_in_zone_maps_gpa(gz, r2, g);
            let k = VmPageKey { vm, gpa: g };
            assert(zone_iommu_s2_entries(zid, gz).contains_key(k));
            lemma_region_gpa_mapped_iff(r, g);
            assert(region.entries().contains_key(k));
            assert(!self@.iommu_s2_map.contains_key(k));  // freshness - contradiction
            assert(false);
        }
        // (4) Fire the `iommu_insert_region` macro transition.

        let post = SoftwareSpec {
            budget: BudgetSpec::take_step::iommu_insert_region(self.budget, zid, r),
        };
        assert(post.budget.zone_ids == self.budget.zone_ids);
        assert(post.budget.zones == self.budget.zones.insert(
            zid,
            self.budget.zones[zid].iommu_insert_region(r),
        ));

        // (5) Projection deltas ⇒ the SoftwareView step.
        lemma_iommu_insert_region_private_pages(self.budget.zones[zid], r);
        lemma_iommu_insert_region_state_iommu_s2_map(self.budget, post.budget, zid, r);
        assert(self@.iommu_owned[vm] == zone_iommu_private_pages(self.budget.zones[zid]));  // view
        assert(post@.iommu_owned =~= self@.iommu_owned.insert(
            vm,
            self@.iommu_owned[vm].union(region.pages()),
        )) by {
            assert forall|w: VmId| #[trigger]
                post@.iommu_owned.contains_key(w) implies post@.iommu_owned[w]
                =~= self@.iommu_owned.insert(
                vm,
                self@.iommu_owned[vm].union(region.pages()),
            )[w] by {
                if w.0 != zid {
                }
            }
        }
        assert(post@.iommu_s2_map =~= self@.iommu_s2_map.union_prefer_right(region.entries()));
        // IOMMU insert leaves every zone's cpu_mem_set untouched ⇒ CPU view unchanged.
        lemma_state_cpu_proj_unchanged(self, post);
        post
    }

    proof fn iommu_remove_region(self, region: Region) -> (post: Self) {
        let vm = region.vm;
        let zid = vm.0;

        // (1) Recover the budget region.
        axiom_assignable_from_budget(self, region);
        let r = choose|r: MemoryRegion| #[trigger]
            zone_regions(zid).contains(r) && region_to_abstract(zid, r) == region;
        configured_regions_valid();
        zone_regions_internal_disjoint();
        assert(r.spec_valid());

        // (2) Projection equalities.
        lemma_region_to_abstract_pages(zid, r);
        lemma_region_to_abstract_entries(zid, r);

        // (3) `r` is present in the zone's IOMMU set: one of its DMA-owned pages is backed
        // by an IOMMU region, which must be `r` (distinct `all_regions` are pmem-disjoint).
        let gz = self.budget.zones[zid];
        let p0 = region.phys_page(0);
        assert(region.wf());
        assert(region.pages().contains(p0));
        assert(self@.iommu_owned[vm].contains(p0));  // enabled ⇒ region.pages() ⊆ iommu_owned[vm]
        assert(self@.iommu_owned[vm] == zone_iommu_private_pages(gz));  // view
        lemma_zone_iommu_private_pages_region_witness(gz, p0);
        let r2 = choose|rr: MemoryRegion| #[trigger]
            gz.iommu_mem_set.regions.contains(rr) && region_owns_page(rr, p0) && rr != gic_region();
        assert(gz.iommu_mem_set.regions.contains(r2));
        assert(zone_regions(zid).contains(r2) || r2 == gic_region());  // inv_iommu_in_zone_regions
        assert(zone_regions(zid).contains(r2));
        assert(r2.spec_valid());
        if r2 != r {
            let i2 = choose|i: nat| 0 <= i < r2.pages && region_phys_page(r2, i) == p0;
            let ir = choose|i: nat| 0 <= i < r.pages && region_phys_page(r, i) == p0;
            lemma_same_phys_page_implies_pmem_overlap(r2, i2, r, ir);
            assert(!r2.spec_overlaps_pmem(r));  // zone_regions_internal_disjoint
            assert(false);
        }
        assert(gz.iommu_mem_set.regions.contains(r));

        // IOMMU pmem-exclusivity: any *other* IOMMU region is disjoint from `r` — a private
        // one by same-zone budget disjointness, the GIC by `gic_region_disjoint_from_zones`.
        assert(region_iommu_pmem_exclusive(gz, r)) by {
            assert forall|rr: MemoryRegion| #[trigger]
                gz.iommu_mem_set.regions.contains(rr) && rr != r implies !rr.spec_overlaps_pmem(
                r,
            ) by {
                assert(gz.iommu_mem_set.regions.contains(rr));
                assert(zone_regions(zid).contains(rr) || rr == gic_region());  // inv
                if rr == gic_region() {
                    gic_region_disjoint_from_zones();
                    assert(zone_regions(zid).contains(r));
                    assert(!gic_region().spec_overlaps_pmem(r));
                } else {
                    assert(zone_regions(zid).contains(rr));
                    zone_regions_internal_disjoint();
                }
            }
        }

        // (4) Fire the `iommu_remove_region` macro transition.
        let post = SoftwareSpec {
            budget: BudgetSpec::take_step::iommu_remove_region(self.budget, zid, r),
        };
        assert(post.budget.zone_ids == self.budget.zone_ids);
        assert(post.budget.zones == self.budget.zones.insert(
            zid,
            self.budget.zones[zid].iommu_remove_region(r),
        ));

        // (5) Projection deltas ⇒ the SoftwareView step.
        lemma_iommu_remove_region_private_pages(self.budget.zones[zid], r);
        lemma_iommu_remove_region_state_iommu_s2_map(self.budget, post.budget, zid, r);
        assert(self@.iommu_owned[vm] == zone_iommu_private_pages(self.budget.zones[zid]));  // view
        assert(post@.iommu_owned =~= self@.iommu_owned.insert(
            vm,
            self@.iommu_owned[vm].difference(region.pages()),
        )) by {
            assert forall|w: VmId| #[trigger]
                post@.iommu_owned.contains_key(w) implies post@.iommu_owned[w]
                =~= self@.iommu_owned.insert(
                vm,
                self@.iommu_owned[vm].difference(region.pages()),
            )[w] by {
                if w.0 != zid {
                }
            }
        }
        assert(post@.iommu_s2_map =~= self@.iommu_s2_map.remove_keys(region.entries().dom()));
        // IOMMU remove leaves every zone's cpu_mem_set untouched ⇒ CPU view unchanged.
        lemma_state_cpu_proj_unchanged(self, post);
        post
    }
}

} // verus!
