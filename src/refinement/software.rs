//! Software refinement from `BudgetSpec` to the policy-neutral `SoftwareView`.
//!
//! The public [`SoftwareRefinement`] contract does not mention `BudgetSpec` or
//! `MemoryRegion`.  It exposes two direct policy predicates and eight
//! class-specific transitions: CPU/IOMMU × zone-private/global-shared ×
//! insert/remove.  The `SoftwareSpec` implementation is the only place where
//! those predicates are tied to the static physical-page budgets.
use vstd::prelude::*;

verus! {

use crate::address::addr::SpecVAddr;
use crate::address::frame::SpecFrame;
use crate::address::region::*;
use crate::constants::*;
use crate::hv_mem::spec::budget::*;
use crate::hv_mem::spec::GhostZone;
use crate::memory_set::SpecMemorySet;
use crate::model::convert::*;
use crate::model::software::{Region, SoftwareView};
use crate::model::types::{GuestPage, PhysPage, S2Entry, VmId, VmPageKey};

// ---------------------------------------------------------------------------
// General software-refinement contract
// ---------------------------------------------------------------------------

/// Policy-neutral contract for software memory-state refinement.
///
/// An implementation supplies two direct predicates describing the region
/// units recognized by its policy.  A recognized unit may be neither private
/// nor shared, but it cannot be both.  No BudgetSpec type appears in this API.
pub trait SoftwareRefinement: View<V = SoftwareView> + Sized {
    /// Implementation invariant preserved by every interface transition.
    spec fn invariants(&self) -> bool;

    /// Whether `region` is one complete operation unit under a zone-private policy.
    spec fn region_is_zone_private(&self, region: Region) -> bool;

    /// Whether `region` is one complete operation unit under a global-shared policy.
    spec fn region_is_global_shared(&self, region: Region) -> bool;

    /// Establishes that the two policy classes never classify the same region.
    proof fn region_classes_disjoint(&self, region: Region)
        ensures
            !(self.region_is_zone_private(region)
                && self.region_is_global_shared(region)),
    ;

    /// Derives the complete software-view invariant from the implementation invariant.
    broadcast proof fn inv_implies_wf(&self)
        requires
            #[trigger] self.invariants(),
        ensures
            self@.wf(),
    ;

    /// Exposes the IOMMU portion of software-view well-formedness directly.
    broadcast proof fn inv_implies_iommu_wf(&self)
        requires
            #[trigger] self.invariants(),
        ensures
            self@.iommu_wf(),
    ;

    /// Adds a fresh VM with empty CPU and IOMMU projections.
    proof fn add_vm(self, vm: VmId) -> (post: Self)
        requires
            self.invariants(),
            SoftwareView::add_vm_enabled(self@, vm),
        ensures
            post.invariants(),
            SoftwareView::add_vm_step(self@, post@, vm),
    ;

    /// Removes a VM after all of its CPU and IOMMU state has been cleared.
    proof fn remove_vm(self, vm: VmId) -> (post: Self)
        requires
            self.invariants(),
            SoftwareView::remove_vm_enabled(self@, vm),
        ensures
            post.invariants(),
            SoftwareView::remove_vm_step(self@, post@, vm),
    ;

    /// Installs one zone-private region in the VM's CPU translation domain.
    proof fn cpu_insert_zone_private_region(self, region: Region) -> (post: Self)
        requires
            self.invariants(),
            self.region_is_zone_private(region),
            SoftwareView::cpu_insert_zone_private_region_enabled(self@, region),
        ensures
            post.invariants(),
            SoftwareView::cpu_insert_zone_private_region_step(self@, post@, region),
    ;

    /// Removes one complete zone-private region from the VM's CPU domain.
    proof fn cpu_remove_zone_private_region(self, region: Region) -> (post: Self)
        requires
            self.invariants(),
            self.region_is_zone_private(region),
            SoftwareView::cpu_remove_zone_private_region_enabled(self@, region),
        ensures
            post.invariants(),
            SoftwareView::cpu_remove_zone_private_region_step(self@, post@, region),
    ;

    /// Installs a global-shared CPU region while permitting physical aliases.
    proof fn cpu_insert_global_shared_region(self, region: Region) -> (post: Self)
        requires
            self.invariants(),
            self.region_is_global_shared(region),
            SoftwareView::cpu_insert_global_shared_region_enabled(self@, region),
        ensures
            post.invariants(),
            SoftwareView::cpu_insert_global_shared_region_step(self@, post@, region),
    ;

    /// Removes a global-shared CPU region and retains pages with surviving aliases.
    proof fn cpu_remove_global_shared_region(self, region: Region) -> (post: Self)
        requires
            self.invariants(),
            self.region_is_global_shared(region),
            SoftwareView::cpu_remove_global_shared_region_enabled(self@, region),
        ensures
            post.invariants(),
            SoftwareView::cpu_remove_global_shared_region_step(self@, post@, region),
    ;

    /// Installs one zone-private region in the VM's IOMMU translation domain.
    proof fn iommu_insert_zone_private_region(self, region: Region) -> (post: Self)
        requires
            self.invariants(),
            self.region_is_zone_private(region),
            SoftwareView::iommu_insert_zone_private_region_enabled(self@, region),
        ensures
            post.invariants(),
            SoftwareView::iommu_insert_zone_private_region_step(self@, post@, region),
    ;

    /// Removes one complete zone-private region from the VM's IOMMU domain.
    proof fn iommu_remove_zone_private_region(self, region: Region) -> (post: Self)
        requires
            self.invariants(),
            self.region_is_zone_private(region),
            SoftwareView::iommu_remove_zone_private_region_enabled(self@, region),
        ensures
            post.invariants(),
            SoftwareView::iommu_remove_zone_private_region_step(self@, post@, region),
    ;

    /// Installs a global-shared IOMMU region while permitting physical aliases.
    proof fn iommu_insert_global_shared_region(self, region: Region) -> (post: Self)
        requires
            self.invariants(),
            self.region_is_global_shared(region),
            SoftwareView::iommu_insert_global_shared_region_enabled(self@, region),
        ensures
            post.invariants(),
            SoftwareView::iommu_insert_global_shared_region_step(self@, post@, region),
    ;

    /// Removes a global-shared IOMMU region and retains pages with surviving aliases.
    proof fn iommu_remove_global_shared_region(self, region: Region) -> (post: Self)
        requires
            self.invariants(),
            self.region_is_global_shared(region),
            SoftwareView::iommu_remove_global_shared_region_enabled(self@, region),
        ensures
            post.invariants(),
            SoftwareView::iommu_remove_global_shared_region_step(self@, post@, region),
    ;
}

// ---------------------------------------------------------------------------
// Concrete-region geometry and its abstract rendering
// ---------------------------------------------------------------------------

/// Guest page occupied by page index `i` of `region`.
pub open spec fn region_guest_page(region: MemoryRegion, i: nat) -> GuestPage {
    gpa_of_vaddr(region.spec_page_vaddr(i))
}

/// `region` contains physical page `page`.
pub open spec fn region_owns_page(region: MemoryRegion, page: PhysPage) -> bool {
    region_phys_pages(region).contains(page)
}

/// `region` contains guest page `gpa`.
pub open spec fn region_owns_gpa(region: MemoryRegion, gpa: GuestPage) -> bool {
    exists|i: nat| 0 <= i < region.pages && #[trigger] region_guest_page(region, i) == gpa
}

/// Physical pages of one concrete region.
pub open spec fn region_pages(region: MemoryRegion) -> Set<PhysPage> {
    region_phys_pages(region)
}

/// Abstract stage-2 entries induced by one concrete region.
pub open spec fn region_s2_entries(zid: nat, region: MemoryRegion) -> Map<VmPageKey, S2Entry> {
    Map::new(
        |key: VmPageKey| key.vm == VmId(zid) && region_owns_gpa(region, key.gpa),
        |key: VmPageKey| {
            let i = choose|i: nat|
                0 <= i < region.pages && region_guest_page(region, i) == key.gpa;
            S2Entry {
                page: region_phys_page(region, i),
                access: attr_to_perms(region.attr),
                generation: 0,
            }
        },
    )
}

/// Render a concrete region as the policy-neutral region used by SoftwareView.
pub open spec fn region_to_abstract(zid: nat, region: MemoryRegion) -> Region {
    Region {
        vm: VmId(zid),
        gpa_base: region.vstart@.0 / SPEC_PAGE_SIZE,
        phys_base: region.pstart@.0 / SPEC_PAGE_SIZE,
        count: region.pages as nat,
        access: attr_to_perms(region.attr),
    }
}

/// Relates concrete frame arithmetic to the physical-page index of a valid region.
pub proof fn lemma_region_phys_page_linear(region: MemoryRegion, i: nat)
    requires
        region.spec_valid(),
        0 <= i < region.pages,
    ensures
        region.pstart@.0
            == (region.pstart@.0 / SPEC_PAGE_SIZE) * SPEC_PAGE_SIZE,
        region_phys_page(region, i).0 == region.pstart@.0 / SPEC_PAGE_SIZE + i,
        frame_phys_page(region.spec_frame(i)) == region_phys_page(region, i),
{
}

/// Expresses a valid region's guest page at index `i` as linear page arithmetic.
pub proof fn lemma_region_guest_page_linear(region: MemoryRegion, i: nat)
    requires
        region.spec_valid(),
        0 <= i < region.pages,
    ensures
        region.vstart@.0
            == (region.vstart@.0 / SPEC_PAGE_SIZE) * SPEC_PAGE_SIZE,
        region_guest_page(region, i).0 == region.vstart@.0 / SPEC_PAGE_SIZE + i,
{
}

/// Converts a region guest page back to the concrete virtual address at the same index.
pub proof fn lemma_gpa_vaddr_roundtrip(region: MemoryRegion, i: nat)
    requires
        region.spec_valid(),
        0 <= i < region.pages,
    ensures
        vaddr_of_gpa(region_guest_page(region, i)) == region.spec_page_vaddr(i),
{
}

/// Characterizes membership in a concrete region's mappings by its guest-page range.
pub proof fn lemma_region_gpa_mapped_iff(region: MemoryRegion, gpa: GuestPage)
    requires
        region.spec_valid(),
    ensures
        region.spec_mappings().contains_key(vaddr_of_gpa(gpa))
            <==> region_owns_gpa(region, gpa),
{
    if region_owns_gpa(region, gpa) {
        let i = choose|i: nat|
            0 <= i < region.pages && region_guest_page(region, i) == gpa;
        lemma_gpa_vaddr_roundtrip(region, i);
        region.lemma_mappings_contains_pair(i);
    }
    if region.spec_mappings().contains_key(vaddr_of_gpa(gpa)) {
        region.lemma_mappings_sound(vaddr_of_gpa(gpa));
        let i = choose|i: nat|
            0 <= i < region.pages
                && vaddr_of_gpa(gpa) == region.spec_page_vaddr(i)
                && region.spec_mappings()[vaddr_of_gpa(gpa)] == region.spec_frame(i);
        lemma_gpa_vaddr_roundtrip(region, i);
        lemma_vaddr_of_gpa_injective(region_guest_page(region, i), gpa);
    }
}

/// Shows the abstract entry for a region agrees with its concrete memory-set mapping.
pub proof fn lemma_region_s2_value(zid: nat, region: MemoryRegion, key: VmPageKey)
    requires
        region.spec_valid(),
        key.vm == VmId(zid),
        region_owns_gpa(region, key.gpa),
    ensures
        region_s2_entries(zid, region).contains_key(key),
        region_s2_entries(zid, region)[key]
            == frame_to_s2(region.spec_mappings()[vaddr_of_gpa(key.gpa)]),
{
    let i = choose|i: nat|
        0 <= i < region.pages && region_guest_page(region, i) == key.gpa;
    lemma_gpa_vaddr_roundtrip(region, i);
    region.lemma_mappings_contains_pair(i);
}

/// Produces a guest page shared by two virtually overlapping valid regions.
pub proof fn lemma_vmem_overlap_implies_shared_gpa(
    first: MemoryRegion,
    second: MemoryRegion,
)
    requires
        first.spec_valid(),
        second.spec_valid(),
        first.spec_overlaps_vmem(second),
    ensures
        exists|gpa: GuestPage|
            region_owns_gpa(first, gpa) && region_owns_gpa(second, gpa),
{
    let page_size = SPEC_PAGE_SIZE;
    let first_base = first.vstart@.0;
    let second_base = second.vstart@.0;
    let first_page = first_base / page_size;
    let second_page = second_base / page_size;
    lemma_region_guest_page_linear(first, 0);
    lemma_region_guest_page_linear(second, 0);
    if first_base <= second_base {
        let i = (second_page - first_page) as nat;
        lemma_region_guest_page_linear(first, i);
        assert(region_owns_gpa(first, GuestPage(second_page)));
        assert(region_owns_gpa(second, GuestPage(second_page)));
    } else {
        let i = (first_page - second_page) as nat;
        lemma_region_guest_page_linear(second, i);
        assert(region_owns_gpa(first, GuestPage(first_page)));
        assert(region_owns_gpa(second, GuestPage(first_page)));
    }
}

/// Produces a physical page shared by two physically overlapping valid regions.
pub proof fn lemma_pmem_overlap_implies_shared_page(
    first: MemoryRegion,
    second: MemoryRegion,
)
    requires
        first.spec_valid(),
        second.spec_valid(),
        first.spec_overlaps_pmem(second),
    ensures
        exists|page: PhysPage|
            region_pages(first).contains(page) && region_pages(second).contains(page),
{
    let page_size = SPEC_PAGE_SIZE;
    let first_base = first.pstart@.0;
    let second_base = second.pstart@.0;
    let first_page = first_base / page_size;
    let second_page = second_base / page_size;
    lemma_region_phys_page_linear(first, 0);
    lemma_region_phys_page_linear(second, 0);
    if first_base <= second_base {
        let i = (second_page - first_page) as nat;
        lemma_region_phys_page_linear(first, i);
        assert(region_pages(first).contains(PhysPage(second_page)));
        assert(region_pages(second).contains(PhysPage(second_page)));
    } else {
        let i = (first_page - second_page) as nat;
        lemma_region_phys_page_linear(second, i);
        assert(region_pages(first).contains(PhysPage(first_page)));
        assert(region_pages(second).contains(PhysPage(first_page)));
    }
}

/// Converts a shared physical page into concrete physical-region overlap.
pub proof fn lemma_shared_page_implies_pmem_overlap(
    first: MemoryRegion,
    second: MemoryRegion,
    page: PhysPage,
)
    requires
        first.spec_valid(),
        second.spec_valid(),
        region_pages(first).contains(page),
        region_pages(second).contains(page),
    ensures
        first.spec_overlaps_pmem(second),
{
    let first_i = choose|i: nat|
        0 <= i < first.pages && region_phys_page(first, i) == page;
    let second_i = choose|i: nat|
        0 <= i < second.pages && region_phys_page(second, i) == page;
    lemma_region_phys_page_linear(first, first_i);
    lemma_region_phys_page_linear(second, second_i);
}

/// Proves that abstraction preserves a concrete region's physical footprint.
pub proof fn lemma_region_to_abstract_pages(zid: nat, region: MemoryRegion)
    requires
        region.spec_valid(),
    ensures
        region_to_abstract(zid, region).pages() == region_pages(region),
{
    let abstract_region = region_to_abstract(zid, region);
    assert forall|page: PhysPage| abstract_region.pages().contains(page)
        <==> region_pages(region).contains(page) by {
        if abstract_region.pages().contains(page) {
            let i = (page.0 - region.pstart@.0 / SPEC_PAGE_SIZE) as nat;
            lemma_region_phys_page_linear(region, i);
        }
        if region_pages(region).contains(page) {
            let i = choose|i: nat|
                0 <= i < region.pages && region_phys_page(region, i) == page;
            lemma_region_phys_page_linear(region, i);
        }
    }
    assert(abstract_region.pages() =~= region_pages(region));
}

/// Proves that abstraction preserves every stage-2 entry of a concrete region.
pub proof fn lemma_region_to_abstract_entries(zid: nat, region: MemoryRegion)
    requires
        region.spec_valid(),
    ensures
        region_to_abstract(zid, region).entries() == region_s2_entries(zid, region),
{
    let abstract_region = region_to_abstract(zid, region);
    let lhs = abstract_region.entries();
    let rhs = region_s2_entries(zid, region);
    assert forall|key: VmPageKey| lhs.contains_key(key) <==> rhs.contains_key(key) by {
        if lhs.contains_key(key) {
            let i = (key.gpa.0 - abstract_region.gpa_base) as nat;
            lemma_region_guest_page_linear(region, i);
        }
        if rhs.contains_key(key) {
            let i = choose|i: nat|
                0 <= i < region.pages && region_guest_page(region, i) == key.gpa;
            lemma_region_guest_page_linear(region, i);
        }
    }
    assert forall|key: VmPageKey| #[trigger] lhs.contains_key(key) implies lhs[key] == rhs[key] by {
        let i = (key.gpa.0 - abstract_region.gpa_base) as nat;
        let j = choose|j: nat|
            0 <= j < region.pages && region_guest_page(region, j) == key.gpa;
        lemma_region_guest_page_linear(region, i);
        lemma_region_guest_page_linear(region, j);
        lemma_region_phys_page_linear(region, i);
    }
    assert(lhs =~= rhs);
}

/// Every entry of `region` is installed with its exact value.
pub open spec fn abstract_region_installed(
    map: Map<VmPageKey, S2Entry>,
    region: Region,
) -> bool {
    forall|key: VmPageKey| #[trigger]
        region.entries().contains_key(key)
            ==> map.contains_key(key) && map[key] == region.entries()[key]
}

// ---------------------------------------------------------------------------
// BudgetSpec -> SoftwareView projection
// ---------------------------------------------------------------------------

/// Physical pages targeted by a concrete memory set.
pub open spec fn memory_set_mapped_pages(mem_set: SpecMemorySet) -> Set<PhysPage> {
    Set::new(
        |page: PhysPage|
            exists|vaddr: SpecVAddr| #[trigger]
                mem_set.mappings.contains_key(vaddr)
                    && frame_phys_page(mem_set.mappings[vaddr]) == page,
    )
}

/// Physical pages targeted by the zone's current CPU mappings.
pub open spec fn zone_cpu_mapped_pages(zone: GhostZone) -> Set<PhysPage> {
    memory_set_mapped_pages(zone.cpu_mem_set)
}

/// Zone-private pages represented by the zone's installed CPU regions.
pub open spec fn zone_cpu_private_pages(zid: nat, zone: GhostZone) -> Set<PhysPage> {
    Set::new(
        |page: PhysPage|
            exists|region: MemoryRegion| #[trigger]
                zone.cpu_mem_set.regions.contains(region)
                    && region_in_zone_private_budget(zid, region)
                    && region_pages(region).contains(page),
    )
}

/// Global-shared pages represented by the zone's installed CPU regions.
pub open spec fn zone_cpu_shared_pages(zone: GhostZone) -> Set<PhysPage> {
    Set::new(
        |page: PhysPage|
            exists|region: MemoryRegion| #[trigger]
                zone.cpu_mem_set.regions.contains(region)
                    && region_in_global_shared_budget(region)
                    && region_pages(region).contains(page),
    )
}

/// Physical pages targeted by the zone's current IOMMU mappings.
pub open spec fn zone_iommu_mapped_pages(zone: GhostZone) -> Set<PhysPage> {
    memory_set_mapped_pages(zone.iommu_mem_set)
}

/// Zone-private pages represented by the zone's installed IOMMU regions.
pub open spec fn zone_iommu_private_pages(zid: nat, zone: GhostZone) -> Set<PhysPage> {
    Set::new(
        |page: PhysPage|
            exists|region: MemoryRegion| #[trigger]
                zone.iommu_mem_set.regions.contains(region)
                    && region_in_zone_private_budget(zid, region)
                    && region_pages(region).contains(page),
    )
}

/// Global-shared pages represented by the zone's installed IOMMU regions.
pub open spec fn zone_iommu_shared_pages(zone: GhostZone) -> Set<PhysPage> {
    Set::new(
        |page: PhysPage|
            exists|region: MemoryRegion| #[trigger]
                zone.iommu_mem_set.regions.contains(region)
                    && region_in_global_shared_budget(region)
                    && region_pages(region).contains(page),
    )
}

/// Renders a concrete memory set as abstract stage-2 entries for one zone.
pub open spec fn memory_set_s2_entries(
    zid: nat,
    mem_set: SpecMemorySet,
) -> Map<VmPageKey, S2Entry> {
    Map::new(
        |key: VmPageKey|
            key.vm == VmId(zid)
                && mem_set.mappings.contains_key(vaddr_of_gpa(key.gpa)),
        |key: VmPageKey|
            frame_to_s2(mem_set.mappings[vaddr_of_gpa(key.gpa)]),
    )
}

/// Abstract CPU stage-2 entries installed for one zone.
pub open spec fn zone_s2_entries(zid: nat, zone: GhostZone) -> Map<VmPageKey, S2Entry> {
    memory_set_s2_entries(zid, zone.cpu_mem_set)
}

/// Abstract IOMMU stage-2 entries installed for one zone.
pub open spec fn zone_iommu_s2_entries(zid: nat, zone: GhostZone) -> Map<VmPageKey, S2Entry> {
    memory_set_s2_entries(zid, zone.iommu_mem_set)
}

/// Union of all static zone-private budgets.  Retained for the future
/// allocatable-memory projection; it is not a SoftwareView field.
pub open spec fn all_zone_private_pages() -> Set<PhysPage> {
    Set::new(|page: PhysPage|
        exists|zid: nat| #[trigger] zone_private_pages(zid).contains(page))
}

/// Zone-private pages currently targeted by a CPU mapping.
pub open spec fn all_cpu_private_pages(zones: Map<nat, GhostZone>) -> Set<PhysPage> {
    Set::new(
        |page: PhysPage|
            exists|zid: nat|
                #![trigger zones.contains_key(zid)]
                zones.contains_key(zid)
                    && zone_cpu_private_pages(zid, zones[zid]).contains(page),
    )
}

/// Per-VM zone-private pages represented by the current CPU regions.
pub open spec fn state_vm_owned(
    state: BudgetSpec::State,
) -> Map<VmId, Set<PhysPage>> {
    Map::new(
        |vm: VmId| state.zone_ids.contains(vm.0),
        |vm: VmId| zone_cpu_private_pages(vm.0, state.zones[vm.0]),
    )
}

/// Per-VM zone-private pages represented by the current IOMMU regions.
pub open spec fn state_iommu_owned(
    state: BudgetSpec::State,
) -> Map<VmId, Set<PhysPage>> {
    Map::new(
        |vm: VmId| state.zone_ids.contains(vm.0),
        |vm: VmId| zone_iommu_private_pages(vm.0, state.zones[vm.0]),
    )
}

/// Combines every live zone's CPU entries into the global software-view map.
pub open spec fn state_s2_map(state: BudgetSpec::State) -> Map<VmPageKey, S2Entry> {
    Map::new(
        |key: VmPageKey|
            state.zone_ids.contains(key.vm.0)
                && zone_s2_entries(key.vm.0, state.zones[key.vm.0]).contains_key(key),
        |key: VmPageKey| zone_s2_entries(key.vm.0, state.zones[key.vm.0])[key],
    )
}

/// Combines every live zone's IOMMU entries into the global software-view map.
pub open spec fn state_iommu_s2_map(state: BudgetSpec::State) -> Map<VmPageKey, S2Entry> {
    Map::new(
        |key: VmPageKey|
            state.zone_ids.contains(key.vm.0)
                && zone_iommu_s2_entries(key.vm.0, state.zones[key.vm.0]).contains_key(key),
        |key: VmPageKey| zone_iommu_s2_entries(key.vm.0, state.zones[key.vm.0])[key],
    )
}

/// Global-shared pages targeted by at least one current CPU mapping.
pub open spec fn state_vm_shared(state: BudgetSpec::State) -> Set<PhysPage> {
    Set::new(
        |page: PhysPage|
            exists|zid: nat|
                #![trigger state.zone_ids.contains(zid)]
                state.zone_ids.contains(zid)
                    && zone_cpu_shared_pages(state.zones[zid]).contains(page),
    )
}

/// Global-shared pages targeted by at least one current IOMMU mapping.
pub open spec fn state_iommu_shared(state: BudgetSpec::State) -> Set<PhysPage> {
    Set::new(
        |page: PhysPage|
            exists|zid: nat|
                #![trigger state.zone_ids.contains(zid)]
                state.zone_ids.contains(zid)
                    && zone_iommu_shared_pages(state.zones[zid]).contains(page),
    )
}

/// BudgetSpec state equipped with its policy-neutral [`SoftwareView`] projection.
pub ghost struct SoftwareSpec {
    /// Concrete state whose budgets and installed regions determine the view.
    pub budget: BudgetSpec::State,
}

impl View for SoftwareSpec {
    type V = SoftwareView;

    open spec fn view(&self) -> SoftwareView {
        SoftwareView {
            all_vms: Set::new(|vm: VmId| self.budget.zone_ids.contains(vm.0)),
            vm_owned: state_vm_owned(self.budget),
            vm_shared: state_vm_shared(self.budget),
            s2_map: state_s2_map(self.budget),
            iommu_owned: state_iommu_owned(self.budget),
            iommu_shared: state_iommu_shared(self.budget),
            iommu_s2_map: state_iommu_s2_map(self.budget),
        }
    }
}

/// A BudgetSpec policy unit in `region.vm`'s zone-private budget.
///
/// The two implications preserve operation granularity: if the abstract region
/// is currently installed in a translation domain, the same concrete witness
/// must be a member of that domain's region set.  This prevents an abstract
/// remove from selecting only a proper subrange of a stored concrete region.
pub open spec fn budget_region_is_zone_private(spec: SoftwareSpec, region: Region) -> bool {
    exists|concrete: MemoryRegion|
        concrete.spec_valid()
            && region_in_zone_private_budget(region.vm.0, concrete)
            && region_to_abstract(region.vm.0, concrete) == region
            && (abstract_region_installed(spec@.s2_map, region) ==> (
                spec.budget.zones.contains_key(region.vm.0)
                    && spec.budget.zones[region.vm.0].cpu_mem_set.regions.contains(concrete)
            ))
            && (abstract_region_installed(spec@.iommu_s2_map, region) ==> (
                spec.budget.zones.contains_key(region.vm.0)
                    && spec.budget.zones[region.vm.0].iommu_mem_set.regions.contains(concrete)
            ))
}

/// A BudgetSpec policy unit in the global-shared budget.
pub open spec fn budget_region_is_global_shared(spec: SoftwareSpec, region: Region) -> bool {
    exists|concrete: MemoryRegion|
        concrete.spec_valid()
            && region_in_global_shared_budget(concrete)
            && region_to_abstract(region.vm.0, concrete) == region
            && (abstract_region_installed(spec@.s2_map, region) ==> (
                spec.budget.zones.contains_key(region.vm.0)
                    && spec.budget.zones[region.vm.0].cpu_mem_set.regions.contains(concrete)
            ))
            && (abstract_region_installed(spec@.iommu_s2_map, region) ==> (
                spec.budget.zones.contains_key(region.vm.0)
                    && spec.budget.zones[region.vm.0].iommu_mem_set.regions.contains(concrete)
            ))
}

/// Selects the concrete zone-private operation unit represented by `region`.
proof fn choose_zone_private_region(
    spec: SoftwareSpec,
    region: Region,
) -> (concrete: MemoryRegion)
    requires
        budget_region_is_zone_private(spec, region),
    ensures
        concrete.spec_valid(),
        region_in_zone_private_budget(region.vm.0, concrete),
        region_to_abstract(region.vm.0, concrete) == region,
        abstract_region_installed(spec@.s2_map, region) ==> (
            spec.budget.zones.contains_key(region.vm.0)
                && spec.budget.zones[region.vm.0].cpu_mem_set.regions.contains(concrete)
        ),
        abstract_region_installed(spec@.iommu_s2_map, region) ==> (
            spec.budget.zones.contains_key(region.vm.0)
                && spec.budget.zones[region.vm.0].iommu_mem_set.regions.contains(concrete)
        ),
{
    choose|concrete: MemoryRegion|
        concrete.spec_valid()
            && region_in_zone_private_budget(region.vm.0, concrete)
            && region_to_abstract(region.vm.0, concrete) == region
            && (abstract_region_installed(spec@.s2_map, region) ==> (
                spec.budget.zones.contains_key(region.vm.0)
                    && spec.budget.zones[region.vm.0].cpu_mem_set.regions.contains(concrete)
            ))
            && (abstract_region_installed(spec@.iommu_s2_map, region) ==> (
                spec.budget.zones.contains_key(region.vm.0)
                    && spec.budget.zones[region.vm.0].iommu_mem_set.regions.contains(concrete)
            ))
}

/// Selects the concrete global-shared operation unit represented by `region`.
proof fn choose_global_shared_region(
    spec: SoftwareSpec,
    region: Region,
) -> (concrete: MemoryRegion)
    requires
        budget_region_is_global_shared(spec, region),
    ensures
        concrete.spec_valid(),
        region_in_global_shared_budget(concrete),
        region_to_abstract(region.vm.0, concrete) == region,
        abstract_region_installed(spec@.s2_map, region) ==> (
            spec.budget.zones.contains_key(region.vm.0)
                && spec.budget.zones[region.vm.0].cpu_mem_set.regions.contains(concrete)
        ),
        abstract_region_installed(spec@.iommu_s2_map, region) ==> (
            spec.budget.zones.contains_key(region.vm.0)
                && spec.budget.zones[region.vm.0].iommu_mem_set.regions.contains(concrete)
        ),
{
    choose|concrete: MemoryRegion|
        concrete.spec_valid()
            && region_in_global_shared_budget(concrete)
            && region_to_abstract(region.vm.0, concrete) == region
            && (abstract_region_installed(spec@.s2_map, region) ==> (
                spec.budget.zones.contains_key(region.vm.0)
                    && spec.budget.zones[region.vm.0].cpu_mem_set.regions.contains(concrete)
            ))
            && (abstract_region_installed(spec@.iommu_s2_map, region) ==> (
                spec.budget.zones.contains_key(region.vm.0)
                    && spec.budget.zones[region.vm.0].iommu_mem_set.regions.contains(concrete)
            ))
}

// ---------------------------------------------------------------------------
// Projection facts
// ---------------------------------------------------------------------------

/// Finds an installed region whose footprint contains a mapped physical page.
proof fn lemma_memory_set_mapped_page_has_region(
    mem_set: SpecMemorySet,
    page: PhysPage,
)
    requires
        mem_set.wf(),
        memory_set_mapped_pages(mem_set).contains(page),
    ensures
        exists|region: MemoryRegion| #[trigger]
            mem_set.regions.contains(region) && region_pages(region).contains(page),
{
    let vaddr = choose|vaddr: SpecVAddr| #[trigger]
        mem_set.mappings.contains_key(vaddr)
            && frame_phys_page(mem_set.mappings[vaddr]) == page;
    let frame = mem_set.mappings[vaddr];
    assert(mem_set.mappings.contains_pair(vaddr, frame));
    assert(exists|region: MemoryRegion, i: nat|
        #![trigger mem_set.regions.contains(region), region.spec_page_vaddr(i)]
        mem_set.regions.contains(region)
            && 0 <= i < region.pages
            && vaddr == region.spec_page_vaddr(i)
            && frame == region.spec_frame(i));
    let (region, i) = choose|region: MemoryRegion, i: nat|
        mem_set.regions.contains(region)
            && 0 <= i < region.pages
            && vaddr == region.spec_page_vaddr(i)
            && frame == region.spec_frame(i);
    assert(region.spec_valid());
    lemma_region_phys_page_linear(region, i);
    assert(region_phys_page(region, i) == page);
    assert(region_pages(region).contains(page));
}

/// Classifies every mapped page as zone-private or global-shared.
proof fn lemma_memory_set_mapped_page_classified(
    zid: nat,
    mem_set: SpecMemorySet,
    page: PhysPage,
)
    requires
        mem_set.wf(),
        all_regions_in_budget(zid, mem_set),
        memory_set_mapped_pages(mem_set).contains(page),
    ensures
        zone_private_pages(zid).contains(page) || global_shared_pages().contains(page),
{
    lemma_memory_set_mapped_page_has_region(mem_set, page);
    let region = choose|region: MemoryRegion| #[trigger]
        mem_set.regions.contains(region) && region_pages(region).contains(page);
    assert(region_in_budget(zid, region));
}

/// Shows that an installed concrete region contributes all of its abstract entries.
proof fn lemma_region_in_memory_set_maps_entries(
    zid: nat,
    mem_set: SpecMemorySet,
    region: MemoryRegion,
)
    requires
        mem_set.wf(),
        mem_set.regions.contains(region),
    ensures
        abstract_region_installed(
            Map::new(
                |key: VmPageKey| key.vm == VmId(zid)
                    && mem_set.mappings.contains_key(vaddr_of_gpa(key.gpa)),
                |key: VmPageKey| frame_to_s2(mem_set.mappings[vaddr_of_gpa(key.gpa)]),
            ),
            region_to_abstract(zid, region),
        ),
{
    lemma_region_to_abstract_entries(zid, region);
}

/// Proves that every invariant BudgetSpec state projects to a well-formed SoftwareView.
proof fn lemma_budget_projection_wf(spec: SoftwareSpec)
    requires
        spec.budget.invariant(),
    ensures
        spec@.wf(),
{
    let sw = spec@;
    assert(spec.budget.inv_zone_ids());
    assert(spec.budget.inv_zones_wf());
    assert(spec.budget.inv_cpu_regions_in_budget());
    assert(spec.budget.inv_iommu_regions_in_budget());
    zone_private_pages_pairwise_disjoint();
    zone_private_pages_disjoint_from_global_shared();

    assert(sw.vm_owned.dom() =~= sw.all_vms);
    assert forall|vm1: VmId, vm2: VmId| #[trigger]
        sw.all_vms.contains(vm1) && #[trigger] sw.all_vms.contains(vm2) && vm1 != vm2
            implies forall|page: PhysPage| #[trigger]
                sw.vm_owned[vm1].contains(page) ==> !sw.vm_owned[vm2].contains(page) by {
    }
    assert forall|vm: VmId| #[trigger]
        sw.all_vms.contains(vm) implies forall|page: PhysPage| #[trigger]
            sw.vm_owned[vm].contains(page) ==> !sw.vm_shared.contains(page) by {
    }
    assert(sw.ownership_wf());

    assert forall|key: VmPageKey| #[trigger]
        sw.s2_map.contains_key(key) implies {
            &&& sw.all_vms.contains(key.vm)
            &&& sw.owned_or_shared(key.vm, sw.s2_map[key].page)
        } by {
        let zid = key.vm.0;
        let page = sw.s2_map[key].page;
        assert(spec.budget.zone_ids.contains(zid));
        assert(spec.budget.zones.contains_key(zid));
        assert(spec.budget.zones[zid].wf());
        assert(memory_set_mapped_pages(spec.budget.zones[zid].cpu_mem_set).contains(page));
        let mem_set = spec.budget.zones[zid].cpu_mem_set;
        assert(mem_set.wf());
        lemma_memory_set_mapped_page_has_region(mem_set, page);
        let concrete = choose|concrete: MemoryRegion| #[trigger]
            mem_set.regions.contains(concrete) && region_pages(concrete).contains(page);
        assert(region_in_budget(zid, concrete));
        if region_in_zone_private_budget(zid, concrete) {
            assert(sw.vm_owned[key.vm].contains(page));
        } else {
            assert(region_in_global_shared_budget(concrete));
            assert(sw.vm_shared.contains(page));
        }
    }
    assert(sw.translation_wf());

    assert(sw.iommu_owned.dom() =~= sw.all_vms);
    assert forall|vm1: VmId, vm2: VmId| #[trigger]
        sw.all_vms.contains(vm1) && #[trigger] sw.all_vms.contains(vm2) && vm1 != vm2
            implies forall|page: PhysPage| #[trigger]
                sw.iommu_owned[vm1].contains(page)
                    ==> !sw.iommu_owned[vm2].contains(page) by {
    }
    assert forall|vm1: VmId, vm2: VmId| #[trigger]
        sw.all_vms.contains(vm1) && #[trigger] sw.all_vms.contains(vm2) && vm1 != vm2
            implies forall|page: PhysPage| #[trigger]
                sw.iommu_owned[vm1].contains(page) ==> !sw.vm_owned[vm2].contains(page) by {
    }
    assert forall|vm: VmId| #[trigger]
        sw.all_vms.contains(vm) implies forall|page: PhysPage| #[trigger]
            sw.iommu_owned[vm].contains(page)
                ==> !sw.iommu_shared.contains(page) && !sw.vm_shared.contains(page) by {
    }
    assert forall|vm: VmId| #[trigger]
        sw.all_vms.contains(vm) implies forall|page: PhysPage| #[trigger]
            sw.vm_owned[vm].contains(page) ==> !sw.iommu_shared.contains(page) by {
    }
    assert(sw.iommu_ownership_wf());

    assert forall|key: VmPageKey| #[trigger]
        sw.iommu_s2_map.contains_key(key) implies {
            &&& sw.all_vms.contains(key.vm)
            &&& sw.iommu_owned.contains_key(key.vm)
            &&& (sw.iommu_owned[key.vm].contains(sw.iommu_s2_map[key].page)
                || sw.iommu_shared.contains(sw.iommu_s2_map[key].page))
        } by {
        let zid = key.vm.0;
        let page = sw.iommu_s2_map[key].page;
        assert(spec.budget.zone_ids.contains(zid));
        assert(spec.budget.zones.contains_key(zid));
        assert(spec.budget.zones[zid].wf());
        assert(memory_set_mapped_pages(spec.budget.zones[zid].iommu_mem_set).contains(page));
        let mem_set = spec.budget.zones[zid].iommu_mem_set;
        assert(mem_set.wf());
        lemma_memory_set_mapped_page_has_region(mem_set, page);
        let concrete = choose|concrete: MemoryRegion| #[trigger]
            mem_set.regions.contains(concrete) && region_pages(concrete).contains(page);
        assert(region_in_budget(zid, concrete));
        if region_in_zone_private_budget(zid, concrete) {
            assert(sw.iommu_owned[key.vm].contains(page));
        } else {
            assert(region_in_global_shared_budget(concrete));
            assert(sw.iommu_shared.contains(page));
        }
    }
    assert(sw.iommu_translation_wf());
    assert(sw.iommu_wf());
    assert(sw.wf());
}

/// Discharges policy-class disjointness for the BudgetSpec-backed implementation.
proof fn lemma_region_classes_disjoint(spec: SoftwareSpec, region: Region)
    requires
        budget_region_is_zone_private(spec, region),
        budget_region_is_global_shared(spec, region),
    ensures
        false,
{
    let private_region = choose|concrete: MemoryRegion|
        concrete.spec_valid()
            && region_in_zone_private_budget(region.vm.0, concrete)
            && region_to_abstract(region.vm.0, concrete) == region
            && (abstract_region_installed(spec@.s2_map, region) ==> (
                spec.budget.zones.contains_key(region.vm.0)
                    && spec.budget.zones[region.vm.0].cpu_mem_set.regions.contains(concrete)
            ))
            && (abstract_region_installed(spec@.iommu_s2_map, region) ==> (
                spec.budget.zones.contains_key(region.vm.0)
                    && spec.budget.zones[region.vm.0].iommu_mem_set.regions.contains(concrete)
            ));
    let shared_region = choose|concrete: MemoryRegion|
        concrete.spec_valid()
            && region_in_global_shared_budget(concrete)
            && region_to_abstract(region.vm.0, concrete) == region
            && (abstract_region_installed(spec@.s2_map, region) ==> (
                spec.budget.zones.contains_key(region.vm.0)
                    && spec.budget.zones[region.vm.0].cpu_mem_set.regions.contains(concrete)
            ))
            && (abstract_region_installed(spec@.iommu_s2_map, region) ==> (
                spec.budget.zones.contains_key(region.vm.0)
                    && spec.budget.zones[region.vm.0].iommu_mem_set.regions.contains(concrete)
            ));
    lemma_region_to_abstract_pages(region.vm.0, private_region);
    lemma_region_to_abstract_pages(region.vm.0, shared_region);
    let page = region.phys_page(0);
    assert(region.wf());
    assert(region.pages().contains(page));
    zone_private_pages_disjoint_from_global_shared();
}

/// Relates concrete memory-set insertion to abstract stage-2 map insertion.
proof fn lemma_memory_set_s2_insert(
    zid: nat,
    mem_set: SpecMemorySet,
    region: MemoryRegion,
)
    requires
        mem_set.wf(),
        region.spec_valid(),
        !mem_set.overlaps_vmem(region),
    ensures
        memory_set_s2_entries(zid, mem_set.insert_region(region))
            =~= memory_set_s2_entries(zid, mem_set).union_prefer_right(
                region_s2_entries(zid, region),
            ),
{
    let old = memory_set_s2_entries(zid, mem_set);
    let added = region_s2_entries(zid, region);
    let new = memory_set_s2_entries(zid, mem_set.insert_region(region));
    assert forall|key: VmPageKey| #[trigger]
        new.contains_key(key) <==> old.union_prefer_right(added).contains_key(key) by {
        lemma_region_gpa_mapped_iff(region, key.gpa);
    }
    assert forall|key: VmPageKey|
        #![trigger new[key]]
        #![trigger old.union_prefer_right(added)[key]]
        new.contains_key(key) implies new[key] == old.union_prefer_right(added)[key] by {
        lemma_region_gpa_mapped_iff(region, key.gpa);
        if region.spec_mappings().contains_key(vaddr_of_gpa(key.gpa)) {
            lemma_region_s2_value(zid, region, key);
        }
    }
}

/// Relates concrete memory-set removal to abstract stage-2 map removal.
proof fn lemma_memory_set_s2_remove(
    zid: nat,
    mem_set: SpecMemorySet,
    region: MemoryRegion,
)
    requires
        mem_set.wf(),
        mem_set.regions.contains(region),
    ensures
        memory_set_s2_entries(zid, mem_set.remove_region_exact(region))
            =~= memory_set_s2_entries(zid, mem_set).remove_keys(
                region_s2_entries(zid, region).dom(),
            ),
{
    let old = memory_set_s2_entries(zid, mem_set);
    let removed = region_s2_entries(zid, region);
    let new = memory_set_s2_entries(zid, mem_set.remove_region_exact(region));
    assert(region.spec_valid());
    assert forall|key: VmPageKey| #[trigger]
        new.contains_key(key) <==> old.remove_keys(removed.dom()).contains_key(key) by {
        lemma_region_gpa_mapped_iff(region, key.gpa);
    }
    assert forall|key: VmPageKey|
        #![trigger new[key]]
        #![trigger old.remove_keys(removed.dom())[key]]
        new.contains_key(key) implies new[key] == old.remove_keys(removed.dom())[key] by {
    }
}

/// Lifts a CPU memory-set insertion into the global CPU map projection.
proof fn lemma_state_s2_insert(
    pre: BudgetSpec::State,
    post: BudgetSpec::State,
    zid: nat,
    region: MemoryRegion,
)
    requires
        pre.invariant(),
        pre.zones.contains_key(zid),
        region.spec_valid(),
        !pre.zones[zid].cpu_mem_set.overlaps_vmem(region),
        post.zone_ids == pre.zone_ids,
        post.zones == pre.zones.insert(zid, pre.zones[zid].cpu_insert_region(region)),
    ensures
        state_s2_map(post) =~= state_s2_map(pre).union_prefer_right(
            region_s2_entries(zid, region),
        ),
{
    assert(pre.inv_zones_wf());
    assert(pre.zones[zid].wf());
    lemma_memory_set_s2_insert(zid, pre.zones[zid].cpu_mem_set, region);
    let lhs = state_s2_map(post);
    let rhs = state_s2_map(pre).union_prefer_right(region_s2_entries(zid, region));
    assert forall|key: VmPageKey| #[trigger]
        lhs.contains_key(key) <==> rhs.contains_key(key) by {
        if key.vm.0 != zid {
        }
    }
    assert forall|key: VmPageKey|
        #![trigger lhs[key]]
        #![trigger rhs[key]]
        lhs.contains_key(key) implies lhs[key] == rhs[key] by {
        if key.vm.0 != zid {
        }
    }
}

/// Lifts a CPU memory-set removal into the global CPU map projection.
proof fn lemma_state_s2_remove(
    pre: BudgetSpec::State,
    post: BudgetSpec::State,
    zid: nat,
    region: MemoryRegion,
)
    requires
        pre.invariant(),
        pre.zones.contains_key(zid),
        pre.zones[zid].cpu_mem_set.regions.contains(region),
        post.zone_ids == pre.zone_ids,
        post.zones == pre.zones.insert(zid, pre.zones[zid].cpu_remove_region(region)),
    ensures
        state_s2_map(post) =~= state_s2_map(pre).remove_keys(
            region_s2_entries(zid, region).dom(),
        ),
{
    assert(pre.inv_zones_wf());
    assert(pre.zones[zid].wf());
    lemma_memory_set_s2_remove(zid, pre.zones[zid].cpu_mem_set, region);
    let lhs = state_s2_map(post);
    let rhs = state_s2_map(pre).remove_keys(region_s2_entries(zid, region).dom());
    assert forall|key: VmPageKey| #[trigger]
        lhs.contains_key(key) <==> rhs.contains_key(key) by {
        if key.vm.0 != zid {
        }
    }
    assert forall|key: VmPageKey|
        #![trigger lhs[key]]
        #![trigger rhs[key]]
        lhs.contains_key(key) implies lhs[key] == rhs[key] by {
        if key.vm.0 != zid {
        }
    }
}

/// Lifts an IOMMU memory-set insertion into the global IOMMU map projection.
proof fn lemma_state_iommu_s2_insert(
    pre: BudgetSpec::State,
    post: BudgetSpec::State,
    zid: nat,
    region: MemoryRegion,
)
    requires
        pre.invariant(),
        pre.zones.contains_key(zid),
        region.spec_valid(),
        !pre.zones[zid].iommu_mem_set.overlaps_vmem(region),
        post.zone_ids == pre.zone_ids,
        post.zones == pre.zones.insert(zid, pre.zones[zid].iommu_insert_region(region)),
    ensures
        state_iommu_s2_map(post) =~= state_iommu_s2_map(pre).union_prefer_right(
            region_s2_entries(zid, region),
        ),
{
    assert(pre.inv_zones_wf());
    assert(pre.zones[zid].wf());
    lemma_memory_set_s2_insert(zid, pre.zones[zid].iommu_mem_set, region);
    let lhs = state_iommu_s2_map(post);
    let rhs = state_iommu_s2_map(pre).union_prefer_right(region_s2_entries(zid, region));
    assert forall|key: VmPageKey| #[trigger]
        lhs.contains_key(key) <==> rhs.contains_key(key) by {
        if key.vm.0 != zid {
        }
    }
    assert forall|key: VmPageKey|
        #![trigger lhs[key]]
        #![trigger rhs[key]]
        lhs.contains_key(key) implies lhs[key] == rhs[key] by {
        if key.vm.0 != zid {
        }
    }
}

/// Lifts an IOMMU memory-set removal into the global IOMMU map projection.
proof fn lemma_state_iommu_s2_remove(
    pre: BudgetSpec::State,
    post: BudgetSpec::State,
    zid: nat,
    region: MemoryRegion,
)
    requires
        pre.invariant(),
        pre.zones.contains_key(zid),
        pre.zones[zid].iommu_mem_set.regions.contains(region),
        post.zone_ids == pre.zone_ids,
        post.zones == pre.zones.insert(zid, pre.zones[zid].iommu_remove_region(region)),
    ensures
        state_iommu_s2_map(post) =~= state_iommu_s2_map(pre).remove_keys(
            region_s2_entries(zid, region).dom(),
        ),
{
    assert(pre.inv_zones_wf());
    assert(pre.zones[zid].wf());
    lemma_memory_set_s2_remove(zid, pre.zones[zid].iommu_mem_set, region);
    let lhs = state_iommu_s2_map(post);
    let rhs = state_iommu_s2_map(pre).remove_keys(region_s2_entries(zid, region).dom());
    assert forall|key: VmPageKey| #[trigger]
        lhs.contains_key(key) <==> rhs.contains_key(key) by {
        if key.vm.0 != zid {
        }
    }
    assert forall|key: VmPageKey|
        #![trigger lhs[key]]
        #![trigger rhs[key]]
        lhs.contains_key(key) implies lhs[key] == rhs[key] by {
        if key.vm.0 != zid {
        }
    }
}

/// Proves the SoftwareView effect of inserting one zone-private CPU region.
proof fn lemma_cpu_insert_zone_private_projection(
    pre: SoftwareSpec,
    post: SoftwareSpec,
    zid: nat,
    concrete: MemoryRegion,
)
    requires
        pre.budget.invariant(),
        post.budget.invariant(),
        pre.budget.zones.contains_key(zid),
        concrete.spec_valid(),
        region_in_zone_private_budget(zid, concrete),
        !pre.budget.zones[zid].cpu_mem_set.overlaps_vmem(concrete),
        post.budget.zone_ids == pre.budget.zone_ids,
        post.budget.zones == pre.budget.zones.insert(
            zid,
            pre.budget.zones[zid].cpu_insert_region(concrete),
        ),
    ensures
        SoftwareView::cpu_insert_zone_private_region_step(
            pre@,
            post@,
            region_to_abstract(zid, concrete),
        ),
{
    assert(pre.budget.inv_zones_wf());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_state_s2_insert(pre.budget, post.budget, zid, concrete);
    zone_private_pages_disjoint_from_global_shared();
    assert(post@.all_vms =~= pre@.all_vms);
    assert(post@.s2_map
        =~= pre@.s2_map.union_prefer_right(region_to_abstract(zid, concrete).entries()));
    assert(post@.iommu_owned =~= pre@.iommu_owned);
    assert(post@.iommu_shared =~= pre@.iommu_shared);
    assert(post@.iommu_s2_map =~= pre@.iommu_s2_map);
    lemma_zone_private_region_not_global_shared(zid, concrete);
        let target_owned = pre@.vm_owned.insert(
            VmId(zid),
            pre@.vm_owned[VmId(zid)].union(region_pages(concrete)),
        );
        assert(post@.vm_owned =~= target_owned) by {
            assert(post@.vm_owned.dom() =~= target_owned.dom());
            assert forall|vm: VmId| #[trigger]
                post@.vm_owned.contains_key(vm) implies post@.vm_owned[vm]
                    =~= target_owned[vm] by {
                if vm.0 == zid {
                    assert forall|page: PhysPage| post@.vm_owned[vm].contains(page)
                        <==> target_owned[vm].contains(page) by {
                        if post@.vm_owned[vm].contains(page) {
                            let stored = choose|stored: MemoryRegion| #[trigger]
                                post.budget.zones[zid].cpu_mem_set.regions.contains(stored)
                                    && region_in_zone_private_budget(zid, stored)
                                    && region_pages(stored).contains(page);
                            if stored != concrete {
                                assert(pre.budget.zones[zid].cpu_mem_set.regions.contains(stored));
                            }
                        }
                        if target_owned[vm].contains(page)
                            && region_pages(concrete).contains(page) {
                            assert(post.budget.zones[zid].cpu_mem_set.regions.contains(concrete));
                        }
                        if pre@.vm_owned[vm].contains(page) {
                            let stored = choose|stored: MemoryRegion| #[trigger]
                                pre.budget.zones[zid].cpu_mem_set.regions.contains(stored)
                                    && region_in_zone_private_budget(zid, stored)
                                    && region_pages(stored).contains(page);
                            assert(post.budget.zones[zid].cpu_mem_set.regions.contains(stored));
                            assert(post@.vm_owned[vm].contains(page));
                        }
                    }
                }
            }
        }
        assert(post@.vm_shared =~= pre@.vm_shared) by {
            assert forall|page: PhysPage| post@.vm_shared.contains(page)
                <==> pre@.vm_shared.contains(page) by {
                if post@.vm_shared.contains(page) {
                    let zone_id = choose|zone_id: nat| #[trigger]
                        post.budget.zone_ids.contains(zone_id)
                            && zone_cpu_shared_pages(post.budget.zones[zone_id]).contains(page);
                    if zone_id == zid {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            post.budget.zones[zid].cpu_mem_set.regions.contains(stored)
                                && region_in_global_shared_budget(stored)
                                && region_pages(stored).contains(page);
                        assert(stored != concrete);
                    }
                }
                if pre@.vm_shared.contains(page) {
                    let zone_id = choose|zone_id: nat| #[trigger]
                        pre.budget.zone_ids.contains(zone_id)
                            && zone_cpu_shared_pages(pre.budget.zones[zone_id]).contains(page);
                    let stored = choose|stored: MemoryRegion| #[trigger]
                        pre.budget.zones[zone_id].cpu_mem_set.regions.contains(stored)
                            && region_in_global_shared_budget(stored)
                            && region_pages(stored).contains(page);
                    assert(post.budget.zones[zone_id].cpu_mem_set.regions.contains(stored));
                    assert(post@.vm_shared.contains(page));
                }
            }
        }
}

/// Proves the SoftwareView effect of inserting one global-shared CPU region.
proof fn lemma_cpu_insert_global_shared_projection(
    pre: SoftwareSpec,
    post: SoftwareSpec,
    zid: nat,
    concrete: MemoryRegion,
)
    requires
        pre.budget.invariant(),
        post.budget.invariant(),
        pre.budget.zones.contains_key(zid),
        concrete.spec_valid(),
        region_in_global_shared_budget(concrete),
        !pre.budget.zones[zid].cpu_mem_set.overlaps_vmem(concrete),
        post.budget.zone_ids == pre.budget.zone_ids,
        post.budget.zones == pre.budget.zones.insert(
            zid,
            pre.budget.zones[zid].cpu_insert_region(concrete),
        ),
    ensures
        SoftwareView::cpu_insert_global_shared_region_step(
            pre@,
            post@,
            region_to_abstract(zid, concrete),
        ),
{
    assert(pre.budget.inv_zones_wf());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_state_s2_insert(pre.budget, post.budget, zid, concrete);
    zone_private_pages_disjoint_from_global_shared();
    assert(post@.all_vms =~= pre@.all_vms);
    assert(post@.s2_map
        =~= pre@.s2_map.union_prefer_right(region_to_abstract(zid, concrete).entries()));
    assert(post@.iommu_owned =~= pre@.iommu_owned);
    assert(post@.iommu_shared =~= pre@.iommu_shared);
    assert(post@.iommu_s2_map =~= pre@.iommu_s2_map);
    lemma_global_shared_region_not_zone_private(zid, concrete);
    assert(post@.vm_owned =~= pre@.vm_owned) by {
        assert forall|vm: VmId| #[trigger]
            post@.vm_owned.contains_key(vm) implies post@.vm_owned[vm]
                =~= pre@.vm_owned[vm] by {
            if vm.0 == zid {
                assert forall|page: PhysPage| post@.vm_owned[vm].contains(page)
                    <==> pre@.vm_owned[vm].contains(page) by {
                    if post@.vm_owned[vm].contains(page) {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            post.budget.zones[zid].cpu_mem_set.regions.contains(stored)
                                && region_in_zone_private_budget(zid, stored)
                                && region_pages(stored).contains(page);
                        assert(stored != concrete);
                    }
                    if pre@.vm_owned[vm].contains(page) {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            pre.budget.zones[zid].cpu_mem_set.regions.contains(stored)
                                && region_in_zone_private_budget(zid, stored)
                                && region_pages(stored).contains(page);
                        assert(post.budget.zones[zid].cpu_mem_set.regions.contains(stored));
                        assert(post@.vm_owned[vm].contains(page));
                    }
                }
            }
        }
    }
    assert(post@.vm_shared =~= pre@.vm_shared.union(region_pages(concrete))) by {
        assert forall|page: PhysPage| post@.vm_shared.contains(page)
            <==> pre@.vm_shared.union(region_pages(concrete)).contains(page) by {
            if post@.vm_shared.contains(page) {
                let zone_id = choose|zone_id: nat| #[trigger]
                    post.budget.zone_ids.contains(zone_id)
                        && zone_cpu_shared_pages(post.budget.zones[zone_id]).contains(page);
                if zone_id == zid {
                    let stored = choose|stored: MemoryRegion| #[trigger]
                        post.budget.zones[zid].cpu_mem_set.regions.contains(stored)
                            && region_in_global_shared_budget(stored)
                            && region_pages(stored).contains(page);
                    if stored != concrete {
                        assert(pre.budget.zones[zid].cpu_mem_set.regions.contains(stored));
                    }
                }
            }
            if region_pages(concrete).contains(page) {
                assert(post.budget.zones[zid].cpu_mem_set.regions.contains(concrete));
            }
            if pre@.vm_shared.contains(page) {
                let zone_id = choose|zone_id: nat| #[trigger]
                    pre.budget.zone_ids.contains(zone_id)
                        && zone_cpu_shared_pages(pre.budget.zones[zone_id]).contains(page);
                let stored = choose|stored: MemoryRegion| #[trigger]
                    pre.budget.zones[zone_id].cpu_mem_set.regions.contains(stored)
                        && region_in_global_shared_budget(stored)
                        && region_pages(stored).contains(page);
                assert(post.budget.zones[zone_id].cpu_mem_set.regions.contains(stored));
                assert(post@.vm_shared.contains(page));
            }
        }
    }
}

/// Proves the SoftwareView effect of removing one zone-private CPU region.
proof fn lemma_cpu_remove_zone_private_projection(
    pre: SoftwareSpec,
    post: SoftwareSpec,
    zid: nat,
    concrete: MemoryRegion,
)
    requires
        pre.budget.invariant(),
        post.budget.invariant(),
        pre.budget.zones.contains_key(zid),
        pre.budget.zones[zid].cpu_mem_set.regions.contains(concrete),
        concrete.spec_valid(),
        region_in_zone_private_budget(zid, concrete),
        post.budget.zone_ids == pre.budget.zone_ids,
        post.budget.zones == pre.budget.zones.insert(
            zid,
            pre.budget.zones[zid].cpu_remove_region(concrete),
        ),
    ensures
        SoftwareView::cpu_remove_zone_private_region_step(
            pre@,
            post@,
            region_to_abstract(zid, concrete),
        ),
{
    assert(pre.budget.inv_zones_wf());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_state_s2_remove(pre.budget, post.budget, zid, concrete);
    assert(post@.all_vms =~= pre@.all_vms);
    assert(post@.s2_map
        =~= pre@.s2_map.remove_keys(region_to_abstract(zid, concrete).entries().dom()));
    assert(post@.iommu_owned =~= pre@.iommu_owned);
    assert(post@.iommu_shared =~= pre@.iommu_shared);
    assert(post@.iommu_s2_map =~= pre@.iommu_s2_map);
    assert(pre.budget.inv_cpu_private_regions_pmem_nonoverlap());
        lemma_zone_private_region_not_global_shared(zid, concrete);
        let target_owned = pre@.vm_owned.insert(
            VmId(zid),
            pre@.vm_owned[VmId(zid)].difference(region_pages(concrete)),
        );
        assert(post@.vm_owned =~= target_owned) by {
            assert(post@.vm_owned.dom() =~= target_owned.dom());
            assert forall|vm: VmId| #[trigger]
                post@.vm_owned.contains_key(vm) implies post@.vm_owned[vm]
                    =~= target_owned[vm] by {
                if vm.0 == zid {
                    assert forall|page: PhysPage| post@.vm_owned[vm].contains(page)
                        <==> target_owned[vm].contains(page) by {
                        if post@.vm_owned[vm].contains(page) {
                            let stored = choose|stored: MemoryRegion| #[trigger]
                                post.budget.zones[zid].cpu_mem_set.regions.contains(stored)
                                    && region_in_zone_private_budget(zid, stored)
                                    && region_pages(stored).contains(page);
                            assert(stored != concrete);
                            assert(pre.budget.zones[zid].cpu_mem_set.regions.contains(stored));
                            if region_pages(concrete).contains(page) {
                                lemma_shared_page_implies_pmem_overlap(stored, concrete, page);
                                assert(!stored.spec_overlaps_pmem(concrete));
                                assert(false);
                            }
                        }
                        if target_owned[vm].contains(page) {
                            let stored = choose|stored: MemoryRegion| #[trigger]
                                pre.budget.zones[zid].cpu_mem_set.regions.contains(stored)
                                    && region_in_zone_private_budget(zid, stored)
                                    && region_pages(stored).contains(page);
                            assert(stored != concrete);
                            assert(post.budget.zones[zid].cpu_mem_set.regions.contains(stored));
                        }
                    }
                }
            }
        }
        assert(post@.vm_shared =~= pre@.vm_shared) by {
            assert forall|page: PhysPage| post@.vm_shared.contains(page)
                <==> pre@.vm_shared.contains(page) by {
                if pre@.vm_shared.contains(page) {
                    let zone_id = choose|zone_id: nat| #[trigger]
                        pre.budget.zone_ids.contains(zone_id)
                            && zone_cpu_shared_pages(pre.budget.zones[zone_id]).contains(page);
                    if zone_id == zid {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            pre.budget.zones[zid].cpu_mem_set.regions.contains(stored)
                                && region_in_global_shared_budget(stored)
                                && region_pages(stored).contains(page);
                        assert(stored != concrete);
                    }
                }
            }
        }
}

/// Proves the SoftwareView effect of removing one global-shared CPU region.
proof fn lemma_cpu_remove_global_shared_projection(
    pre: SoftwareSpec,
    post: SoftwareSpec,
    zid: nat,
    concrete: MemoryRegion,
)
    requires
        pre.budget.invariant(),
        post.budget.invariant(),
        pre.budget.zones.contains_key(zid),
        pre.budget.zones[zid].cpu_mem_set.regions.contains(concrete),
        concrete.spec_valid(),
        region_in_global_shared_budget(concrete),
        post.budget.zone_ids == pre.budget.zone_ids,
        post.budget.zones == pre.budget.zones.insert(
            zid,
            pre.budget.zones[zid].cpu_remove_region(concrete),
        ),
    ensures
        SoftwareView::cpu_remove_global_shared_region_step(
            pre@,
            post@,
            region_to_abstract(zid, concrete),
        ),
{
    assert(pre.budget.inv_zones_wf());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_state_s2_remove(pre.budget, post.budget, zid, concrete);
    assert(post@.all_vms =~= pre@.all_vms);
    assert(post@.s2_map
        =~= pre@.s2_map.remove_keys(region_to_abstract(zid, concrete).entries().dom()));
    assert(post@.iommu_owned =~= pre@.iommu_owned);
    assert(post@.iommu_shared =~= pre@.iommu_shared);
    assert(post@.iommu_s2_map =~= pre@.iommu_s2_map);
    lemma_global_shared_region_not_zone_private(zid, concrete);
    assert(post@.vm_owned =~= pre@.vm_owned) by {
        assert forall|vm: VmId| #[trigger]
            post@.vm_owned.contains_key(vm) implies post@.vm_owned[vm]
                =~= pre@.vm_owned[vm] by {
            if vm.0 == zid {
                assert forall|page: PhysPage| post@.vm_owned[vm].contains(page)
                    <==> pre@.vm_owned[vm].contains(page) by {
                    if pre@.vm_owned[vm].contains(page) {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            pre.budget.zones[zid].cpu_mem_set.regions.contains(stored)
                                && region_in_zone_private_budget(zid, stored)
                                && region_pages(stored).contains(page);
                        assert(stored != concrete);
                    }
                }
            }
        }
    }
    let target_shared = Set::new(
        |page: PhysPage| {
            let post_map = pre@.s2_map.remove_keys(
                region_to_abstract(zid, concrete).entries().dom(),
            );
            &&& pre@.vm_shared.contains(page)
            &&& (!region_pages(concrete).contains(page)
                || exists|key: VmPageKey| #[trigger]
                    post_map.contains_key(key) && post_map[key].page == page)
        },
    );
    assert(post@.vm_shared =~= target_shared) by {
        assert(post.budget.inv_zone_ids());
        assert(post.budget.inv_zones_wf());
        assert(post.budget.inv_cpu_regions_in_budget());
        zone_private_pages_disjoint_from_global_shared();
        assert forall|page: PhysPage| post@.vm_shared.contains(page)
            <==> target_shared.contains(page) by {
            if post@.vm_shared.contains(page) {
                let zone_id = choose|zone_id: nat| #[trigger]
                    post.budget.zone_ids.contains(zone_id)
                        && zone_cpu_shared_pages(post.budget.zones[zone_id]).contains(page);
                let stored = choose|stored: MemoryRegion| #[trigger]
                    post.budget.zones[zone_id].cpu_mem_set.regions.contains(stored)
                        && region_in_global_shared_budget(stored)
                        && region_pages(stored).contains(page);
                assert(pre@.vm_shared.contains(page));
                if region_pages(concrete).contains(page) {
                    assert(post.budget.zones[zone_id].wf());
                    let i = choose|i: nat|
                        0 <= i < stored.pages && region_phys_page(stored, i) == page;
                    let key = VmPageKey {
                        vm: VmId(zone_id),
                        gpa: region_guest_page(stored, i),
                    };
                    lemma_gpa_vaddr_roundtrip(stored, i);
                    lemma_region_phys_page_linear(stored, i);
                    assert(post.budget.zones[zone_id].cpu_mem_set.mappings.contains_pair(
                        stored.spec_page_vaddr(i),
                        stored.spec_frame(i),
                    ));
                    assert(post@.s2_map.contains_key(key));
                    assert(post@.s2_map[key].page == page);
                }
            }
            if target_shared.contains(page) {
                if !region_pages(concrete).contains(page) {
                    let zone_id = choose|zone_id: nat| #[trigger]
                        pre.budget.zone_ids.contains(zone_id)
                            && zone_cpu_shared_pages(pre.budget.zones[zone_id]).contains(page);
                    let stored = choose|stored: MemoryRegion| #[trigger]
                        pre.budget.zones[zone_id].cpu_mem_set.regions.contains(stored)
                            && region_in_global_shared_budget(stored)
                            && region_pages(stored).contains(page);
                    if zone_id == zid {
                        assert(stored != concrete);
                    }
                    assert(post.budget.zones[zone_id].cpu_mem_set.regions.contains(stored));
                } else {
                    let key = choose|key: VmPageKey| #[trigger]
                        post@.s2_map.contains_key(key) && post@.s2_map[key].page == page;
                    let zone_id = key.vm.0;
                    assert(post.budget.zone_ids.contains(zone_id));
                    assert(post.budget.zones.contains_key(zone_id));
                    let mem_set = post.budget.zones[zone_id].cpu_mem_set;
                    assert(post.budget.zones[zone_id].wf());
                    assert(memory_set_mapped_pages(mem_set).contains(page));
                    lemma_memory_set_mapped_page_has_region(mem_set, page);
                    let stored = choose|stored: MemoryRegion| #[trigger]
                        mem_set.regions.contains(stored) && region_pages(stored).contains(page);
                    assert(region_in_budget(zone_id, stored));
                    if region_in_zone_private_budget(zone_id, stored) {
                        assert(zone_private_pages(zone_id).contains(page));
                        assert(global_shared_pages().contains(page));
                        assert(false);
                    }
                    assert(region_in_global_shared_budget(stored));
                    assert(post@.vm_shared.contains(page));
                }
            }
        }
    }
    let abstract_region = region_to_abstract(zid, concrete);
    let expected_shared = Set::new(
        |page: PhysPage| {
            let post_map = pre@.s2_map.remove_keys(abstract_region.entries().dom());
            &&& pre@.vm_shared.contains(page)
            &&& (!abstract_region.pages().contains(page)
                || exists|key: VmPageKey| #[trigger]
                    post_map.contains_key(key) && post_map[key].page == page)
        },
    );
    assert forall|page: PhysPage| target_shared.contains(page)
        <==> expected_shared.contains(page) by {
        lemma_region_to_abstract_pages(zid, concrete);
    }
    assert(target_shared =~= expected_shared);
    assert(post@.vm_shared == expected_shared);
    assert(post@.vm_owned == pre@.vm_owned);
    assert(post@.all_vms == pre@.all_vms);
    assert(post@.s2_map
        == pre@.s2_map.remove_keys(abstract_region.entries().dom()));
    assert(post@.iommu_owned == pre@.iommu_owned);
    assert(post@.iommu_shared == pre@.iommu_shared);
    assert(post@.iommu_s2_map == pre@.iommu_s2_map);
    assert(SoftwareView::cpu_remove_global_shared_region_step(
        pre@,
        post@,
        abstract_region,
    ));
}

/// Proves the SoftwareView effect of inserting one zone-private IOMMU region.
proof fn lemma_iommu_insert_zone_private_projection(
    pre: SoftwareSpec,
    post: SoftwareSpec,
    zid: nat,
    concrete: MemoryRegion,
)
    requires
        pre.budget.invariant(),
        post.budget.invariant(),
        pre.budget.zones.contains_key(zid),
        concrete.spec_valid(),
        region_in_zone_private_budget(zid, concrete),
        !pre.budget.zones[zid].iommu_mem_set.overlaps_vmem(concrete),
        post.budget.zone_ids == pre.budget.zone_ids,
        post.budget.zones == pre.budget.zones.insert(
            zid,
            pre.budget.zones[zid].iommu_insert_region(concrete),
        ),
    ensures
        SoftwareView::iommu_insert_zone_private_region_step(
            pre@,
            post@,
            region_to_abstract(zid, concrete),
        ),
{
    assert(pre.budget.inv_zones_wf());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_state_iommu_s2_insert(pre.budget, post.budget, zid, concrete);
    zone_private_pages_disjoint_from_global_shared();
    assert(post@.all_vms =~= pre@.all_vms);
    assert(post@.vm_owned =~= pre@.vm_owned);
    assert(post@.vm_shared =~= pre@.vm_shared);
    assert(post@.s2_map =~= pre@.s2_map);
    assert(post@.iommu_s2_map
        =~= pre@.iommu_s2_map.union_prefer_right(region_to_abstract(zid, concrete).entries()));
    lemma_zone_private_region_not_global_shared(zid, concrete);
        let target_owned = pre@.iommu_owned.insert(
            VmId(zid),
            pre@.iommu_owned[VmId(zid)].union(region_pages(concrete)),
        );
        assert(post@.iommu_owned =~= target_owned) by {
            assert(post@.iommu_owned.dom() =~= target_owned.dom());
            assert forall|vm: VmId| #[trigger]
                post@.iommu_owned.contains_key(vm) implies post@.iommu_owned[vm]
                    =~= target_owned[vm] by {
                if vm.0 == zid {
                    assert forall|page: PhysPage| post@.iommu_owned[vm].contains(page)
                        <==> target_owned[vm].contains(page) by {
                        if post@.iommu_owned[vm].contains(page) {
                            let stored = choose|stored: MemoryRegion| #[trigger]
                                post.budget.zones[zid].iommu_mem_set.regions.contains(stored)
                                    && region_in_zone_private_budget(zid, stored)
                                    && region_pages(stored).contains(page);
                            if stored != concrete {
                                assert(pre.budget.zones[zid].iommu_mem_set.regions.contains(stored));
                            }
                        }
                        if target_owned[vm].contains(page)
                            && region_pages(concrete).contains(page) {
                            assert(post.budget.zones[zid].iommu_mem_set.regions.contains(concrete));
                        }
                        if pre@.iommu_owned[vm].contains(page) {
                            let stored = choose|stored: MemoryRegion| #[trigger]
                                pre.budget.zones[zid].iommu_mem_set.regions.contains(stored)
                                    && region_in_zone_private_budget(zid, stored)
                                    && region_pages(stored).contains(page);
                            assert(post.budget.zones[zid].iommu_mem_set.regions.contains(stored));
                            assert(post@.iommu_owned[vm].contains(page));
                        }
                    }
                }
            }
        }
        assert(post@.iommu_shared =~= pre@.iommu_shared) by {
            assert forall|page: PhysPage| post@.iommu_shared.contains(page)
                <==> pre@.iommu_shared.contains(page) by {
                if post@.iommu_shared.contains(page) {
                    let zone_id = choose|zone_id: nat| #[trigger]
                        post.budget.zone_ids.contains(zone_id)
                            && zone_iommu_shared_pages(post.budget.zones[zone_id]).contains(page);
                    if zone_id == zid {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            post.budget.zones[zid].iommu_mem_set.regions.contains(stored)
                                && region_in_global_shared_budget(stored)
                                && region_pages(stored).contains(page);
                        assert(stored != concrete);
                    }
                }
                if pre@.iommu_shared.contains(page) {
                    let zone_id = choose|zone_id: nat| #[trigger]
                        pre.budget.zone_ids.contains(zone_id)
                            && zone_iommu_shared_pages(pre.budget.zones[zone_id]).contains(page);
                    let stored = choose|stored: MemoryRegion| #[trigger]
                        pre.budget.zones[zone_id].iommu_mem_set.regions.contains(stored)
                            && region_in_global_shared_budget(stored)
                            && region_pages(stored).contains(page);
                    assert(post.budget.zones[zone_id].iommu_mem_set.regions.contains(stored));
                    assert(post@.iommu_shared.contains(page));
                }
            }
        }
}

/// Proves the SoftwareView effect of inserting one global-shared IOMMU region.
proof fn lemma_iommu_insert_global_shared_projection(
    pre: SoftwareSpec,
    post: SoftwareSpec,
    zid: nat,
    concrete: MemoryRegion,
)
    requires
        pre.budget.invariant(),
        post.budget.invariant(),
        pre.budget.zones.contains_key(zid),
        concrete.spec_valid(),
        region_in_global_shared_budget(concrete),
        !pre.budget.zones[zid].iommu_mem_set.overlaps_vmem(concrete),
        post.budget.zone_ids == pre.budget.zone_ids,
        post.budget.zones == pre.budget.zones.insert(
            zid,
            pre.budget.zones[zid].iommu_insert_region(concrete),
        ),
    ensures
        SoftwareView::iommu_insert_global_shared_region_step(
            pre@,
            post@,
            region_to_abstract(zid, concrete),
        ),
{
    assert(pre.budget.inv_zones_wf());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_state_iommu_s2_insert(pre.budget, post.budget, zid, concrete);
    zone_private_pages_disjoint_from_global_shared();
    assert(post@.all_vms =~= pre@.all_vms);
    assert(post@.vm_owned =~= pre@.vm_owned);
    assert(post@.vm_shared =~= pre@.vm_shared);
    assert(post@.s2_map =~= pre@.s2_map);
    assert(post@.iommu_s2_map
        =~= pre@.iommu_s2_map.union_prefer_right(region_to_abstract(zid, concrete).entries()));
    lemma_global_shared_region_not_zone_private(zid, concrete);
    assert(post@.iommu_owned =~= pre@.iommu_owned) by {
        assert forall|vm: VmId| #[trigger]
            post@.iommu_owned.contains_key(vm) implies post@.iommu_owned[vm]
                =~= pre@.iommu_owned[vm] by {
            if vm.0 == zid {
                assert forall|page: PhysPage| post@.iommu_owned[vm].contains(page)
                    <==> pre@.iommu_owned[vm].contains(page) by {
                    if post@.iommu_owned[vm].contains(page) {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            post.budget.zones[zid].iommu_mem_set.regions.contains(stored)
                                && region_in_zone_private_budget(zid, stored)
                                && region_pages(stored).contains(page);
                        assert(stored != concrete);
                    }
                    if pre@.iommu_owned[vm].contains(page) {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            pre.budget.zones[zid].iommu_mem_set.regions.contains(stored)
                                && region_in_zone_private_budget(zid, stored)
                                && region_pages(stored).contains(page);
                        assert(post.budget.zones[zid].iommu_mem_set.regions.contains(stored));
                        assert(post@.iommu_owned[vm].contains(page));
                    }
                }
            }
        }
    }
    assert(post@.iommu_shared =~= pre@.iommu_shared.union(region_pages(concrete))) by {
        assert forall|page: PhysPage| post@.iommu_shared.contains(page)
            <==> pre@.iommu_shared.union(region_pages(concrete)).contains(page) by {
            if post@.iommu_shared.contains(page) {
                let zone_id = choose|zone_id: nat| #[trigger]
                    post.budget.zone_ids.contains(zone_id)
                        && zone_iommu_shared_pages(post.budget.zones[zone_id]).contains(page);
                if zone_id == zid {
                    let stored = choose|stored: MemoryRegion| #[trigger]
                        post.budget.zones[zid].iommu_mem_set.regions.contains(stored)
                            && region_in_global_shared_budget(stored)
                            && region_pages(stored).contains(page);
                    if stored != concrete {
                        assert(pre.budget.zones[zid].iommu_mem_set.regions.contains(stored));
                    }
                }
            }
            if region_pages(concrete).contains(page) {
                assert(post.budget.zones[zid].iommu_mem_set.regions.contains(concrete));
            }
            if pre@.iommu_shared.contains(page) {
                let zone_id = choose|zone_id: nat| #[trigger]
                    pre.budget.zone_ids.contains(zone_id)
                        && zone_iommu_shared_pages(pre.budget.zones[zone_id]).contains(page);
                let stored = choose|stored: MemoryRegion| #[trigger]
                    pre.budget.zones[zone_id].iommu_mem_set.regions.contains(stored)
                        && region_in_global_shared_budget(stored)
                        && region_pages(stored).contains(page);
                assert(post.budget.zones[zone_id].iommu_mem_set.regions.contains(stored));
                assert(post@.iommu_shared.contains(page));
            }
        }
    }
}

/// Proves the SoftwareView effect of removing one zone-private IOMMU region.
proof fn lemma_iommu_remove_zone_private_projection(
    pre: SoftwareSpec,
    post: SoftwareSpec,
    zid: nat,
    concrete: MemoryRegion,
)
    requires
        pre.budget.invariant(),
        post.budget.invariant(),
        pre.budget.zones.contains_key(zid),
        pre.budget.zones[zid].iommu_mem_set.regions.contains(concrete),
        concrete.spec_valid(),
        region_in_zone_private_budget(zid, concrete),
        post.budget.zone_ids == pre.budget.zone_ids,
        post.budget.zones == pre.budget.zones.insert(
            zid,
            pre.budget.zones[zid].iommu_remove_region(concrete),
        ),
    ensures
        SoftwareView::iommu_remove_zone_private_region_step(
            pre@,
            post@,
            region_to_abstract(zid, concrete),
        ),
{
    assert(pre.budget.inv_zones_wf());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_state_iommu_s2_remove(pre.budget, post.budget, zid, concrete);
    assert(post@.all_vms =~= pre@.all_vms);
    assert(post@.vm_owned =~= pre@.vm_owned);
    assert(post@.vm_shared =~= pre@.vm_shared);
    assert(post@.s2_map =~= pre@.s2_map);
    assert(post@.iommu_s2_map
        =~= pre@.iommu_s2_map.remove_keys(region_to_abstract(zid, concrete).entries().dom()));
    assert(pre.budget.inv_iommu_private_regions_pmem_nonoverlap());
        lemma_zone_private_region_not_global_shared(zid, concrete);
        let target_owned = pre@.iommu_owned.insert(
            VmId(zid),
            pre@.iommu_owned[VmId(zid)].difference(region_pages(concrete)),
        );
        assert(post@.iommu_owned =~= target_owned) by {
            assert(post@.iommu_owned.dom() =~= target_owned.dom());
            assert forall|vm: VmId| #[trigger]
                post@.iommu_owned.contains_key(vm) implies post@.iommu_owned[vm]
                    =~= target_owned[vm] by {
                if vm.0 == zid {
                    assert forall|page: PhysPage| post@.iommu_owned[vm].contains(page)
                        <==> target_owned[vm].contains(page) by {
                        if post@.iommu_owned[vm].contains(page) {
                            let stored = choose|stored: MemoryRegion| #[trigger]
                                post.budget.zones[zid].iommu_mem_set.regions.contains(stored)
                                    && region_in_zone_private_budget(zid, stored)
                                    && region_pages(stored).contains(page);
                            assert(stored != concrete);
                            assert(pre.budget.zones[zid].iommu_mem_set.regions.contains(stored));
                            if region_pages(concrete).contains(page) {
                                lemma_shared_page_implies_pmem_overlap(stored, concrete, page);
                                assert(!stored.spec_overlaps_pmem(concrete));
                                assert(false);
                            }
                        }
                        if target_owned[vm].contains(page) {
                            let stored = choose|stored: MemoryRegion| #[trigger]
                                pre.budget.zones[zid].iommu_mem_set.regions.contains(stored)
                                    && region_in_zone_private_budget(zid, stored)
                                    && region_pages(stored).contains(page);
                            assert(stored != concrete);
                            assert(post.budget.zones[zid].iommu_mem_set.regions.contains(stored));
                        }
                    }
                }
            }
        }
        assert(post@.iommu_shared =~= pre@.iommu_shared) by {
            assert forall|page: PhysPage| post@.iommu_shared.contains(page)
                <==> pre@.iommu_shared.contains(page) by {
                if pre@.iommu_shared.contains(page) {
                    let zone_id = choose|zone_id: nat| #[trigger]
                        pre.budget.zone_ids.contains(zone_id)
                            && zone_iommu_shared_pages(pre.budget.zones[zone_id]).contains(page);
                    if zone_id == zid {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            pre.budget.zones[zid].iommu_mem_set.regions.contains(stored)
                                && region_in_global_shared_budget(stored)
                                && region_pages(stored).contains(page);
                        assert(stored != concrete);
                    }
                }
            }
        }
}

/// Proves the SoftwareView effect of removing one global-shared IOMMU region.
proof fn lemma_iommu_remove_global_shared_projection(
    pre: SoftwareSpec,
    post: SoftwareSpec,
    zid: nat,
    concrete: MemoryRegion,
)
    requires
        pre.budget.invariant(),
        post.budget.invariant(),
        pre.budget.zones.contains_key(zid),
        pre.budget.zones[zid].iommu_mem_set.regions.contains(concrete),
        concrete.spec_valid(),
        region_in_global_shared_budget(concrete),
        post.budget.zone_ids == pre.budget.zone_ids,
        post.budget.zones == pre.budget.zones.insert(
            zid,
            pre.budget.zones[zid].iommu_remove_region(concrete),
        ),
    ensures
        SoftwareView::iommu_remove_global_shared_region_step(
            pre@,
            post@,
            region_to_abstract(zid, concrete),
        ),
{
    assert(pre.budget.inv_zones_wf());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_state_iommu_s2_remove(pre.budget, post.budget, zid, concrete);
    assert(post@.all_vms =~= pre@.all_vms);
    assert(post@.vm_owned =~= pre@.vm_owned);
    assert(post@.vm_shared =~= pre@.vm_shared);
    assert(post@.s2_map =~= pre@.s2_map);
    assert(post@.iommu_s2_map
        =~= pre@.iommu_s2_map.remove_keys(region_to_abstract(zid, concrete).entries().dom()));
    lemma_global_shared_region_not_zone_private(zid, concrete);
    assert(post@.iommu_owned =~= pre@.iommu_owned) by {
        assert forall|vm: VmId| #[trigger]
            post@.iommu_owned.contains_key(vm) implies post@.iommu_owned[vm]
                =~= pre@.iommu_owned[vm] by {
            if vm.0 == zid {
                assert forall|page: PhysPage| post@.iommu_owned[vm].contains(page)
                    <==> pre@.iommu_owned[vm].contains(page) by {
                    if pre@.iommu_owned[vm].contains(page) {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            pre.budget.zones[zid].iommu_mem_set.regions.contains(stored)
                                && region_in_zone_private_budget(zid, stored)
                                && region_pages(stored).contains(page);
                        assert(stored != concrete);
                    }
                }
            }
        }
    }
    let target_shared = Set::new(
        |page: PhysPage| {
            let post_map = pre@.iommu_s2_map.remove_keys(
                region_to_abstract(zid, concrete).entries().dom(),
            );
            &&& pre@.iommu_shared.contains(page)
            &&& (!region_pages(concrete).contains(page)
                || exists|key: VmPageKey| #[trigger]
                    post_map.contains_key(key) && post_map[key].page == page)
        },
    );
    assert(post@.iommu_shared =~= target_shared) by {
        assert(post.budget.inv_zone_ids());
        assert(post.budget.inv_zones_wf());
        assert(post.budget.inv_iommu_regions_in_budget());
        zone_private_pages_disjoint_from_global_shared();
        assert forall|page: PhysPage| post@.iommu_shared.contains(page)
            <==> target_shared.contains(page) by {
            if post@.iommu_shared.contains(page) {
                let zone_id = choose|zone_id: nat| #[trigger]
                    post.budget.zone_ids.contains(zone_id)
                        && zone_iommu_shared_pages(post.budget.zones[zone_id]).contains(page);
                let stored = choose|stored: MemoryRegion| #[trigger]
                    post.budget.zones[zone_id].iommu_mem_set.regions.contains(stored)
                        && region_in_global_shared_budget(stored)
                        && region_pages(stored).contains(page);
                assert(pre@.iommu_shared.contains(page));
                if region_pages(concrete).contains(page) {
                    assert(post.budget.zones[zone_id].wf());
                    let i = choose|i: nat|
                        0 <= i < stored.pages && region_phys_page(stored, i) == page;
                    let key = VmPageKey {
                        vm: VmId(zone_id),
                        gpa: region_guest_page(stored, i),
                    };
                    lemma_gpa_vaddr_roundtrip(stored, i);
                    lemma_region_phys_page_linear(stored, i);
                    assert(post.budget.zones[zone_id].iommu_mem_set.mappings.contains_pair(
                        stored.spec_page_vaddr(i),
                        stored.spec_frame(i),
                    ));
                    assert(post@.iommu_s2_map.contains_key(key));
                    assert(post@.iommu_s2_map[key].page == page);
                }
            }
            if target_shared.contains(page) {
                if !region_pages(concrete).contains(page) {
                    let zone_id = choose|zone_id: nat| #[trigger]
                        pre.budget.zone_ids.contains(zone_id)
                            && zone_iommu_shared_pages(pre.budget.zones[zone_id]).contains(page);
                    let stored = choose|stored: MemoryRegion| #[trigger]
                        pre.budget.zones[zone_id].iommu_mem_set.regions.contains(stored)
                            && region_in_global_shared_budget(stored)
                            && region_pages(stored).contains(page);
                    if zone_id == zid {
                        assert(stored != concrete);
                    }
                    assert(post.budget.zones[zone_id].iommu_mem_set.regions.contains(stored));
                } else {
                    let key = choose|key: VmPageKey| #[trigger]
                        post@.iommu_s2_map.contains_key(key)
                            && post@.iommu_s2_map[key].page == page;
                    let zone_id = key.vm.0;
                    assert(post.budget.zone_ids.contains(zone_id));
                    assert(post.budget.zones.contains_key(zone_id));
                    let mem_set = post.budget.zones[zone_id].iommu_mem_set;
                    assert(post.budget.zones[zone_id].wf());
                    assert(memory_set_mapped_pages(mem_set).contains(page));
                    lemma_memory_set_mapped_page_has_region(mem_set, page);
                    let stored = choose|stored: MemoryRegion| #[trigger]
                        mem_set.regions.contains(stored) && region_pages(stored).contains(page);
                    assert(region_in_budget(zone_id, stored));
                    if region_in_zone_private_budget(zone_id, stored) {
                        assert(zone_private_pages(zone_id).contains(page));
                        assert(global_shared_pages().contains(page));
                        assert(false);
                    }
                    assert(region_in_global_shared_budget(stored));
                    assert(post@.iommu_shared.contains(page));
                }
            }
        }
    }
    let abstract_region = region_to_abstract(zid, concrete);
    let expected_shared = Set::new(
        |page: PhysPage| {
            let post_map = pre@.iommu_s2_map.remove_keys(abstract_region.entries().dom());
            &&& pre@.iommu_shared.contains(page)
            &&& (!abstract_region.pages().contains(page)
                || exists|key: VmPageKey| #[trigger]
                    post_map.contains_key(key) && post_map[key].page == page)
        },
    );
    assert forall|page: PhysPage| target_shared.contains(page)
        <==> expected_shared.contains(page) by {
        lemma_region_to_abstract_pages(zid, concrete);
    }
    assert(target_shared =~= expected_shared);
    assert(post@.iommu_shared == expected_shared);
    assert(post@.iommu_owned == pre@.iommu_owned);
    assert(post@.all_vms == pre@.all_vms);
    assert(post@.vm_owned == pre@.vm_owned);
    assert(post@.vm_shared == pre@.vm_shared);
    assert(post@.s2_map == pre@.s2_map);
    assert(post@.iommu_s2_map
        == pre@.iommu_s2_map.remove_keys(abstract_region.entries().dom()));
    assert(SoftwareView::iommu_remove_global_shared_region_step(
        pre@,
        post@,
        abstract_region,
    ));
}

// ---------------------------------------------------------------------------
// Concrete transition guards
// ---------------------------------------------------------------------------

/// Derives the appropriate abstract CPU insertion guard from BudgetSpec invariants.
proof fn lemma_cpu_insert_guards(
    spec: SoftwareSpec,
    region: Region,
    concrete: MemoryRegion,
)
    requires
        spec.budget.invariant(),
        concrete.spec_valid(),
        region_to_abstract(region.vm.0, concrete) == region,
        region_in_budget(region.vm.0, concrete),
        SoftwareView::cpu_insert_zone_private_region_enabled(spec@, region)
            || SoftwareView::cpu_insert_global_shared_region_enabled(spec@, region),
    ensures
        spec.budget.zones.contains_key(region.vm.0),
        !spec.budget.zones[region.vm.0].cpu_mem_set.regions.contains(concrete),
        !spec.budget.zones[region.vm.0].cpu_mem_set.overlaps_vmem(concrete),
        region_in_zone_private_budget(region.vm.0, concrete) ==>
            pmem_nonoverlap_with_zone_private_regions(
                region.vm.0,
                spec.budget.zones[region.vm.0].cpu_mem_set,
                concrete,
            ),
{
    let zid = region.vm.0;
    assert(spec.budget.inv_zone_ids());
    assert(spec.budget.inv_zones_wf());
    assert(spec@.all_vms.contains(region.vm));
    assert(spec.budget.zone_ids.contains(zid));
    assert(spec.budget.zones.contains_key(zid));
    let zone = spec.budget.zones[zid];
    assert(zone.wf());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    if zone.cpu_mem_set.regions.contains(concrete) {
        let key = VmPageKey { vm: region.vm, gpa: region.guest_page(0) };
        assert(region.entries().contains_key(key));
        assert(concrete.spec_mappings().contains_key(vaddr_of_gpa(key.gpa))) by {
            lemma_region_gpa_mapped_iff(concrete, key.gpa);
        }
        assert(zone.cpu_mem_set.mappings.contains_key(vaddr_of_gpa(key.gpa)));
        assert(zone_s2_entries(zid, zone).contains_key(key));
        assert(spec@.s2_map.contains_key(key));
        assert(false);
    }
    if zone.cpu_mem_set.overlaps_vmem(concrete) {
        let old = choose|old: MemoryRegion| #[trigger]
            zone.cpu_mem_set.regions.contains(old) && old.spec_overlaps_vmem(concrete);
        assert(old.spec_valid());
        lemma_vmem_overlap_implies_shared_gpa(old, concrete);
        let gpa = choose|gpa: GuestPage|
            region_owns_gpa(old, gpa) && region_owns_gpa(concrete, gpa);
        let key = VmPageKey { vm: region.vm, gpa };
        let i = choose|i: nat| 0 <= i < old.pages && region_guest_page(old, i) == gpa;
        lemma_gpa_vaddr_roundtrip(old, i);
        assert(zone.cpu_mem_set.mappings.contains_key(vaddr_of_gpa(gpa)));
        assert(zone_s2_entries(zid, zone).contains_key(key));
        assert(spec@.s2_map.contains_key(key));
        assert(region.entries().contains_key(key));
        assert(false);
    }
    if region_in_zone_private_budget(zid, concrete) {
        assert(pmem_nonoverlap_with_zone_private_regions(zid, zone.cpu_mem_set, concrete)) by {
            assert forall|old: MemoryRegion| #[trigger]
                zone.cpu_mem_set.regions.contains(old)
                    && region_in_zone_private_budget(zid, old)
                    implies !old.spec_overlaps_pmem(concrete) by {
                if old.spec_overlaps_pmem(concrete) {
                    assert(old.spec_valid());
                    lemma_pmem_overlap_implies_shared_page(old, concrete);
                    let page = choose|page: PhysPage|
                        region_pages(old).contains(page) && region_pages(concrete).contains(page);
                    assert(spec@.vm_owned[region.vm].contains(page));
                    assert(false);
                }
            }
        }
    }
}

/// Derives the appropriate abstract IOMMU insertion guard from BudgetSpec invariants.
proof fn lemma_iommu_insert_guards(
    spec: SoftwareSpec,
    region: Region,
    concrete: MemoryRegion,
)
    requires
        spec.budget.invariant(),
        concrete.spec_valid(),
        region_to_abstract(region.vm.0, concrete) == region,
        region_in_budget(region.vm.0, concrete),
        SoftwareView::iommu_insert_zone_private_region_enabled(spec@, region)
            || SoftwareView::iommu_insert_global_shared_region_enabled(spec@, region),
    ensures
        spec.budget.zones.contains_key(region.vm.0),
        !spec.budget.zones[region.vm.0].iommu_mem_set.regions.contains(concrete),
        !spec.budget.zones[region.vm.0].iommu_mem_set.overlaps_vmem(concrete),
        region_in_zone_private_budget(region.vm.0, concrete) ==>
            pmem_nonoverlap_with_zone_private_regions(
                region.vm.0,
                spec.budget.zones[region.vm.0].iommu_mem_set,
                concrete,
            ),
{
    let zid = region.vm.0;
    assert(spec.budget.inv_zone_ids());
    assert(spec.budget.inv_zones_wf());
    assert(spec@.all_vms.contains(region.vm));
    assert(spec.budget.zone_ids.contains(zid));
    assert(spec.budget.zones.contains_key(zid));
    let zone = spec.budget.zones[zid];
    assert(zone.wf());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    if zone.iommu_mem_set.regions.contains(concrete) {
        let key = VmPageKey { vm: region.vm, gpa: region.guest_page(0) };
        assert(region.entries().contains_key(key));
        assert(concrete.spec_mappings().contains_key(vaddr_of_gpa(key.gpa))) by {
            lemma_region_gpa_mapped_iff(concrete, key.gpa);
        }
        assert(zone.iommu_mem_set.mappings.contains_key(vaddr_of_gpa(key.gpa)));
        assert(zone_iommu_s2_entries(zid, zone).contains_key(key));
        assert(spec@.iommu_s2_map.contains_key(key));
        assert(false);
    }
    if zone.iommu_mem_set.overlaps_vmem(concrete) {
        let old = choose|old: MemoryRegion| #[trigger]
            zone.iommu_mem_set.regions.contains(old) && old.spec_overlaps_vmem(concrete);
        assert(old.spec_valid());
        lemma_vmem_overlap_implies_shared_gpa(old, concrete);
        let gpa = choose|gpa: GuestPage|
            region_owns_gpa(old, gpa) && region_owns_gpa(concrete, gpa);
        let key = VmPageKey { vm: region.vm, gpa };
        let i = choose|i: nat| 0 <= i < old.pages && region_guest_page(old, i) == gpa;
        lemma_gpa_vaddr_roundtrip(old, i);
        assert(zone.iommu_mem_set.mappings.contains_key(vaddr_of_gpa(gpa)));
        assert(zone_iommu_s2_entries(zid, zone).contains_key(key));
        assert(spec@.iommu_s2_map.contains_key(key));
        assert(region.entries().contains_key(key));
        assert(false);
    }
    if region_in_zone_private_budget(zid, concrete) {
        assert(pmem_nonoverlap_with_zone_private_regions(zid, zone.iommu_mem_set, concrete)) by {
            assert forall|old: MemoryRegion| #[trigger]
                zone.iommu_mem_set.regions.contains(old)
                    && region_in_zone_private_budget(zid, old)
                    implies !old.spec_overlaps_pmem(concrete) by {
                if old.spec_overlaps_pmem(concrete) {
                    assert(old.spec_valid());
                    lemma_pmem_overlap_implies_shared_page(old, concrete);
                    let page = choose|page: PhysPage|
                        region_pages(old).contains(page) && region_pages(concrete).contains(page);
                    assert(spec@.iommu_owned[region.vm].contains(page));
                    assert(false);
                }
            }
        }
    }
}

/// Shows that a well-formed CPU memory set with no entries has no stored regions.
proof fn lemma_no_cpu_entries_implies_empty(
    spec: SoftwareSpec,
    vm: VmId,
)
    requires
        spec.budget.invariant(),
        spec.budget.zones.contains_key(vm.0),
        forall|key: VmPageKey| #[trigger]
            spec@.s2_map.contains_key(key) ==> key.vm != vm,
    ensures
        spec.budget.zones[vm.0].cpu_mem_set.regions == Set::<MemoryRegion>::empty(),
        spec.budget.zones[vm.0].cpu_mem_set.mappings
            == Map::<SpecVAddr, SpecFrame>::empty(),
{
    assert(spec.budget.inv_zones_wf());
    assert(spec.budget.zones[vm.0].wf());
    let mem_set = spec.budget.zones[vm.0].cpu_mem_set;
    assert(mem_set.wf());
    assert(mem_set.regions =~= Set::<MemoryRegion>::empty()) by {
        assert forall|region: MemoryRegion| !mem_set.regions.contains(region) by {
            if mem_set.regions.contains(region) {
                assert(region.spec_valid());
                let gpa = region_guest_page(region, 0);
                let key = VmPageKey { vm, gpa };
                lemma_gpa_vaddr_roundtrip(region, 0);
                assert(mem_set.mappings.contains_key(vaddr_of_gpa(gpa)));
                assert(zone_s2_entries(vm.0, spec.budget.zones[vm.0]).contains_key(key));
                assert(spec@.s2_map.contains_key(key));
                assert(false);
            }
        }
    }
    assert(mem_set.mappings =~= Map::<SpecVAddr, SpecFrame>::empty()) by {
        assert forall|vaddr: SpecVAddr| !mem_set.mappings.contains_key(vaddr) by {
            if mem_set.mappings.contains_key(vaddr) {
                let frame = mem_set.mappings[vaddr];
                assert(mem_set.mappings.contains_pair(vaddr, frame));
                let (region, i) = choose|region: MemoryRegion, i: nat|
                    mem_set.regions.contains(region)
                        && 0 <= i < region.pages
                        && vaddr == region.spec_page_vaddr(i)
                        && frame == region.spec_frame(i);
                assert(false);
            }
        }
    }
}

/// Shows that a well-formed IOMMU memory set with no entries has no stored regions.
proof fn lemma_no_iommu_entries_implies_empty(
    spec: SoftwareSpec,
    vm: VmId,
)
    requires
        spec.budget.invariant(),
        spec.budget.zones.contains_key(vm.0),
        forall|key: VmPageKey| #[trigger]
            spec@.iommu_s2_map.contains_key(key) ==> key.vm != vm,
    ensures
        spec.budget.zones[vm.0].iommu_mem_set.regions == Set::<MemoryRegion>::empty(),
        spec.budget.zones[vm.0].iommu_mem_set.mappings
            == Map::<SpecVAddr, SpecFrame>::empty(),
{
    assert(spec.budget.inv_zones_wf());
    assert(spec.budget.zones[vm.0].wf());
    let mem_set = spec.budget.zones[vm.0].iommu_mem_set;
    assert(mem_set.wf());
    assert(mem_set.regions =~= Set::<MemoryRegion>::empty()) by {
        assert forall|region: MemoryRegion| !mem_set.regions.contains(region) by {
            if mem_set.regions.contains(region) {
                assert(region.spec_valid());
                let gpa = region_guest_page(region, 0);
                let key = VmPageKey { vm, gpa };
                lemma_gpa_vaddr_roundtrip(region, 0);
                assert(mem_set.mappings.contains_key(vaddr_of_gpa(gpa)));
                assert(zone_iommu_s2_entries(vm.0, spec.budget.zones[vm.0]).contains_key(key));
                assert(spec@.iommu_s2_map.contains_key(key));
                assert(false);
            }
        }
    }
    assert(mem_set.mappings =~= Map::<SpecVAddr, SpecFrame>::empty()) by {
        assert forall|vaddr: SpecVAddr| !mem_set.mappings.contains_key(vaddr) by {
            if mem_set.mappings.contains_key(vaddr) {
                let frame = mem_set.mappings[vaddr];
                assert(mem_set.mappings.contains_pair(vaddr, frame));
                let (region, i) = choose|region: MemoryRegion, i: nat|
                    mem_set.regions.contains(region)
                        && 0 <= i < region.pages
                        && vaddr == region.spec_page_vaddr(i)
                        && frame == region.spec_frame(i);
                assert(false);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// SoftwareSpec implementation
// ---------------------------------------------------------------------------

impl SoftwareRefinement for SoftwareSpec {
    open spec fn invariants(&self) -> bool {
        self.budget.invariant()
    }

    open spec fn region_is_zone_private(&self, region: Region) -> bool {
        budget_region_is_zone_private(*self, region)
    }

    open spec fn region_is_global_shared(&self, region: Region) -> bool {
        budget_region_is_global_shared(*self, region)
    }

    proof fn region_classes_disjoint(&self, region: Region) {
        if self.region_is_zone_private(region) && self.region_is_global_shared(region) {
            lemma_region_classes_disjoint(*self, region);
        }
    }

    broadcast proof fn inv_implies_wf(&self)
        ensures
            #[trigger] self@.wf(),
    {
        lemma_budget_projection_wf(*self);
    }

    broadcast proof fn inv_implies_iommu_wf(&self)
        ensures
            #[trigger] self@.iommu_wf(),
    {
        lemma_budget_projection_wf(*self);
    }

    proof fn add_vm(self, vm: VmId) -> (post: Self) {
        let post = SoftwareSpec {
            budget: BudgetSpec::take_step::add_zone(self.budget, vm.0),
        };
        let empty_zone = GhostZone {
            cpu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
            iommu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
        };
        assert(post.budget.zone_ids == self.budget.zone_ids.insert(vm.0));
        assert(post.budget.zones == self.budget.zones.insert(vm.0, empty_zone));
        assert(post@.all_vms =~= self@.all_vms.insert(vm));
        assert(post@.vm_owned =~= self@.vm_owned.insert(vm, Set::empty())) by {
            assert forall|other: VmId| #[trigger]
                post@.vm_owned.contains_key(other)
                    <==> self@.vm_owned.insert(vm, Set::empty()).contains_key(other) by {
            }
            assert forall|other: VmId| #[trigger]
                post@.vm_owned.contains_key(other) implies post@.vm_owned[other]
                    == self@.vm_owned.insert(vm, Set::empty())[other] by {
                if other == vm {
                    assert(zone_cpu_private_pages(vm.0, empty_zone) =~= Set::empty());
                }
            }
        }
        assert(post@.vm_shared =~= self@.vm_shared) by {
            assert forall|page: PhysPage| post@.vm_shared.contains(page)
                <==> self@.vm_shared.contains(page) by {
                if post@.vm_shared.contains(page) {
                    let zid = choose|zid: nat| #[trigger]
                        post.budget.zone_ids.contains(zid)
                            && zone_cpu_shared_pages(post.budget.zones[zid]).contains(page);
                    assert(zid != vm.0);
                }
                if self@.vm_shared.contains(page) {
                    let zid = choose|zid: nat| #[trigger]
                        self.budget.zone_ids.contains(zid)
                            && zone_cpu_shared_pages(self.budget.zones[zid]).contains(page);
                    assert(post.budget.zone_ids.contains(zid));
                    assert(post.budget.zones[zid] == self.budget.zones[zid]);
                    assert(post@.vm_shared.contains(page));
                }
            }
        }
        assert(post@.s2_map =~= self@.s2_map);
        assert(post@.iommu_owned =~= self@.iommu_owned.insert(vm, Set::empty())) by {
            assert forall|other: VmId| #[trigger]
                post@.iommu_owned.contains_key(other)
                    <==> self@.iommu_owned.insert(vm, Set::empty()).contains_key(other) by {
            }
            assert forall|other: VmId| #[trigger]
                post@.iommu_owned.contains_key(other) implies post@.iommu_owned[other]
                    == self@.iommu_owned.insert(vm, Set::empty())[other] by {
                if other == vm {
                    assert(zone_iommu_private_pages(vm.0, empty_zone) =~= Set::empty());
                }
            }
        }
        assert(post@.iommu_shared =~= self@.iommu_shared) by {
            assert forall|page: PhysPage| post@.iommu_shared.contains(page)
                <==> self@.iommu_shared.contains(page) by {
                if post@.iommu_shared.contains(page) {
                    let zid = choose|zid: nat| #[trigger]
                        post.budget.zone_ids.contains(zid)
                            && zone_iommu_shared_pages(post.budget.zones[zid]).contains(page);
                    assert(zid != vm.0);
                }
                if self@.iommu_shared.contains(page) {
                    let zid = choose|zid: nat| #[trigger]
                        self.budget.zone_ids.contains(zid)
                            && zone_iommu_shared_pages(self.budget.zones[zid]).contains(page);
                    assert(post.budget.zone_ids.contains(zid));
                    assert(post.budget.zones[zid] == self.budget.zones[zid]);
                    assert(post@.iommu_shared.contains(page));
                }
            }
        }
        assert(post@.iommu_s2_map =~= self@.iommu_s2_map);
        post
    }

    proof fn remove_vm(self, vm: VmId) -> (post: Self) {
        assert(self.budget.inv_zone_ids());
        assert(self.budget.zones.contains_key(vm.0));
        lemma_no_cpu_entries_implies_empty(self, vm);
        lemma_no_iommu_entries_implies_empty(self, vm);
        let post = SoftwareSpec {
            budget: BudgetSpec::take_step::remove_zone(self.budget, vm.0),
        };
        assert(post.budget.zone_ids == self.budget.zone_ids.remove(vm.0));
        assert(post.budget.zones == self.budget.zones.remove(vm.0));
        assert(post@.all_vms =~= self@.all_vms.remove(vm));
        assert(post@.vm_owned =~= self@.vm_owned.remove(vm));
        assert(post@.vm_shared =~= self@.vm_shared) by {
            assert forall|page: PhysPage| post@.vm_shared.contains(page)
                <==> self@.vm_shared.contains(page) by {
                if self@.vm_shared.contains(page) {
                    let zid = choose|zid: nat| #[trigger]
                        self.budget.zone_ids.contains(zid)
                            && zone_cpu_shared_pages(self.budget.zones[zid]).contains(page);
                    assert(zid != vm.0);
                }
            }
        }
        assert(post@.s2_map =~= self@.s2_map);
        assert(post@.iommu_owned =~= self@.iommu_owned.remove(vm));
        assert(post@.iommu_shared =~= self@.iommu_shared) by {
            assert forall|page: PhysPage| post@.iommu_shared.contains(page)
                <==> self@.iommu_shared.contains(page) by {
                if self@.iommu_shared.contains(page) {
                    let zid = choose|zid: nat| #[trigger]
                        self.budget.zone_ids.contains(zid)
                            && zone_iommu_shared_pages(self.budget.zones[zid]).contains(page);
                    assert(zid != vm.0);
                }
            }
        }
        assert(post@.iommu_s2_map =~= self@.iommu_s2_map);
        post
    }

    proof fn cpu_insert_zone_private_region(self, region: Region) -> (post: Self) {
        let zid = region.vm.0;
        assert(budget_region_is_zone_private(self, region));
        let concrete = choose_zone_private_region(self, region);
        lemma_cpu_insert_guards(self, region, concrete);
        let post = SoftwareSpec {
            budget: BudgetSpec::take_step::cpu_insert_region(self.budget, zid, concrete),
        };
        assert(post.budget.zone_ids == self.budget.zone_ids);
        assert(post.budget.zones == self.budget.zones.insert(
            zid,
            self.budget.zones[zid].cpu_insert_region(concrete),
        ));
        lemma_cpu_insert_zone_private_projection(self, post, zid, concrete);
        post
    }

    proof fn cpu_remove_zone_private_region(self, region: Region) -> (post: Self) {
        let zid = region.vm.0;
        assert(budget_region_is_zone_private(self, region));
        let concrete = choose_zone_private_region(self, region);
        assert(abstract_region_installed(self@.s2_map, region));
        assert(self.budget.zones[zid].cpu_mem_set.regions.contains(concrete));
        let post = SoftwareSpec {
            budget: BudgetSpec::take_step::cpu_remove_region(self.budget, zid, concrete),
        };
        assert(post.budget.zone_ids == self.budget.zone_ids);
        assert(post.budget.zones == self.budget.zones.insert(
            zid,
            self.budget.zones[zid].cpu_remove_region(concrete),
        ));
        lemma_cpu_remove_zone_private_projection(self, post, zid, concrete);
        post
    }

    proof fn cpu_insert_global_shared_region(self, region: Region) -> (post: Self) {
        let zid = region.vm.0;
        assert(budget_region_is_global_shared(self, region));
        let concrete = choose_global_shared_region(self, region);
        assert(region_in_budget(zid, concrete));
        lemma_cpu_insert_guards(self, region, concrete);
        lemma_global_shared_region_not_zone_private(zid, concrete);
        let post = SoftwareSpec {
            budget: BudgetSpec::take_step::cpu_insert_region(self.budget, zid, concrete),
        };
        assert(post.budget.zone_ids == self.budget.zone_ids);
        assert(post.budget.zones == self.budget.zones.insert(
            zid,
            self.budget.zones[zid].cpu_insert_region(concrete),
        ));
        lemma_cpu_insert_global_shared_projection(self, post, zid, concrete);
        post
    }

    proof fn cpu_remove_global_shared_region(self, region: Region) -> (post: Self) {
        let zid = region.vm.0;
        assert(budget_region_is_global_shared(self, region));
        let concrete = choose_global_shared_region(self, region);
        assert(abstract_region_installed(self@.s2_map, region));
        assert(self.budget.zones[zid].cpu_mem_set.regions.contains(concrete));
        let post = SoftwareSpec {
            budget: BudgetSpec::take_step::cpu_remove_region(self.budget, zid, concrete),
        };
        assert(post.budget.zone_ids == self.budget.zone_ids);
        assert(post.budget.zones == self.budget.zones.insert(
            zid,
            self.budget.zones[zid].cpu_remove_region(concrete),
        ));
        lemma_cpu_remove_global_shared_projection(self, post, zid, concrete);
        post
    }

    proof fn iommu_insert_zone_private_region(self, region: Region) -> (post: Self) {
        let zid = region.vm.0;
        assert(budget_region_is_zone_private(self, region));
        let concrete = choose_zone_private_region(self, region);
        lemma_iommu_insert_guards(self, region, concrete);
        let post = SoftwareSpec {
            budget: BudgetSpec::take_step::iommu_insert_region(self.budget, zid, concrete),
        };
        assert(post.budget.zone_ids == self.budget.zone_ids);
        assert(post.budget.zones == self.budget.zones.insert(
            zid,
            self.budget.zones[zid].iommu_insert_region(concrete),
        ));
        lemma_iommu_insert_zone_private_projection(self, post, zid, concrete);
        post
    }

    proof fn iommu_remove_zone_private_region(self, region: Region) -> (post: Self) {
        let zid = region.vm.0;
        assert(budget_region_is_zone_private(self, region));
        let concrete = choose_zone_private_region(self, region);
        assert(abstract_region_installed(self@.iommu_s2_map, region));
        assert(self.budget.zones[zid].iommu_mem_set.regions.contains(concrete));
        let post = SoftwareSpec {
            budget: BudgetSpec::take_step::iommu_remove_region(self.budget, zid, concrete),
        };
        assert(post.budget.zone_ids == self.budget.zone_ids);
        assert(post.budget.zones == self.budget.zones.insert(
            zid,
            self.budget.zones[zid].iommu_remove_region(concrete),
        ));
        lemma_iommu_remove_zone_private_projection(self, post, zid, concrete);
        post
    }

    proof fn iommu_insert_global_shared_region(self, region: Region) -> (post: Self) {
        let zid = region.vm.0;
        assert(budget_region_is_global_shared(self, region));
        let concrete = choose_global_shared_region(self, region);
        assert(region_in_budget(zid, concrete));
        lemma_iommu_insert_guards(self, region, concrete);
        lemma_global_shared_region_not_zone_private(zid, concrete);
        let post = SoftwareSpec {
            budget: BudgetSpec::take_step::iommu_insert_region(self.budget, zid, concrete),
        };
        assert(post.budget.zone_ids == self.budget.zone_ids);
        assert(post.budget.zones == self.budget.zones.insert(
            zid,
            self.budget.zones[zid].iommu_insert_region(concrete),
        ));
        lemma_iommu_insert_global_shared_projection(self, post, zid, concrete);
        post
    }

    proof fn iommu_remove_global_shared_region(self, region: Region) -> (post: Self) {
        let zid = region.vm.0;
        assert(budget_region_is_global_shared(self, region));
        let concrete = choose_global_shared_region(self, region);
        assert(abstract_region_installed(self@.iommu_s2_map, region));
        assert(self.budget.zones[zid].iommu_mem_set.regions.contains(concrete));
        let post = SoftwareSpec {
            budget: BudgetSpec::take_step::iommu_remove_region(self.budget, zid, concrete),
        };
        assert(post.budget.zone_ids == self.budget.zone_ids);
        assert(post.budget.zones == self.budget.zones.insert(
            zid,
            self.budget.zones[zid].iommu_remove_region(concrete),
        ));
        lemma_iommu_remove_global_shared_projection(self, post, zid, concrete);
        post
    }
}

} // verus!
