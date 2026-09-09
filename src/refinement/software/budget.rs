//! BudgetSpec-specific projection and transition-refinement proofs.
use vstd::prelude::*;

verus! {

use super::*;
use crate::address::addr::SpecVAddr;
use crate::address::frame::SpecFrame;
use crate::address::region::*;
use crate::constants::*;
use crate::hv_mem::spec::budget::*;
use crate::hv_mem::spec::GhostZone;
use crate::memory_set::SpecMemorySet;
use crate::model::convert::*;
use crate::model::software::*;
use crate::model::types::{GuestPage, PhysPage, S2Entry, VmId, VmPageKey};

// ---------------------------------------------------------------------------
// BudgetSpec-specific page classifications and projections
// ---------------------------------------------------------------------------
/// Private pages represented by the zone's installed CPU regions.
pub open spec fn zone_s2_private_pages(zid: nat, zone: GhostZone) -> Set<PhysPage> {
    Set::new(
        |page: PhysPage|
            exists|region: MemoryRegion| #[trigger]
                zone.cpu_mem_set.regions.contains(region) && region_in_private_budget(zid, region)
                    && region_pages(region).contains(page),
    )
}

/// Shared pages represented by the zone's installed CPU regions.
pub open spec fn zone_s2_shared_pages(zone: GhostZone) -> Set<PhysPage> {
    Set::new(
        |page: PhysPage|
            exists|region: MemoryRegion| #[trigger]
                zone.cpu_mem_set.regions.contains(region) && region_in_shared_budget(region)
                    && region_pages(region).contains(page),
    )
}

/// Private pages represented by the zone's installed IOMMU regions.
pub open spec fn zone_iommu_private_pages(zid: nat, zone: GhostZone) -> Set<PhysPage> {
    Set::new(
        |page: PhysPage|
            exists|region: MemoryRegion| #[trigger]
                zone.iommu_mem_set.regions.contains(region) && region_in_private_budget(zid, region)
                    && region_pages(region).contains(page),
    )
}

/// Shared pages represented by the zone's installed IOMMU regions.
pub open spec fn zone_iommu_shared_pages(zone: GhostZone) -> Set<PhysPage> {
    Set::new(
        |page: PhysPage|
            exists|region: MemoryRegion| #[trigger]
                zone.iommu_mem_set.regions.contains(region) && region_in_shared_budget(region)
                    && region_pages(region).contains(page),
    )
}

/// Union of all static private budgets.  Retained for the future
/// allocatable-memory projection; it is not a SoftwareView field.
pub open spec fn all_private_pages() -> Set<PhysPage> {
    Set::new(|page: PhysPage| exists|zid: nat| #[trigger] private_pages(zid).contains(page))
}

/// Private pages currently targeted by a CPU mapping.
pub open spec fn all_s2_private_pages(zones: Map<nat, GhostZone>) -> Set<PhysPage> {
    Set::new(
        |page: PhysPage|
            exists|zid: nat|
                #![trigger zones.contains_key(zid)]
                zones.contains_key(zid) && zone_s2_private_pages(zid, zones[zid]).contains(page),
    )
}

/// Per-VM private pages represented by the current CPU regions.
pub open spec fn state_s2_private_pages(state: BudgetSpec::State) -> Map<VmId, Set<PhysPage>> {
    Map::new(
        |vm: VmId| state.zone_ids.contains(vm.0),
        |vm: VmId| zone_s2_private_pages(vm.0, state.zones[vm.0]),
    )
}

/// Per-VM private pages represented by the current IOMMU regions.
pub open spec fn state_iommu_private_pages(state: BudgetSpec::State) -> Map<VmId, Set<PhysPage>> {
    Map::new(
        |vm: VmId| state.zone_ids.contains(vm.0),
        |vm: VmId| zone_iommu_private_pages(vm.0, state.zones[vm.0]),
    )
}

/// Combines every live zone's CPU entries into the global software-view map.
pub open spec fn state_s2_map(state: BudgetSpec::State) -> Map<VmPageKey, S2Entry> {
    Map::new(
        |key: VmPageKey|
            state.zone_ids.contains(key.vm.0) && zone_s2_entries(
                key.vm.0,
                state.zones[key.vm.0],
            ).contains_key(key),
        |key: VmPageKey| zone_s2_entries(key.vm.0, state.zones[key.vm.0])[key],
    )
}

/// Combines every live zone's IOMMU entries into the global software-view map.
pub open spec fn state_iommu_s2_map(state: BudgetSpec::State) -> Map<VmPageKey, S2Entry> {
    Map::new(
        |key: VmPageKey|
            state.zone_ids.contains(key.vm.0) && zone_iommu_s2_entries(
                key.vm.0,
                state.zones[key.vm.0],
            ).contains_key(key),
        |key: VmPageKey| zone_iommu_s2_entries(key.vm.0, state.zones[key.vm.0])[key],
    )
}

/// Shared pages targeted by at least one current CPU mapping.
pub open spec fn state_s2_shared_pages(state: BudgetSpec::State) -> Set<PhysPage> {
    Set::new(
        |page: PhysPage|
            exists|zid: nat|
                #![trigger state.zone_ids.contains(zid)]
                state.zone_ids.contains(zid) && zone_s2_shared_pages(state.zones[zid]).contains(
                    page,
                ),
    )
}

/// Shared pages targeted by at least one current IOMMU mapping.
pub open spec fn state_iommu_shared_pages(state: BudgetSpec::State) -> Set<PhysPage> {
    Set::new(
        |page: PhysPage|
            exists|zid: nat|
                #![trigger state.zone_ids.contains(zid)]
                state.zone_ids.contains(zid) && zone_iommu_shared_pages(state.zones[zid]).contains(
                    page,
                ),
    )
}

/// BudgetSpec state equipped with its policy-neutral [`SoftwareView`] projection.
pub ghost struct SoftwareSpec {
    /// Concrete state whose budgets and installed regions determine the view.
    pub budget: BudgetSpec::State,
}

impl SoftwareSpec {
    pub open spec fn view(&self) -> SoftwareView {
        SoftwareView {
            all_vms: Set::new(|vm: VmId| self.budget.zone_ids.contains(vm.0)),
            s2_private_pages: state_s2_private_pages(self.budget),
            s2_shared_pages: state_s2_shared_pages(self.budget),
            s2_map: state_s2_map(self.budget),
            iommu_private_pages: state_iommu_private_pages(self.budget),
            iommu_shared_pages: state_iommu_shared_pages(self.budget),
            iommu_s2_map: state_iommu_s2_map(self.budget),
        }
    }
}

// ---------------------------------------------------------------------------
// Projection facts
// ---------------------------------------------------------------------------
/// Proves that every invariant BudgetSpec state projects to a well-formed SoftwareView.
proof fn lemma_budget_projection_wf(spec: SoftwareSpec)
    requires
        spec.budget.invariant(),
    ensures
        spec.view().wf(),
{
    let sw = spec.view();
    assert(spec.budget.inv_zone_ids());
    assert(spec.budget.inv_zones_wf());
    assert(spec.budget.inv_cpu_regions_in_budget());
    assert(spec.budget.inv_iommu_regions_in_budget());
    private_pages_pairwise_disjoint();
    private_pages_disjoint_from_shared();

    assert(sw.s2_private_pages.dom() =~= sw.all_vms);
    assert(forall|vm1: VmId, vm2: VmId| #[trigger]
        sw.all_vms.contains(vm1) && #[trigger] sw.all_vms.contains(vm2) && vm1 != vm2 ==> forall|
            page: PhysPage,
        | #[trigger]
            sw.s2_private_pages[vm1].contains(page) ==> !sw.s2_private_pages[vm2].contains(page));
    assert(forall|vm: VmId| #[trigger]
        sw.all_vms.contains(vm) ==> forall|page: PhysPage| #[trigger]
            sw.s2_private_pages[vm].contains(page) ==> !sw.s2_shared_pages.contains(page));
    assert(sw.s2_classification_wf());

    assert forall|key: VmPageKey| #[trigger] sw.s2_map.contains_key(key) implies {
        &&& sw.all_vms.contains(key.vm)
        &&& sw.s2_private_or_shared(key.vm, sw.s2_map[key].page)
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
        if region_in_private_budget(zid, concrete) {
            assert(sw.s2_private_pages[key.vm].contains(page));
        } else {
            assert(region_in_shared_budget(concrete));
            assert(sw.s2_shared_pages.contains(page));
        }
    }
    assert(sw.translation_wf());

    assert(sw.iommu_private_pages.dom() =~= sw.all_vms);
    assert(forall|vm1: VmId, vm2: VmId| #[trigger]
        sw.all_vms.contains(vm1) && #[trigger] sw.all_vms.contains(vm2) && vm1 != vm2 ==> forall|
            page: PhysPage,
        | #[trigger]
            sw.iommu_private_pages[vm1].contains(page) ==> !sw.iommu_private_pages[vm2].contains(
                page,
            ));
    assert(forall|vm1: VmId, vm2: VmId| #[trigger]
        sw.all_vms.contains(vm1) && #[trigger] sw.all_vms.contains(vm2) && vm1 != vm2 ==> forall|
            page: PhysPage,
        | #[trigger]
            sw.iommu_private_pages[vm1].contains(page) ==> !sw.s2_private_pages[vm2].contains(
                page,
            ));
    assert(forall|vm: VmId| #[trigger]
        sw.all_vms.contains(vm) ==> forall|page: PhysPage| #[trigger]
            sw.iommu_private_pages[vm].contains(page) ==> !sw.iommu_shared_pages.contains(page));
    assert(forall|vm: VmId| #[trigger]
        sw.all_vms.contains(vm) ==> forall|page: PhysPage| #[trigger]
            sw.s2_private_pages[vm].contains(page) ==> !sw.iommu_shared_pages.contains(page));
    assert(sw.iommu_classification_wf());

    assert forall|key: VmPageKey| #[trigger] sw.iommu_s2_map.contains_key(key) implies {
        &&& sw.all_vms.contains(key.vm)
        &&& sw.iommu_private_pages.contains_key(key.vm)
        &&& (sw.iommu_private_pages[key.vm].contains(sw.iommu_s2_map[key].page)
            || sw.iommu_shared_pages.contains(sw.iommu_s2_map[key].page))
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
        if region_in_private_budget(zid, concrete) {
            assert(sw.iommu_private_pages[key.vm].contains(page));
        } else {
            assert(region_in_shared_budget(concrete));
            assert(sw.iommu_shared_pages.contains(page));
        }
    }
    assert(sw.iommu_translation_wf());
    assert(sw.iommu_wf());
    assert(sw.wf());
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
        state_s2_map(post) =~= state_s2_map(pre).union_prefer_right(region_s2_entries(zid, region)),
{
    assert(pre.inv_zones_wf());
    assert(pre.zones[zid].wf());
    lemma_memory_set_s2_insert(zid, pre.zones[zid].cpu_mem_set, region);
    let lhs = state_s2_map(post);
    let rhs = state_s2_map(pre).union_prefer_right(region_s2_entries(zid, region));
    assert forall|key: VmPageKey| #[trigger] lhs.contains_key(key) <==> rhs.contains_key(key) by {
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
        state_s2_map(post) =~= state_s2_map(pre).remove_keys(region_s2_entries(zid, region).dom()),
{
    assert(pre.inv_zones_wf());
    assert(pre.zones[zid].wf());
    lemma_memory_set_s2_remove(zid, pre.zones[zid].cpu_mem_set, region);
    let lhs = state_s2_map(post);
    let rhs = state_s2_map(pre).remove_keys(region_s2_entries(zid, region).dom());
    assert forall|key: VmPageKey| #[trigger] lhs.contains_key(key) <==> rhs.contains_key(key) by {
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
    assert forall|key: VmPageKey| #[trigger] lhs.contains_key(key) <==> rhs.contains_key(key) by {
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
    assert forall|key: VmPageKey| #[trigger] lhs.contains_key(key) <==> rhs.contains_key(key) by {
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

/// Proves the SoftwareView effect of inserting one private CPU region.
proof fn lemma_cpu_insert_private_projection(
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
        region_in_private_budget(zid, concrete),
        !pre.budget.zones[zid].cpu_mem_set.overlaps_vmem(concrete),
        post.budget.zone_ids == pre.budget.zone_ids,
        post.budget.zones == pre.budget.zones.insert(
            zid,
            pre.budget.zones[zid].cpu_insert_region(concrete),
        ),
    ensures
        SoftwareView::cpu_insert_private_region_step(
            pre.view(),
            post.view(),
            region_to_abstract(zid, concrete),
        ),
{
    assert(pre.budget.inv_zones_wf());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_state_s2_insert(pre.budget, post.budget, zid, concrete);
    private_pages_disjoint_from_shared();
    assert(post.view().all_vms =~= pre.view().all_vms);
    assert(post.view().s2_map =~= pre.view().s2_map.union_prefer_right(
        region_to_abstract(zid, concrete).entries(),
    ));
    assert(post.view().iommu_private_pages =~= pre.view().iommu_private_pages);
    assert(post.view().iommu_shared_pages =~= pre.view().iommu_shared_pages);
    assert(post.view().iommu_s2_map =~= pre.view().iommu_s2_map);
    lemma_private_region_not_shared(zid, concrete);
    let target_private = pre.view().s2_private_pages.insert(
        VmId(zid),
        pre.view().s2_private_pages[VmId(zid)].union(region_pages(concrete)),
    );
    assert(post.view().s2_private_pages =~= target_private) by {
        assert(post.view().s2_private_pages.dom() =~= target_private.dom());
        assert forall|vm: VmId| #[trigger]
            post.view().s2_private_pages.contains_key(vm) implies post.view().s2_private_pages[vm]
            =~= target_private[vm] by {
            if vm.0 == zid {
                assert forall|page: PhysPage|
                    post.view().s2_private_pages[vm].contains(page)
                        <==> target_private[vm].contains(page) by {
                    if post.view().s2_private_pages[vm].contains(page) {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            post.budget.zones[zid].cpu_mem_set.regions.contains(stored)
                                && region_in_private_budget(zid, stored) && region_pages(
                                stored,
                            ).contains(page);
                        if stored != concrete {
                            assert(pre.budget.zones[zid].cpu_mem_set.regions.contains(stored));
                        }
                    }
                    if target_private[vm].contains(page) && region_pages(concrete).contains(page) {
                        assert(post.budget.zones[zid].cpu_mem_set.regions.contains(concrete));
                    }
                    if pre.view().s2_private_pages[vm].contains(page) {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            pre.budget.zones[zid].cpu_mem_set.regions.contains(stored)
                                && region_in_private_budget(zid, stored) && region_pages(
                                stored,
                            ).contains(page);
                        assert(post.budget.zones[zid].cpu_mem_set.regions.contains(stored));
                        assert(post.view().s2_private_pages[vm].contains(page));
                    }
                }
            }
        }
    }
    assert(post.view().s2_shared_pages =~= pre.view().s2_shared_pages) by {
        assert forall|page: PhysPage|
            post.view().s2_shared_pages.contains(page) <==> pre.view().s2_shared_pages.contains(
                page,
            ) by {
            if post.view().s2_shared_pages.contains(page) {
                let zone_id = choose|zone_id: nat| #[trigger]
                    post.budget.zone_ids.contains(zone_id) && zone_s2_shared_pages(
                        post.budget.zones[zone_id],
                    ).contains(page);
                if zone_id == zid {
                    let stored = choose|stored: MemoryRegion| #[trigger]
                        post.budget.zones[zid].cpu_mem_set.regions.contains(stored)
                            && region_in_shared_budget(stored) && region_pages(stored).contains(
                            page,
                        );
                    assert(stored != concrete);
                }
            }
            if pre.view().s2_shared_pages.contains(page) {
                let zone_id = choose|zone_id: nat| #[trigger]
                    pre.budget.zone_ids.contains(zone_id) && zone_s2_shared_pages(
                        pre.budget.zones[zone_id],
                    ).contains(page);
                let stored = choose|stored: MemoryRegion| #[trigger]
                    pre.budget.zones[zone_id].cpu_mem_set.regions.contains(stored)
                        && region_in_shared_budget(stored) && region_pages(stored).contains(page);
                assert(post.budget.zones[zone_id].cpu_mem_set.regions.contains(stored));
                assert(post.view().s2_shared_pages.contains(page));
            }
        }
    }
}

/// Proves the SoftwareView effect of inserting one shared CPU region.
proof fn lemma_cpu_insert_shared_projection(
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
        region_in_shared_budget(concrete),
        !pre.budget.zones[zid].cpu_mem_set.overlaps_vmem(concrete),
        post.budget.zone_ids == pre.budget.zone_ids,
        post.budget.zones == pre.budget.zones.insert(
            zid,
            pre.budget.zones[zid].cpu_insert_region(concrete),
        ),
    ensures
        SoftwareView::cpu_insert_shared_region_step(
            pre.view(),
            post.view(),
            region_to_abstract(zid, concrete),
        ),
{
    assert(pre.budget.inv_zones_wf());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_state_s2_insert(pre.budget, post.budget, zid, concrete);
    private_pages_disjoint_from_shared();
    assert(post.view().all_vms =~= pre.view().all_vms);
    assert(post.view().s2_map =~= pre.view().s2_map.union_prefer_right(
        region_to_abstract(zid, concrete).entries(),
    ));
    assert(post.view().iommu_private_pages =~= pre.view().iommu_private_pages);
    assert(post.view().iommu_shared_pages =~= pre.view().iommu_shared_pages);
    assert(post.view().iommu_s2_map =~= pre.view().iommu_s2_map);
    lemma_shared_region_not_private(zid, concrete);
    assert(post.view().s2_private_pages =~= pre.view().s2_private_pages) by {
        assert forall|vm: VmId| #[trigger]
            post.view().s2_private_pages.contains_key(vm) implies post.view().s2_private_pages[vm]
            =~= pre.view().s2_private_pages[vm] by {
            if vm.0 == zid {
                assert forall|page: PhysPage|
                    post.view().s2_private_pages[vm].contains(page)
                        <==> pre.view().s2_private_pages[vm].contains(page) by {
                    if post.view().s2_private_pages[vm].contains(page) {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            post.budget.zones[zid].cpu_mem_set.regions.contains(stored)
                                && region_in_private_budget(zid, stored) && region_pages(
                                stored,
                            ).contains(page);
                        assert(stored != concrete);
                    }
                    if pre.view().s2_private_pages[vm].contains(page) {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            pre.budget.zones[zid].cpu_mem_set.regions.contains(stored)
                                && region_in_private_budget(zid, stored) && region_pages(
                                stored,
                            ).contains(page);
                        assert(post.budget.zones[zid].cpu_mem_set.regions.contains(stored));
                        assert(post.view().s2_private_pages[vm].contains(page));
                    }
                }
            }
        }
    }
    assert(post.view().s2_shared_pages =~= pre.view().s2_shared_pages.union(region_pages(concrete)))
        by {
        assert forall|page: PhysPage|
            post.view().s2_shared_pages.contains(page) <==> pre.view().s2_shared_pages.union(
                region_pages(concrete),
            ).contains(page) by {
            if post.view().s2_shared_pages.contains(page) {
                let zone_id = choose|zone_id: nat| #[trigger]
                    post.budget.zone_ids.contains(zone_id) && zone_s2_shared_pages(
                        post.budget.zones[zone_id],
                    ).contains(page);
                if zone_id == zid {
                    let stored = choose|stored: MemoryRegion| #[trigger]
                        post.budget.zones[zid].cpu_mem_set.regions.contains(stored)
                            && region_in_shared_budget(stored) && region_pages(stored).contains(
                            page,
                        );
                    if stored != concrete {
                        assert(pre.budget.zones[zid].cpu_mem_set.regions.contains(stored));
                    }
                }
            }
            if region_pages(concrete).contains(page) {
                assert(post.budget.zones[zid].cpu_mem_set.regions.contains(concrete));
            }
            if pre.view().s2_shared_pages.contains(page) {
                let zone_id = choose|zone_id: nat| #[trigger]
                    pre.budget.zone_ids.contains(zone_id) && zone_s2_shared_pages(
                        pre.budget.zones[zone_id],
                    ).contains(page);
                let stored = choose|stored: MemoryRegion| #[trigger]
                    pre.budget.zones[zone_id].cpu_mem_set.regions.contains(stored)
                        && region_in_shared_budget(stored) && region_pages(stored).contains(page);
                assert(post.budget.zones[zone_id].cpu_mem_set.regions.contains(stored));
                assert(post.view().s2_shared_pages.contains(page));
            }
        }
    }
}

/// Proves the SoftwareView effect of removing one private CPU region.
proof fn lemma_cpu_remove_private_projection(
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
        region_in_private_budget(zid, concrete),
        post.budget.zone_ids == pre.budget.zone_ids,
        post.budget.zones == pre.budget.zones.insert(
            zid,
            pre.budget.zones[zid].cpu_remove_region(concrete),
        ),
    ensures
        SoftwareView::cpu_remove_private_region_step(
            pre.view(),
            post.view(),
            region_to_abstract(zid, concrete),
        ),
{
    assert(pre.budget.inv_zones_wf());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_state_s2_remove(pre.budget, post.budget, zid, concrete);
    assert(post.view().all_vms =~= pre.view().all_vms);
    assert(post.view().s2_map =~= pre.view().s2_map.remove_keys(
        region_to_abstract(zid, concrete).entries().dom(),
    ));
    assert(post.view().iommu_private_pages =~= pre.view().iommu_private_pages);
    assert(post.view().iommu_shared_pages =~= pre.view().iommu_shared_pages);
    assert(post.view().iommu_s2_map =~= pre.view().iommu_s2_map);
    assert(pre.budget.inv_cpu_private_regions_pmem_nonoverlap());
    lemma_private_region_not_shared(zid, concrete);
    let target_private = pre.view().s2_private_pages.insert(
        VmId(zid),
        pre.view().s2_private_pages[VmId(zid)].difference(region_pages(concrete)),
    );
    assert(post.view().s2_private_pages =~= target_private) by {
        assert(post.view().s2_private_pages.dom() =~= target_private.dom());
        assert forall|vm: VmId| #[trigger]
            post.view().s2_private_pages.contains_key(vm) implies post.view().s2_private_pages[vm]
            =~= target_private[vm] by {
            if vm.0 == zid {
                assert forall|page: PhysPage|
                    post.view().s2_private_pages[vm].contains(page)
                        <==> target_private[vm].contains(page) by {
                    if post.view().s2_private_pages[vm].contains(page) {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            post.budget.zones[zid].cpu_mem_set.regions.contains(stored)
                                && region_in_private_budget(zid, stored) && region_pages(
                                stored,
                            ).contains(page);
                        assert(stored != concrete);
                        assert(pre.budget.zones[zid].cpu_mem_set.regions.contains(stored));
                        if region_pages(concrete).contains(page) {
                            lemma_shared_page_implies_pmem_overlap(stored, concrete, page);
                            assert(!stored.spec_overlaps_pmem(concrete));
                            assert(false);
                        }
                    }
                    if target_private[vm].contains(page) {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            pre.budget.zones[zid].cpu_mem_set.regions.contains(stored)
                                && region_in_private_budget(zid, stored) && region_pages(
                                stored,
                            ).contains(page);
                        assert(stored != concrete);
                        assert(post.budget.zones[zid].cpu_mem_set.regions.contains(stored));
                    }
                }
            }
        }
    }
    assert(post.view().s2_shared_pages =~= pre.view().s2_shared_pages) by {
        assert forall|page: PhysPage|
            post.view().s2_shared_pages.contains(page) <==> pre.view().s2_shared_pages.contains(
                page,
            ) by {
            if pre.view().s2_shared_pages.contains(page) {
                let zone_id = choose|zone_id: nat| #[trigger]
                    pre.budget.zone_ids.contains(zone_id) && zone_s2_shared_pages(
                        pre.budget.zones[zone_id],
                    ).contains(page);
                if zone_id == zid {
                    let stored = choose|stored: MemoryRegion| #[trigger]
                        pre.budget.zones[zid].cpu_mem_set.regions.contains(stored)
                            && region_in_shared_budget(stored) && region_pages(stored).contains(
                            page,
                        );
                    assert(stored != concrete);
                }
            }
        }
    }
}

/// Proves the SoftwareView effect of removing one shared CPU region.
proof fn lemma_cpu_remove_shared_projection(
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
        region_in_shared_budget(concrete),
        post.budget.zone_ids == pre.budget.zone_ids,
        post.budget.zones == pre.budget.zones.insert(
            zid,
            pre.budget.zones[zid].cpu_remove_region(concrete),
        ),
    ensures
        SoftwareView::cpu_remove_shared_region_step(
            pre.view(),
            post.view(),
            region_to_abstract(zid, concrete),
        ),
{
    assert(pre.budget.inv_zones_wf());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_state_s2_remove(pre.budget, post.budget, zid, concrete);
    assert(post.view().all_vms =~= pre.view().all_vms);
    assert(post.view().s2_map =~= pre.view().s2_map.remove_keys(
        region_to_abstract(zid, concrete).entries().dom(),
    ));
    assert(post.view().iommu_private_pages =~= pre.view().iommu_private_pages);
    assert(post.view().iommu_shared_pages =~= pre.view().iommu_shared_pages);
    assert(post.view().iommu_s2_map =~= pre.view().iommu_s2_map);
    lemma_shared_region_not_private(zid, concrete);
    assert(post.view().s2_private_pages =~= pre.view().s2_private_pages) by {
        assert forall|vm: VmId| #[trigger]
            post.view().s2_private_pages.contains_key(vm) implies post.view().s2_private_pages[vm]
            =~= pre.view().s2_private_pages[vm] by {
            if vm.0 == zid {
                assert forall|page: PhysPage|
                    post.view().s2_private_pages[vm].contains(page)
                        <==> pre.view().s2_private_pages[vm].contains(page) by {
                    if pre.view().s2_private_pages[vm].contains(page) {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            pre.budget.zones[zid].cpu_mem_set.regions.contains(stored)
                                && region_in_private_budget(zid, stored) && region_pages(
                                stored,
                            ).contains(page);
                        assert(stored != concrete);
                    }
                }
            }
        }
    }
    let target_shared = Set::new(
        |page: PhysPage|
            {
                let post_map = pre.view().s2_map.remove_keys(
                    region_to_abstract(zid, concrete).entries().dom(),
                );
                &&& pre.view().s2_shared_pages.contains(page)
                &&& (!region_pages(concrete).contains(page) || exists|key: VmPageKey| #[trigger]
                    post_map.contains_key(key) && post_map[key].page == page)
            },
    );
    assert(post.budget.inv_zone_ids());
    assert(post.budget.inv_zones_wf());
    assert(post.budget.inv_cpu_regions_in_budget());
    private_pages_disjoint_from_shared();
    assert(post.view().s2_shared_pages =~= target_shared) by {
        assert forall|page: PhysPage|
            post.view().s2_shared_pages.contains(page) <==> target_shared.contains(page) by {
            if post.view().s2_shared_pages.contains(page) {
                let zone_id = choose|zone_id: nat| #[trigger]
                    post.budget.zone_ids.contains(zone_id) && zone_s2_shared_pages(
                        post.budget.zones[zone_id],
                    ).contains(page);
                let stored = choose|stored: MemoryRegion| #[trigger]
                    post.budget.zones[zone_id].cpu_mem_set.regions.contains(stored)
                        && region_in_shared_budget(stored) && region_pages(stored).contains(page);
                assert(pre.view().s2_shared_pages.contains(page));
                if region_pages(concrete).contains(page) {
                    assert(post.budget.zones[zone_id].wf());
                    let i = choose|i: nat|
                        0 <= i < stored.pages && region_phys_page(stored, i) == page;
                    let key = VmPageKey { vm: VmId(zone_id), gpa: region_guest_page(stored, i) };
                    lemma_gpa_vaddr_roundtrip(stored, i);
                    lemma_region_phys_page_linear(stored, i);
                    assert(post.budget.zones[zone_id].cpu_mem_set.mappings.contains_pair(
                        stored.spec_page_vaddr(i),
                        stored.spec_frame(i),
                    ));
                    assert(post.view().s2_map.contains_key(key));
                    assert(post.view().s2_map[key].page == page);
                }
            }
            if target_shared.contains(page) {
                if !region_pages(concrete).contains(page) {
                    let zone_id = choose|zone_id: nat| #[trigger]
                        pre.budget.zone_ids.contains(zone_id) && zone_s2_shared_pages(
                            pre.budget.zones[zone_id],
                        ).contains(page);
                    let stored = choose|stored: MemoryRegion| #[trigger]
                        pre.budget.zones[zone_id].cpu_mem_set.regions.contains(stored)
                            && region_in_shared_budget(stored) && region_pages(stored).contains(
                            page,
                        );
                    if zone_id == zid {
                        assert(stored != concrete);
                    }
                    assert(post.budget.zones[zone_id].cpu_mem_set.regions.contains(stored));
                } else {
                    let key = choose|key: VmPageKey| #[trigger]
                        post.view().s2_map.contains_key(key) && post.view().s2_map[key].page
                            == page;
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
                    if region_in_private_budget(zone_id, stored) {
                        assert(private_pages(zone_id).contains(page));
                        assert(shared_pages().contains(page));
                        assert(false);
                    }
                    assert(region_in_shared_budget(stored));
                    assert(post.view().s2_shared_pages.contains(page));
                }
            }
        }
    }
    let abstract_region = region_to_abstract(zid, concrete);
    let expected_shared = Set::new(
        |page: PhysPage|
            {
                let post_map = pre.view().s2_map.remove_keys(abstract_region.entries().dom());
                &&& pre.view().s2_shared_pages.contains(page)
                &&& (!abstract_region.pages().contains(page) || exists|key: VmPageKey| #[trigger]
                    post_map.contains_key(key) && post_map[key].page == page)
            },
    );
    assert(forall|page: PhysPage| target_shared.contains(page) <==> expected_shared.contains(page));
    assert(target_shared =~= expected_shared);
    assert(post.view().s2_shared_pages == expected_shared);
    assert(post.view().s2_private_pages == pre.view().s2_private_pages);
    assert(post.view().all_vms == pre.view().all_vms);
    assert(post.view().s2_map == pre.view().s2_map.remove_keys(abstract_region.entries().dom()));
    assert(post.view().iommu_private_pages == pre.view().iommu_private_pages);
    assert(post.view().iommu_shared_pages == pre.view().iommu_shared_pages);
    assert(post.view().iommu_s2_map == pre.view().iommu_s2_map);
    assert(SoftwareView::cpu_remove_shared_region_step(pre.view(), post.view(), abstract_region));
}

/// Proves the SoftwareView effect of inserting one private IOMMU region.
proof fn lemma_iommu_insert_private_projection(
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
        region_in_private_budget(zid, concrete),
        !pre.budget.zones[zid].iommu_mem_set.overlaps_vmem(concrete),
        post.budget.zone_ids == pre.budget.zone_ids,
        post.budget.zones == pre.budget.zones.insert(
            zid,
            pre.budget.zones[zid].iommu_insert_region(concrete),
        ),
    ensures
        SoftwareView::iommu_insert_private_region_step(
            pre.view(),
            post.view(),
            region_to_abstract(zid, concrete),
        ),
{
    assert(pre.budget.inv_zones_wf());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_state_iommu_s2_insert(pre.budget, post.budget, zid, concrete);
    private_pages_disjoint_from_shared();
    assert(post.view().all_vms =~= pre.view().all_vms);
    assert(post.view().s2_private_pages =~= pre.view().s2_private_pages);
    assert(post.view().s2_shared_pages =~= pre.view().s2_shared_pages);
    assert(post.view().s2_map =~= pre.view().s2_map);
    assert(post.view().iommu_s2_map =~= pre.view().iommu_s2_map.union_prefer_right(
        region_to_abstract(zid, concrete).entries(),
    ));
    lemma_private_region_not_shared(zid, concrete);
    let target_private = pre.view().iommu_private_pages.insert(
        VmId(zid),
        pre.view().iommu_private_pages[VmId(zid)].union(region_pages(concrete)),
    );
    assert(post.view().iommu_private_pages =~= target_private) by {
        assert(post.view().iommu_private_pages.dom() =~= target_private.dom());
        assert forall|vm: VmId| #[trigger]
            post.view().iommu_private_pages.contains_key(
                vm,
            ) implies post.view().iommu_private_pages[vm] =~= target_private[vm] by {
            if vm.0 == zid {
                assert forall|page: PhysPage|
                    post.view().iommu_private_pages[vm].contains(page)
                        <==> target_private[vm].contains(page) by {
                    if post.view().iommu_private_pages[vm].contains(page) {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            post.budget.zones[zid].iommu_mem_set.regions.contains(stored)
                                && region_in_private_budget(zid, stored) && region_pages(
                                stored,
                            ).contains(page);
                        if stored != concrete {
                            assert(pre.budget.zones[zid].iommu_mem_set.regions.contains(stored));
                        }
                    }
                    if target_private[vm].contains(page) && region_pages(concrete).contains(page) {
                        assert(post.budget.zones[zid].iommu_mem_set.regions.contains(concrete));
                    }
                    if pre.view().iommu_private_pages[vm].contains(page) {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            pre.budget.zones[zid].iommu_mem_set.regions.contains(stored)
                                && region_in_private_budget(zid, stored) && region_pages(
                                stored,
                            ).contains(page);
                        assert(post.budget.zones[zid].iommu_mem_set.regions.contains(stored));
                        assert(post.view().iommu_private_pages[vm].contains(page));
                    }
                }
            }
        }
    }
    assert(post.view().iommu_shared_pages =~= pre.view().iommu_shared_pages) by {
        assert forall|page: PhysPage|
            post.view().iommu_shared_pages.contains(page)
                <==> pre.view().iommu_shared_pages.contains(page) by {
            if post.view().iommu_shared_pages.contains(page) {
                let zone_id = choose|zone_id: nat| #[trigger]
                    post.budget.zone_ids.contains(zone_id) && zone_iommu_shared_pages(
                        post.budget.zones[zone_id],
                    ).contains(page);
                if zone_id == zid {
                    let stored = choose|stored: MemoryRegion| #[trigger]
                        post.budget.zones[zid].iommu_mem_set.regions.contains(stored)
                            && region_in_shared_budget(stored) && region_pages(stored).contains(
                            page,
                        );
                    assert(stored != concrete);
                }
            }
            if pre.view().iommu_shared_pages.contains(page) {
                let zone_id = choose|zone_id: nat| #[trigger]
                    pre.budget.zone_ids.contains(zone_id) && zone_iommu_shared_pages(
                        pre.budget.zones[zone_id],
                    ).contains(page);
                let stored = choose|stored: MemoryRegion| #[trigger]
                    pre.budget.zones[zone_id].iommu_mem_set.regions.contains(stored)
                        && region_in_shared_budget(stored) && region_pages(stored).contains(page);
                assert(post.budget.zones[zone_id].iommu_mem_set.regions.contains(stored));
                assert(post.view().iommu_shared_pages.contains(page));
            }
        }
    }
}

/// Proves the SoftwareView effect of inserting one shared IOMMU region.
proof fn lemma_iommu_insert_shared_projection(
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
        region_in_shared_budget(concrete),
        !pre.budget.zones[zid].iommu_mem_set.overlaps_vmem(concrete),
        post.budget.zone_ids == pre.budget.zone_ids,
        post.budget.zones == pre.budget.zones.insert(
            zid,
            pre.budget.zones[zid].iommu_insert_region(concrete),
        ),
    ensures
        SoftwareView::iommu_insert_shared_region_step(
            pre.view(),
            post.view(),
            region_to_abstract(zid, concrete),
        ),
{
    assert(pre.budget.inv_zones_wf());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_state_iommu_s2_insert(pre.budget, post.budget, zid, concrete);
    private_pages_disjoint_from_shared();
    assert(post.view().all_vms =~= pre.view().all_vms);
    assert(post.view().s2_private_pages =~= pre.view().s2_private_pages);
    assert(post.view().s2_shared_pages =~= pre.view().s2_shared_pages);
    assert(post.view().s2_map =~= pre.view().s2_map);
    assert(post.view().iommu_s2_map =~= pre.view().iommu_s2_map.union_prefer_right(
        region_to_abstract(zid, concrete).entries(),
    ));
    lemma_shared_region_not_private(zid, concrete);
    assert(post.view().iommu_private_pages =~= pre.view().iommu_private_pages) by {
        assert forall|vm: VmId| #[trigger]
            post.view().iommu_private_pages.contains_key(
                vm,
            ) implies post.view().iommu_private_pages[vm]
            =~= pre.view().iommu_private_pages[vm] by {
            if vm.0 == zid {
                assert forall|page: PhysPage|
                    post.view().iommu_private_pages[vm].contains(page)
                        <==> pre.view().iommu_private_pages[vm].contains(page) by {
                    if post.view().iommu_private_pages[vm].contains(page) {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            post.budget.zones[zid].iommu_mem_set.regions.contains(stored)
                                && region_in_private_budget(zid, stored) && region_pages(
                                stored,
                            ).contains(page);
                        assert(stored != concrete);
                    }
                    if pre.view().iommu_private_pages[vm].contains(page) {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            pre.budget.zones[zid].iommu_mem_set.regions.contains(stored)
                                && region_in_private_budget(zid, stored) && region_pages(
                                stored,
                            ).contains(page);
                        assert(post.budget.zones[zid].iommu_mem_set.regions.contains(stored));
                        assert(post.view().iommu_private_pages[vm].contains(page));
                    }
                }
            }
        }
    }
    assert(post.view().iommu_shared_pages =~= pre.view().iommu_shared_pages.union(
        region_pages(concrete),
    )) by {
        assert forall|page: PhysPage|
            post.view().iommu_shared_pages.contains(page) <==> pre.view().iommu_shared_pages.union(
                region_pages(concrete),
            ).contains(page) by {
            if post.view().iommu_shared_pages.contains(page) {
                let zone_id = choose|zone_id: nat| #[trigger]
                    post.budget.zone_ids.contains(zone_id) && zone_iommu_shared_pages(
                        post.budget.zones[zone_id],
                    ).contains(page);
                if zone_id == zid {
                    let stored = choose|stored: MemoryRegion| #[trigger]
                        post.budget.zones[zid].iommu_mem_set.regions.contains(stored)
                            && region_in_shared_budget(stored) && region_pages(stored).contains(
                            page,
                        );
                    if stored != concrete {
                        assert(pre.budget.zones[zid].iommu_mem_set.regions.contains(stored));
                    }
                }
            }
            if region_pages(concrete).contains(page) {
                assert(post.budget.zones[zid].iommu_mem_set.regions.contains(concrete));
            }
            if pre.view().iommu_shared_pages.contains(page) {
                let zone_id = choose|zone_id: nat| #[trigger]
                    pre.budget.zone_ids.contains(zone_id) && zone_iommu_shared_pages(
                        pre.budget.zones[zone_id],
                    ).contains(page);
                let stored = choose|stored: MemoryRegion| #[trigger]
                    pre.budget.zones[zone_id].iommu_mem_set.regions.contains(stored)
                        && region_in_shared_budget(stored) && region_pages(stored).contains(page);
                assert(post.budget.zones[zone_id].iommu_mem_set.regions.contains(stored));
                assert(post.view().iommu_shared_pages.contains(page));
            }
        }
    }
}

/// Proves the SoftwareView effect of removing one private IOMMU region.
proof fn lemma_iommu_remove_private_projection(
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
        region_in_private_budget(zid, concrete),
        post.budget.zone_ids == pre.budget.zone_ids,
        post.budget.zones == pre.budget.zones.insert(
            zid,
            pre.budget.zones[zid].iommu_remove_region(concrete),
        ),
    ensures
        SoftwareView::iommu_remove_private_region_step(
            pre.view(),
            post.view(),
            region_to_abstract(zid, concrete),
        ),
{
    assert(pre.budget.inv_zones_wf());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_state_iommu_s2_remove(pre.budget, post.budget, zid, concrete);
    assert(post.view().all_vms =~= pre.view().all_vms);
    assert(post.view().s2_private_pages =~= pre.view().s2_private_pages);
    assert(post.view().s2_shared_pages =~= pre.view().s2_shared_pages);
    assert(post.view().s2_map =~= pre.view().s2_map);
    assert(post.view().iommu_s2_map =~= pre.view().iommu_s2_map.remove_keys(
        region_to_abstract(zid, concrete).entries().dom(),
    ));
    assert(pre.budget.inv_iommu_private_regions_pmem_nonoverlap());
    lemma_private_region_not_shared(zid, concrete);
    let target_private = pre.view().iommu_private_pages.insert(
        VmId(zid),
        pre.view().iommu_private_pages[VmId(zid)].difference(region_pages(concrete)),
    );
    assert(post.view().iommu_private_pages =~= target_private) by {
        assert(post.view().iommu_private_pages.dom() =~= target_private.dom());
        assert forall|vm: VmId| #[trigger]
            post.view().iommu_private_pages.contains_key(
                vm,
            ) implies post.view().iommu_private_pages[vm] =~= target_private[vm] by {
            if vm.0 == zid {
                assert forall|page: PhysPage|
                    post.view().iommu_private_pages[vm].contains(page)
                        <==> target_private[vm].contains(page) by {
                    if post.view().iommu_private_pages[vm].contains(page) {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            post.budget.zones[zid].iommu_mem_set.regions.contains(stored)
                                && region_in_private_budget(zid, stored) && region_pages(
                                stored,
                            ).contains(page);
                        assert(stored != concrete);
                        assert(pre.budget.zones[zid].iommu_mem_set.regions.contains(stored));
                        if region_pages(concrete).contains(page) {
                            lemma_shared_page_implies_pmem_overlap(stored, concrete, page);
                            assert(!stored.spec_overlaps_pmem(concrete));
                            assert(false);
                        }
                    }
                    if target_private[vm].contains(page) {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            pre.budget.zones[zid].iommu_mem_set.regions.contains(stored)
                                && region_in_private_budget(zid, stored) && region_pages(
                                stored,
                            ).contains(page);
                        assert(stored != concrete);
                        assert(post.budget.zones[zid].iommu_mem_set.regions.contains(stored));
                    }
                }
            }
        }
    }
    assert(post.view().iommu_shared_pages =~= pre.view().iommu_shared_pages) by {
        assert forall|page: PhysPage|
            post.view().iommu_shared_pages.contains(page)
                <==> pre.view().iommu_shared_pages.contains(page) by {
            if pre.view().iommu_shared_pages.contains(page) {
                let zone_id = choose|zone_id: nat| #[trigger]
                    pre.budget.zone_ids.contains(zone_id) && zone_iommu_shared_pages(
                        pre.budget.zones[zone_id],
                    ).contains(page);
                if zone_id == zid {
                    let stored = choose|stored: MemoryRegion| #[trigger]
                        pre.budget.zones[zid].iommu_mem_set.regions.contains(stored)
                            && region_in_shared_budget(stored) && region_pages(stored).contains(
                            page,
                        );
                    assert(stored != concrete);
                }
            }
        }
    }
}

/// Proves the SoftwareView effect of removing one shared IOMMU region.
proof fn lemma_iommu_remove_shared_projection(
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
        region_in_shared_budget(concrete),
        post.budget.zone_ids == pre.budget.zone_ids,
        post.budget.zones == pre.budget.zones.insert(
            zid,
            pre.budget.zones[zid].iommu_remove_region(concrete),
        ),
    ensures
        SoftwareView::iommu_remove_shared_region_step(
            pre.view(),
            post.view(),
            region_to_abstract(zid, concrete),
        ),
{
    assert(pre.budget.inv_zones_wf());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_state_iommu_s2_remove(pre.budget, post.budget, zid, concrete);
    assert(post.view().all_vms =~= pre.view().all_vms);
    assert(post.view().s2_private_pages =~= pre.view().s2_private_pages);
    assert(post.view().s2_shared_pages =~= pre.view().s2_shared_pages);
    assert(post.view().s2_map =~= pre.view().s2_map);
    assert(post.view().iommu_s2_map =~= pre.view().iommu_s2_map.remove_keys(
        region_to_abstract(zid, concrete).entries().dom(),
    ));
    lemma_shared_region_not_private(zid, concrete);
    assert(post.view().iommu_private_pages =~= pre.view().iommu_private_pages) by {
        assert forall|vm: VmId| #[trigger]
            post.view().iommu_private_pages.contains_key(
                vm,
            ) implies post.view().iommu_private_pages[vm]
            =~= pre.view().iommu_private_pages[vm] by {
            if vm.0 == zid {
                assert forall|page: PhysPage|
                    post.view().iommu_private_pages[vm].contains(page)
                        <==> pre.view().iommu_private_pages[vm].contains(page) by {
                    if pre.view().iommu_private_pages[vm].contains(page) {
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            pre.budget.zones[zid].iommu_mem_set.regions.contains(stored)
                                && region_in_private_budget(zid, stored) && region_pages(
                                stored,
                            ).contains(page);
                        assert(stored != concrete);
                    }
                }
            }
        }
    }
    let target_shared = Set::new(
        |page: PhysPage|
            {
                let post_map = pre.view().iommu_s2_map.remove_keys(
                    region_to_abstract(zid, concrete).entries().dom(),
                );
                &&& pre.view().iommu_shared_pages.contains(page)
                &&& (!region_pages(concrete).contains(page) || exists|key: VmPageKey| #[trigger]
                    post_map.contains_key(key) && post_map[key].page == page)
            },
    );
    assert(post.budget.inv_zone_ids());
    assert(post.budget.inv_zones_wf());
    assert(post.budget.inv_iommu_regions_in_budget());
    private_pages_disjoint_from_shared();
    assert(post.view().iommu_shared_pages =~= target_shared) by {
        assert forall|page: PhysPage|
            post.view().iommu_shared_pages.contains(page) <==> target_shared.contains(page) by {
            if post.view().iommu_shared_pages.contains(page) {
                let zone_id = choose|zone_id: nat| #[trigger]
                    post.budget.zone_ids.contains(zone_id) && zone_iommu_shared_pages(
                        post.budget.zones[zone_id],
                    ).contains(page);
                let stored = choose|stored: MemoryRegion| #[trigger]
                    post.budget.zones[zone_id].iommu_mem_set.regions.contains(stored)
                        && region_in_shared_budget(stored) && region_pages(stored).contains(page);
                assert(pre.view().iommu_shared_pages.contains(page));
                if region_pages(concrete).contains(page) {
                    assert(post.budget.zones[zone_id].wf());
                    let i = choose|i: nat|
                        0 <= i < stored.pages && region_phys_page(stored, i) == page;
                    let key = VmPageKey { vm: VmId(zone_id), gpa: region_guest_page(stored, i) };
                    lemma_gpa_vaddr_roundtrip(stored, i);
                    lemma_region_phys_page_linear(stored, i);
                    assert(post.budget.zones[zone_id].iommu_mem_set.mappings.contains_pair(
                        stored.spec_page_vaddr(i),
                        stored.spec_frame(i),
                    ));
                    assert(post.view().iommu_s2_map.contains_key(key));
                    assert(post.view().iommu_s2_map[key].page == page);
                }
            }
            if target_shared.contains(page) {
                if !region_pages(concrete).contains(page) {
                    let zone_id = choose|zone_id: nat| #[trigger]
                        pre.budget.zone_ids.contains(zone_id) && zone_iommu_shared_pages(
                            pre.budget.zones[zone_id],
                        ).contains(page);
                    let stored = choose|stored: MemoryRegion| #[trigger]
                        pre.budget.zones[zone_id].iommu_mem_set.regions.contains(stored)
                            && region_in_shared_budget(stored) && region_pages(stored).contains(
                            page,
                        );
                    if zone_id == zid {
                        assert(stored != concrete);
                    }
                    assert(post.budget.zones[zone_id].iommu_mem_set.regions.contains(stored));
                } else {
                    let key = choose|key: VmPageKey| #[trigger]
                        post.view().iommu_s2_map.contains_key(key)
                            && post.view().iommu_s2_map[key].page == page;
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
                    if region_in_private_budget(zone_id, stored) {
                        assert(private_pages(zone_id).contains(page));
                        assert(shared_pages().contains(page));
                        assert(false);
                    }
                    assert(region_in_shared_budget(stored));
                    assert(post.view().iommu_shared_pages.contains(page));
                }
            }
        }
    }
    let abstract_region = region_to_abstract(zid, concrete);
    let expected_shared = Set::new(
        |page: PhysPage|
            {
                let post_map = pre.view().iommu_s2_map.remove_keys(abstract_region.entries().dom());
                &&& pre.view().iommu_shared_pages.contains(page)
                &&& (!abstract_region.pages().contains(page) || exists|key: VmPageKey| #[trigger]
                    post_map.contains_key(key) && post_map[key].page == page)
            },
    );
    assert(forall|page: PhysPage| target_shared.contains(page) <==> expected_shared.contains(page));
    assert(target_shared =~= expected_shared);
    assert(post.view().iommu_shared_pages == expected_shared);
    assert(post.view().iommu_private_pages == pre.view().iommu_private_pages);
    assert(post.view().all_vms == pre.view().all_vms);
    assert(post.view().s2_private_pages == pre.view().s2_private_pages);
    assert(post.view().s2_shared_pages == pre.view().s2_shared_pages);
    assert(post.view().s2_map == pre.view().s2_map);
    assert(post.view().iommu_s2_map == pre.view().iommu_s2_map.remove_keys(
        abstract_region.entries().dom(),
    ));
    assert(SoftwareView::iommu_remove_shared_region_step(pre.view(), post.view(), abstract_region));
}

// ---------------------------------------------------------------------------
// Concrete transition guards
// ---------------------------------------------------------------------------
/// A concrete CPU insertion that is virtually disjoint from the stored region
/// set is fresh in the flattened SoftwareView map.
proof fn lemma_cpu_insert_entries_fresh(spec: SoftwareSpec, zid: nat, concrete: MemoryRegion)
    requires
        spec.budget.invariant(),
        spec.budget.zones.contains_key(zid),
        concrete.spec_valid(),
        !spec.budget.zones[zid].cpu_mem_set.overlaps_vmem(concrete),
    ensures
        forall|key: VmPageKey| #[trigger]
            region_to_abstract(zid, concrete).entries().contains_key(key)
                ==> !spec.view().s2_map.contains_key(key),
{
    lemma_region_to_abstract_entries(zid, concrete);
    assert(spec.budget.inv_zones_wf());
    assert(spec.budget.zones[zid].wf());
    assert(spec.budget.zones[zid].cpu_mem_set.wf());
    assert forall|key: VmPageKey| #[trigger]
        region_to_abstract(zid, concrete).entries().contains_key(
            key,
        ) implies !spec.view().s2_map.contains_key(key) by {
        if spec.view().s2_map.contains_key(key) {
            assert(key.vm == VmId(zid));
            assert(spec.budget.zones[zid].cpu_mem_set.mappings.contains_key(vaddr_of_gpa(key.gpa)));
            let frame = spec.budget.zones[zid].cpu_mem_set.mappings[vaddr_of_gpa(key.gpa)];
            assert(spec.budget.zones[zid].cpu_mem_set.mappings.contains_pair(
                vaddr_of_gpa(key.gpa),
                frame,
            ));
            let (old, i) = choose|old: MemoryRegion, i: nat|
                spec.budget.zones[zid].cpu_mem_set.regions.contains(old) && 0 <= i < old.pages
                    && vaddr_of_gpa(key.gpa) == old.spec_page_vaddr(i) && frame == old.spec_frame(
                    i,
                );
            assert(old.spec_valid());
            lemma_gpa_vaddr_roundtrip(old, i);
            assert(region_guest_page(old, i) == key.gpa) by {
                lemma_vaddr_of_gpa_injective(region_guest_page(old, i), key.gpa);
            }
            assert(region_owns_gpa(old, key.gpa)) by {
                let witness = i;
            }
            assert(region_owns_gpa(concrete, key.gpa));
            lemma_shared_gpa_implies_vmem_overlap(old, concrete, key.gpa);
            assert(spec.budget.zones[zid].cpu_mem_set.overlaps_vmem(concrete));
        }
    }
}

/// IOMMU counterpart of [`lemma_cpu_insert_entries_fresh`].
proof fn lemma_iommu_insert_entries_fresh(spec: SoftwareSpec, zid: nat, concrete: MemoryRegion)
    requires
        spec.budget.invariant(),
        spec.budget.zones.contains_key(zid),
        concrete.spec_valid(),
        !spec.budget.zones[zid].iommu_mem_set.overlaps_vmem(concrete),
    ensures
        forall|key: VmPageKey| #[trigger]
            region_to_abstract(zid, concrete).entries().contains_key(key)
                ==> !spec.view().iommu_s2_map.contains_key(key),
{
    lemma_region_to_abstract_entries(zid, concrete);
    assert(spec.budget.inv_zones_wf());
    assert(spec.budget.zones[zid].wf());
    assert(spec.budget.zones[zid].iommu_mem_set.wf());
    assert forall|key: VmPageKey| #[trigger]
        region_to_abstract(zid, concrete).entries().contains_key(
            key,
        ) implies !spec.view().iommu_s2_map.contains_key(key) by {
        if spec.view().iommu_s2_map.contains_key(key) {
            assert(key.vm == VmId(zid));
            assert(spec.budget.zones[zid].iommu_mem_set.mappings.contains_key(
                vaddr_of_gpa(key.gpa),
            ));
            let frame = spec.budget.zones[zid].iommu_mem_set.mappings[vaddr_of_gpa(key.gpa)];
            assert(spec.budget.zones[zid].iommu_mem_set.mappings.contains_pair(
                vaddr_of_gpa(key.gpa),
                frame,
            ));
            let (old, i) = choose|old: MemoryRegion, i: nat|
                spec.budget.zones[zid].iommu_mem_set.regions.contains(old) && 0 <= i < old.pages
                    && vaddr_of_gpa(key.gpa) == old.spec_page_vaddr(i) && frame == old.spec_frame(
                    i,
                );
            assert(old.spec_valid());
            lemma_gpa_vaddr_roundtrip(old, i);
            assert(region_guest_page(old, i) == key.gpa) by {
                lemma_vaddr_of_gpa_injective(region_guest_page(old, i), key.gpa);
            }
            assert(region_owns_gpa(old, key.gpa)) by {
                let witness = i;
            }
            assert(region_owns_gpa(concrete, key.gpa));
            lemma_shared_gpa_implies_vmem_overlap(old, concrete, key.gpa);
            assert(spec.budget.zones[zid].iommu_mem_set.overlaps_vmem(concrete));
        }
    }
}

proof fn lemma_cpu_insert_private_enabled(spec: SoftwareSpec, zid: nat, concrete: MemoryRegion)
    requires
        spec.budget.invariant(),
        spec.budget.zones.contains_key(zid),
        concrete.spec_valid(),
        region_in_private_budget(zid, concrete),
        pmem_nonoverlap_with_private_regions(zid, spec.budget.zones[zid].cpu_mem_set, concrete),
        !spec.budget.zones[zid].cpu_mem_set.overlaps_vmem(concrete),
    ensures
        SoftwareView::cpu_insert_private_region_enabled(
            spec.view(),
            region_to_abstract(zid, concrete),
        ),
{
    let region = region_to_abstract(zid, concrete);
    lemma_budget_projection_wf(spec);
    assert(spec.budget.inv_zones_wf());
    assert(spec.budget.zones[zid].wf());
    assert(spec.budget.zones[zid].cpu_mem_set.wf());
    assert(concrete.spec_valid());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_cpu_insert_entries_fresh(spec, zid, concrete);
    private_pages_pairwise_disjoint();
    private_pages_disjoint_from_shared();
    assert(region.wf());
    assert(spec.view().all_vms.contains(region.vm));
    assert forall|page: PhysPage, vm: VmId| #[trigger]
        region.pages().contains(page) && #[trigger] spec.view().all_vms.contains(
            vm,
        ) implies !spec.view().s2_private_pages[vm].contains(page) by {
        if spec.view().s2_private_pages[vm].contains(page) {
            let old = choose|old: MemoryRegion| #[trigger]
                spec.budget.zones[vm.0].cpu_mem_set.regions.contains(old)
                    && region_in_private_budget(vm.0, old) && region_pages(old).contains(page);
            if vm.0 == zid {
                lemma_shared_page_implies_pmem_overlap(old, concrete, page);
            }
        }
    }
    assert(forall|page: PhysPage| #[trigger]
        region.pages().contains(page) ==> !spec.view().s2_shared_pages.contains(page));
    assert(forall|page: PhysPage, vm: VmId| #[trigger]
        region.pages().contains(page) && #[trigger] spec.view().all_vms.contains(vm) && vm
            != region.vm ==> !spec.view().iommu_private_pages[vm].contains(page));
    assert(forall|page: PhysPage| #[trigger]
        region.pages().contains(page) ==> !spec.view().iommu_shared_pages.contains(page));
}

proof fn lemma_cpu_insert_shared_enabled(spec: SoftwareSpec, zid: nat, concrete: MemoryRegion)
    requires
        spec.budget.invariant(),
        spec.budget.zones.contains_key(zid),
        concrete.spec_valid(),
        region_in_shared_budget(concrete),
        !spec.budget.zones[zid].cpu_mem_set.overlaps_vmem(concrete),
    ensures
        SoftwareView::cpu_insert_shared_region_enabled(
            spec.view(),
            region_to_abstract(zid, concrete),
        ),
{
    let region = region_to_abstract(zid, concrete);
    lemma_budget_projection_wf(spec);
    assert(spec.budget.inv_zones_wf());
    assert(spec.budget.zones[zid].wf());
    assert(spec.budget.zones[zid].cpu_mem_set.wf());
    assert(concrete.spec_valid());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_cpu_insert_entries_fresh(spec, zid, concrete);
    private_pages_disjoint_from_shared();
    assert(region.wf());
    assert(spec.view().all_vms.contains(region.vm));
    assert(forall|page: PhysPage, vm: VmId| #[trigger]
        region.pages().contains(page) && #[trigger] spec.view().all_vms.contains(vm)
            ==> !spec.view().s2_private_pages[vm].contains(page));
}

proof fn lemma_iommu_insert_private_enabled(spec: SoftwareSpec, zid: nat, concrete: MemoryRegion)
    requires
        spec.budget.invariant(),
        spec.budget.zones.contains_key(zid),
        concrete.spec_valid(),
        region_in_private_budget(zid, concrete),
        pmem_nonoverlap_with_private_regions(zid, spec.budget.zones[zid].iommu_mem_set, concrete),
        !spec.budget.zones[zid].iommu_mem_set.overlaps_vmem(concrete),
    ensures
        SoftwareView::iommu_insert_private_region_enabled(
            spec.view(),
            region_to_abstract(zid, concrete),
        ),
{
    let region = region_to_abstract(zid, concrete);
    lemma_budget_projection_wf(spec);
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_iommu_insert_entries_fresh(spec, zid, concrete);
    private_pages_pairwise_disjoint();
    private_pages_disjoint_from_shared();
    assert(region.wf());
    assert(spec.view().all_vms.contains(region.vm));
    assert forall|page: PhysPage, vm: VmId| #[trigger]
        region.pages().contains(page) && #[trigger] spec.view().all_vms.contains(
            vm,
        ) implies !spec.view().iommu_private_pages[vm].contains(page) by {
        if spec.view().iommu_private_pages[vm].contains(page) {
            let old = choose|old: MemoryRegion| #[trigger]
                spec.budget.zones[vm.0].iommu_mem_set.regions.contains(old)
                    && region_in_private_budget(vm.0, old) && region_pages(old).contains(page);
            if vm.0 == zid {
                lemma_shared_page_implies_pmem_overlap(old, concrete, page);
            }
        }
    }
    assert(forall|page: PhysPage, vm: VmId| #[trigger]
        region.pages().contains(page) && #[trigger] spec.view().all_vms.contains(vm) && vm
            != region.vm ==> !spec.view().s2_private_pages[vm].contains(page));
    assert(forall|page: PhysPage| #[trigger]
        region.pages().contains(page) ==> !spec.view().iommu_shared_pages.contains(page));
}

proof fn lemma_iommu_insert_shared_enabled(spec: SoftwareSpec, zid: nat, concrete: MemoryRegion)
    requires
        spec.budget.invariant(),
        spec.budget.zones.contains_key(zid),
        concrete.spec_valid(),
        region_in_shared_budget(concrete),
        !spec.budget.zones[zid].iommu_mem_set.overlaps_vmem(concrete),
    ensures
        SoftwareView::iommu_insert_shared_region_enabled(
            spec.view(),
            region_to_abstract(zid, concrete),
        ),
{
    let region = region_to_abstract(zid, concrete);
    lemma_budget_projection_wf(spec);
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_iommu_insert_entries_fresh(spec, zid, concrete);
    private_pages_disjoint_from_shared();
    assert(region.wf());
    assert(spec.view().all_vms.contains(region.vm));
    assert(forall|page: PhysPage, vm: VmId| #[trigger]
        region.pages().contains(page) && #[trigger] spec.view().all_vms.contains(vm)
            ==> !spec.view().s2_private_pages[vm].contains(page)
            && !spec.view().iommu_private_pages[vm].contains(page));
}

proof fn lemma_cpu_remove_private_enabled(spec: SoftwareSpec, zid: nat, concrete: MemoryRegion)
    requires
        spec.budget.invariant(),
        spec.budget.zones.contains_key(zid),
        spec.budget.zones[zid].cpu_mem_set.regions.contains(concrete),
        region_in_private_budget(zid, concrete),
    ensures
        SoftwareView::cpu_remove_private_region_enabled(
            spec.view(),
            region_to_abstract(zid, concrete),
        ),
{
    let region = region_to_abstract(zid, concrete);
    lemma_budget_projection_wf(spec);
    assert(spec.budget.inv_zones_wf());
    assert(spec.budget.zones[zid].wf());
    assert(spec.budget.zones[zid].cpu_mem_set.wf());
    assert(concrete.spec_valid());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_region_in_memory_set_maps_entries(zid, spec.budget.zones[zid].cpu_mem_set, concrete);
    private_pages_pairwise_disjoint();
    private_pages_disjoint_from_shared();
    assert(region.wf());
    assert(spec.view().all_vms.contains(region.vm));
    assert(forall|page: PhysPage| #[trigger]
        region.pages().contains(page) ==> spec.view().s2_private_pages[region.vm].contains(page));
    assert(abstract_region_installed(spec.view().s2_map, region));
    assert forall|key: VmPageKey| #[trigger]
        spec.view().s2_map.contains_key(key) && !region.entries().contains_key(
            key,
        ) implies !region.pages().contains(spec.view().s2_map[key].page) by {
        if region.pages().contains(spec.view().s2_map[key].page) {
            let page = spec.view().s2_map[key].page;
            assert(spec.budget.zones.contains_key(key.vm.0));
            let mem_set = spec.budget.zones[key.vm.0].cpu_mem_set;
            assert(spec.budget.zones[key.vm.0].wf());
            assert(mem_set.wf());
            let vaddr = vaddr_of_gpa(key.gpa);
            assert(mem_set.mappings.contains_key(vaddr));
            let frame = mem_set.mappings[vaddr];
            assert(mem_set.mappings.contains_pair(vaddr, frame));
            assert(frame_to_s2(frame) == spec.view().s2_map[key]);
            assert(frame_phys_page(frame) == page);
            let (old, i) = choose|old: MemoryRegion, i: nat|
                mem_set.regions.contains(old) && 0 <= i < old.pages && vaddr == old.spec_page_vaddr(
                    i,
                ) && frame == old.spec_frame(i);
            assert(old.spec_valid());
            lemma_region_phys_page_linear(old, i);
            assert(region_pages(old).contains(page));
            assert(region_in_budget(key.vm.0, old));
            if region_in_private_budget(key.vm.0, old) {
                if key.vm.0 == zid {
                    if old == concrete {
                        lemma_gpa_vaddr_roundtrip(old, i);
                        assert(region_guest_page(old, i) == key.gpa) by {
                            lemma_vaddr_of_gpa_injective(region_guest_page(old, i), key.gpa);
                        }
                        assert(region_owns_gpa(concrete, key.gpa)) by {
                            let witness = i;
                        }
                        assert(region.entries().contains_key(key));
                    } else {
                        lemma_shared_page_implies_pmem_overlap(old, concrete, page);
                    }
                }
            }
        }
    }
    assert(forall|page: PhysPage| #[trigger]
        region.pages().contains(page) ==> !spec.view().s2_shared_pages.contains(page));
}

proof fn lemma_cpu_remove_shared_enabled(spec: SoftwareSpec, zid: nat, concrete: MemoryRegion)
    requires
        spec.budget.invariant(),
        spec.budget.zones.contains_key(zid),
        spec.budget.zones[zid].cpu_mem_set.regions.contains(concrete),
        region_in_shared_budget(concrete),
    ensures
        SoftwareView::cpu_remove_shared_region_enabled(
            spec.view(),
            region_to_abstract(zid, concrete),
        ),
{
    let region = region_to_abstract(zid, concrete);
    lemma_budget_projection_wf(spec);
    assert(spec.budget.inv_zones_wf());
    assert(spec.budget.zones[zid].wf());
    assert(spec.budget.zones[zid].cpu_mem_set.wf());
    assert(concrete.spec_valid());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_region_in_memory_set_maps_entries(zid, spec.budget.zones[zid].cpu_mem_set, concrete);
    assert(region.wf());
    assert(spec.view().all_vms.contains(region.vm));
    assert(forall|page: PhysPage| #[trigger]
        region.pages().contains(page) ==> spec.view().s2_shared_pages.contains(page));
    assert(abstract_region_installed(spec.view().s2_map, region));
}

proof fn lemma_iommu_remove_private_enabled(spec: SoftwareSpec, zid: nat, concrete: MemoryRegion)
    requires
        spec.budget.invariant(),
        spec.budget.zones.contains_key(zid),
        spec.budget.zones[zid].iommu_mem_set.regions.contains(concrete),
        region_in_private_budget(zid, concrete),
    ensures
        SoftwareView::iommu_remove_private_region_enabled(
            spec.view(),
            region_to_abstract(zid, concrete),
        ),
{
    let region = region_to_abstract(zid, concrete);
    lemma_budget_projection_wf(spec);
    assert(spec.budget.inv_zones_wf());
    assert(spec.budget.zones[zid].wf());
    assert(spec.budget.zones[zid].iommu_mem_set.wf());
    assert(concrete.spec_valid());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_region_in_memory_set_maps_entries(zid, spec.budget.zones[zid].iommu_mem_set, concrete);
    private_pages_pairwise_disjoint();
    private_pages_disjoint_from_shared();
    assert(region.wf());
    assert(spec.view().all_vms.contains(region.vm));
    assert(forall|page: PhysPage| #[trigger]
        region.pages().contains(page) ==> spec.view().iommu_private_pages[region.vm].contains(
            page,
        ));
    assert(abstract_region_installed(spec.view().iommu_s2_map, region));
    assert forall|key: VmPageKey| #[trigger]
        spec.view().iommu_s2_map.contains_key(key) && !region.entries().contains_key(
            key,
        ) implies !region.pages().contains(spec.view().iommu_s2_map[key].page) by {
        if region.pages().contains(spec.view().iommu_s2_map[key].page) {
            let page = spec.view().iommu_s2_map[key].page;
            assert(spec.budget.zones.contains_key(key.vm.0));
            let mem_set = spec.budget.zones[key.vm.0].iommu_mem_set;
            assert(spec.budget.zones[key.vm.0].wf());
            assert(mem_set.wf());
            let vaddr = vaddr_of_gpa(key.gpa);
            assert(mem_set.mappings.contains_key(vaddr));
            let frame = mem_set.mappings[vaddr];
            assert(mem_set.mappings.contains_pair(vaddr, frame));
            assert(frame_to_s2(frame) == spec.view().iommu_s2_map[key]);
            assert(frame_phys_page(frame) == page);
            let (old, i) = choose|old: MemoryRegion, i: nat|
                mem_set.regions.contains(old) && 0 <= i < old.pages && vaddr == old.spec_page_vaddr(
                    i,
                ) && frame == old.spec_frame(i);
            assert(old.spec_valid());
            lemma_region_phys_page_linear(old, i);
            assert(region_pages(old).contains(page));
            assert(region_in_budget(key.vm.0, old));
            if region_in_private_budget(key.vm.0, old) {
                if key.vm.0 == zid {
                    if old == concrete {
                        lemma_gpa_vaddr_roundtrip(old, i);
                        assert(region_guest_page(old, i) == key.gpa) by {
                            lemma_vaddr_of_gpa_injective(region_guest_page(old, i), key.gpa);
                        }
                        assert(region_owns_gpa(concrete, key.gpa)) by {
                            let witness = i;
                        }
                        assert(region.entries().contains_key(key));
                    } else {
                        lemma_shared_page_implies_pmem_overlap(old, concrete, page);
                    }
                }
            }
        }
    }
}

proof fn lemma_iommu_remove_shared_enabled(spec: SoftwareSpec, zid: nat, concrete: MemoryRegion)
    requires
        spec.budget.invariant(),
        spec.budget.zones.contains_key(zid),
        spec.budget.zones[zid].iommu_mem_set.regions.contains(concrete),
        region_in_shared_budget(concrete),
    ensures
        SoftwareView::iommu_remove_shared_region_enabled(
            spec.view(),
            region_to_abstract(zid, concrete),
        ),
{
    let region = region_to_abstract(zid, concrete);
    lemma_budget_projection_wf(spec);
    assert(spec.budget.inv_zones_wf());
    assert(spec.budget.zones[zid].wf());
    assert(spec.budget.zones[zid].iommu_mem_set.wf());
    assert(concrete.spec_valid());
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_region_in_memory_set_maps_entries(zid, spec.budget.zones[zid].iommu_mem_set, concrete);
    assert(region.wf());
    assert(spec.view().all_vms.contains(region.vm));
    assert(forall|page: PhysPage| #[trigger]
        region.pages().contains(page) ==> spec.view().iommu_shared_pages.contains(page));
    assert(abstract_region_installed(spec.view().iommu_s2_map, region));
}

/// Refines one concrete CPU-region removal to the corresponding policy-neutral
/// private or shared removal edge.
proof fn lemma_cpu_remove_region_refines(
    pre: SoftwareSpec,
    zid: nat,
    concrete: MemoryRegion,
) -> (result: (SoftwareSpec, Seq<SoftwareOp>))
    requires
        pre.budget.invariant(),
        pre.budget.zones.contains_key(zid),
        pre.budget.zones[zid].cpu_mem_set.regions.contains(concrete),
    ensures
        result.0.budget.invariant(),
        BudgetSpec::State::next_by(
            pre.budget,
            result.0.budget,
            BudgetSpec::Step::cpu_remove_region(zid, concrete),
        ),
        result.0.budget.zone_ids == pre.budget.zone_ids,
        result.0.budget.zones == pre.budget.zones.insert(
            zid,
            pre.budget.zones[zid].cpu_remove_region(concrete),
        ),
        run_software_ops(pre.view(), result.0.view(), result.1),
{
    assert(pre.budget.zones[zid].wf());
    let region = region_to_abstract(zid, concrete);
    let post = SoftwareSpec {
        budget: BudgetSpec::take_step::cpu_remove_region(pre.budget, zid, concrete),
    };
    assert(post.budget.zones == pre.budget.zones.insert(
        zid,
        pre.budget.zones[zid].cpu_remove_region(concrete),
    ));
    reveal(BudgetSpec::State::next_by);
    if region_in_private_budget(zid, concrete) {
        lemma_cpu_remove_private_enabled(pre, zid, concrete);
        lemma_cpu_remove_private_projection(pre, post, zid, concrete);
        let op = SoftwareOp::CpuRemovePrivateRegion(region);
        lemma_run_software_ops_single(pre.view(), post.view(), op);
        (post, seq![op])
    } else {
        lemma_cpu_remove_shared_enabled(pre, zid, concrete);
        lemma_cpu_remove_shared_projection(pre, post, zid, concrete);
        let op = SoftwareOp::CpuRemoveSharedRegion(region);
        lemma_run_software_ops_single(pre.view(), post.view(), op);
        (post, seq![op])
    }
}

/// IOMMU counterpart of [`lemma_cpu_remove_region_refines`].
proof fn lemma_iommu_remove_region_refines(
    pre: SoftwareSpec,
    zid: nat,
    concrete: MemoryRegion,
) -> (result: (SoftwareSpec, Seq<SoftwareOp>))
    requires
        pre.budget.invariant(),
        pre.budget.zones.contains_key(zid),
        pre.budget.zones[zid].iommu_mem_set.regions.contains(concrete),
    ensures
        result.0.budget.invariant(),
        BudgetSpec::State::next_by(
            pre.budget,
            result.0.budget,
            BudgetSpec::Step::iommu_remove_region(zid, concrete),
        ),
        result.0.budget.zone_ids == pre.budget.zone_ids,
        result.0.budget.zones == pre.budget.zones.insert(
            zid,
            pre.budget.zones[zid].iommu_remove_region(concrete),
        ),
        run_software_ops(pre.view(), result.0.view(), result.1),
{
    assert(pre.budget.zones[zid].wf());
    let region = region_to_abstract(zid, concrete);
    let post = SoftwareSpec {
        budget: BudgetSpec::take_step::iommu_remove_region(pre.budget, zid, concrete),
    };
    assert(post.budget.zones == pre.budget.zones.insert(
        zid,
        pre.budget.zones[zid].iommu_remove_region(concrete),
    ));
    reveal(BudgetSpec::State::next_by);
    if region_in_private_budget(zid, concrete) {
        lemma_iommu_remove_private_enabled(pre, zid, concrete);
        lemma_iommu_remove_private_projection(pre, post, zid, concrete);
        let op = SoftwareOp::IommuRemovePrivateRegion(region);
        lemma_run_software_ops_single(pre.view(), post.view(), op);
        (post, seq![op])
    } else {
        lemma_iommu_remove_shared_enabled(pre, zid, concrete);
        lemma_iommu_remove_shared_projection(pre, post, zid, concrete);
        let op = SoftwareOp::IommuRemoveSharedRegion(region);
        lemma_run_software_ops_single(pre.view(), post.view(), op);
        (post, seq![op])
    }
}

/// Refines an atomic CPU clear to one abstract removal per stored region.
proof fn lemma_cpu_clear_refines(pre: SoftwareSpec, zid: nat) -> (result: (
    SoftwareSpec,
    Seq<SoftwareOp>,
))
    requires
        pre.budget.invariant(),
        pre.budget.zones.contains_key(zid),
    ensures
        result.0.budget.invariant(),
        result.0.budget.zone_ids == pre.budget.zone_ids,
        result.0.budget.zones == pre.budget.zones.insert(zid, pre.budget.zones[zid].cpu_clear()),
        run_software_ops(pre.view(), result.0.view(), result.1),
    decreases pre.budget.zones[zid].cpu_mem_set.regions.len(),
{
    let regions = pre.budget.zones[zid].cpu_mem_set.regions;
    if regions.len() == 0 {
        regions.lemma_len0_is_empty();
        let mem_set = pre.budget.zones[zid].cpu_mem_set;
        assert(pre.budget.zones[zid].wf());
        assert(mem_set.mappings =~= Map::<SpecVAddr, SpecFrame>::empty()) by {
            assert forall|vaddr: SpecVAddr| !mem_set.mappings.contains_key(vaddr) by {
                if mem_set.mappings.contains_key(vaddr) {
                    let frame = mem_set.mappings[vaddr];
                    assert(mem_set.mappings.contains_pair(vaddr, frame));
                    let (old, i) = choose|old: MemoryRegion, i: nat|
                        mem_set.regions.contains(old) && 0 <= i < old.pages && vaddr
                            == old.spec_page_vaddr(i) && frame == old.spec_frame(i);
                    assert(false);
                }
            }
        }
        (pre, Seq::empty())
    } else {
        let concrete = regions.choose();
        let first = lemma_cpu_remove_region_refines(pre, zid, concrete);
        let middle = first.0;
        let first_ops = first.1;
        vstd::set::axiom_set_remove_len(regions, concrete);
        let rest = lemma_cpu_clear_refines(middle, zid);
        let post = rest.0;
        let rest_ops = rest.1;
        lemma_run_software_ops_concat(pre.view(), middle.view(), post.view(), first_ops, rest_ops);
        (post, first_ops + rest_ops)
    }
}

/// Refines an atomic IOMMU clear to one abstract removal per stored region.
proof fn lemma_iommu_clear_refines(pre: SoftwareSpec, zid: nat) -> (result: (
    SoftwareSpec,
    Seq<SoftwareOp>,
))
    requires
        pre.budget.invariant(),
        pre.budget.zones.contains_key(zid),
    ensures
        result.0.budget.invariant(),
        result.0.budget.zone_ids == pre.budget.zone_ids,
        result.0.budget.zones == pre.budget.zones.insert(zid, pre.budget.zones[zid].iommu_clear()),
        run_software_ops(pre.view(), result.0.view(), result.1),
    decreases pre.budget.zones[zid].iommu_mem_set.regions.len(),
{
    let regions = pre.budget.zones[zid].iommu_mem_set.regions;
    if regions.len() == 0 {
        regions.lemma_len0_is_empty();
        let mem_set = pre.budget.zones[zid].iommu_mem_set;
        assert(pre.budget.zones[zid].wf());
        assert(mem_set.mappings =~= Map::<SpecVAddr, SpecFrame>::empty()) by {
            assert forall|vaddr: SpecVAddr| !mem_set.mappings.contains_key(vaddr) by {
                if mem_set.mappings.contains_key(vaddr) {
                    let frame = mem_set.mappings[vaddr];
                    assert(mem_set.mappings.contains_pair(vaddr, frame));
                    let (old, i) = choose|old: MemoryRegion, i: nat|
                        mem_set.regions.contains(old) && 0 <= i < old.pages && vaddr
                            == old.spec_page_vaddr(i) && frame == old.spec_frame(i);
                    assert(false);
                }
            }
        }
        (pre, Seq::empty())
    } else {
        let concrete = regions.choose();
        let first = lemma_iommu_remove_region_refines(pre, zid, concrete);
        let middle = first.0;
        let first_ops = first.1;
        vstd::set::axiom_set_remove_len(regions, concrete);
        let rest = lemma_iommu_clear_refines(middle, zid);
        let post = rest.0;
        let rest_ops = rest.1;
        lemma_run_software_ops_concat(pre.view(), middle.view(), post.view(), first_ops, rest_ops);
        (post, first_ops + rest_ops)
    }
}

// ---------------------------------------------------------------------------
// Relational BudgetSpec refinement
// ---------------------------------------------------------------------------
proof fn lemma_add_zone_step_refines(pre: SoftwareSpec, post: SoftwareSpec, zid: nat) -> (ops: Seq<
    SoftwareOp,
>)
    requires
        pre.budget.invariant(),
        BudgetSpec::State::next_by(pre.budget, post.budget, BudgetSpec::Step::add_zone(zid)),
    ensures
        post.budget.invariant(),
        run_software_ops(pre.view(), post.view(), ops),
{
    reveal(BudgetSpec::State::next_by);
    let vm = VmId(zid);
    let empty_zone = GhostZone {
        cpu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
        iommu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
    };
    assert(post.budget.zone_ids == pre.budget.zone_ids.insert(zid));
    assert(post.budget.zones == pre.budget.zones.insert(zid, empty_zone));
    assert(post.view().all_vms =~= pre.view().all_vms.insert(vm));
    assert(post.view().s2_private_pages =~= pre.view().s2_private_pages.insert(vm, Set::empty()))
        by {
        assert(forall|other: VmId| #[trigger]
            post.view().s2_private_pages.contains_key(other)
                <==> pre.view().s2_private_pages.insert(vm, Set::empty()).contains_key(other));
        assert(forall|other: VmId| #[trigger]
            post.view().s2_private_pages.contains_key(other) ==> post.view().s2_private_pages[other]
                == pre.view().s2_private_pages.insert(vm, Set::empty())[other]);
    }
    assert(post.view().s2_shared_pages =~= pre.view().s2_shared_pages) by {
        assert forall|page: PhysPage|
            post.view().s2_shared_pages.contains(page) <==> pre.view().s2_shared_pages.contains(
                page,
            ) by {
            if post.view().s2_shared_pages.contains(page) {
                let other = choose|other: nat| #[trigger]
                    post.budget.zone_ids.contains(other) && zone_s2_shared_pages(
                        post.budget.zones[other],
                    ).contains(page);
                assert(other != zid);
            }
            if pre.view().s2_shared_pages.contains(page) {
                let other = choose|other: nat| #[trigger]
                    pre.budget.zone_ids.contains(other) && zone_s2_shared_pages(
                        pre.budget.zones[other],
                    ).contains(page);
                assert(post.budget.zone_ids.contains(other));
                assert(post.budget.zones[other] == pre.budget.zones[other]);
                assert(post.view().s2_shared_pages.contains(page));
            }
        }
    }
    assert(post.view().s2_map =~= pre.view().s2_map);
    assert(post.view().iommu_private_pages =~= pre.view().iommu_private_pages.insert(
        vm,
        Set::empty(),
    )) by {
        assert(forall|other: VmId| #[trigger]
            post.view().iommu_private_pages.contains_key(other)
                <==> pre.view().iommu_private_pages.insert(vm, Set::empty()).contains_key(other));
        assert(forall|other: VmId| #[trigger]
            post.view().iommu_private_pages.contains_key(other)
                ==> post.view().iommu_private_pages[other] == pre.view().iommu_private_pages.insert(
                vm,
                Set::empty(),
            )[other]);
    }
    assert(post.view().iommu_shared_pages =~= pre.view().iommu_shared_pages) by {
        assert forall|page: PhysPage|
            post.view().iommu_shared_pages.contains(page)
                <==> pre.view().iommu_shared_pages.contains(page) by {
            if post.view().iommu_shared_pages.contains(page) {
                let other = choose|other: nat| #[trigger]
                    post.budget.zone_ids.contains(other) && zone_iommu_shared_pages(
                        post.budget.zones[other],
                    ).contains(page);
                assert(other != zid);
            }
            if pre.view().iommu_shared_pages.contains(page) {
                let other = choose|other: nat| #[trigger]
                    pre.budget.zone_ids.contains(other) && zone_iommu_shared_pages(
                        pre.budget.zones[other],
                    ).contains(page);
                assert(post.budget.zone_ids.contains(other));
                assert(post.budget.zones[other] == pre.budget.zones[other]);
                assert(post.view().iommu_shared_pages.contains(page));
            }
        }
    }
    assert(post.view().iommu_s2_map =~= pre.view().iommu_s2_map);
    let op = SoftwareOp::AddVm(vm);
    lemma_run_software_ops_single(pre.view(), post.view(), op);
    seq![op]
}

proof fn lemma_cpu_insert_region_step_refines(
    pre: SoftwareSpec,
    post: SoftwareSpec,
    zid: nat,
    concrete: MemoryRegion,
) -> (ops: Seq<SoftwareOp>)
    requires
        pre.budget.invariant(),
        BudgetSpec::State::next_by(
            pre.budget,
            post.budget,
            BudgetSpec::Step::cpu_insert_region(zid, concrete),
        ),
    ensures
        post.budget.invariant(),
        run_software_ops(pre.view(), post.view(), ops),
{
    reveal(BudgetSpec::State::next_by);
    let generated = SoftwareSpec {
        budget: BudgetSpec::take_step::cpu_insert_region(pre.budget, zid, concrete),
    };
    assert(generated.budget.zones == pre.budget.zones.insert(
        zid,
        pre.budget.zones[zid].cpu_insert_region(concrete),
    ));
    let region = region_to_abstract(zid, concrete);
    if region_in_private_budget(zid, concrete) {
        lemma_cpu_insert_private_enabled(pre, zid, concrete);
        lemma_cpu_insert_private_projection(pre, post, zid, concrete);
        let op = SoftwareOp::CpuInsertPrivateRegion(region);
        lemma_run_software_ops_single(pre.view(), post.view(), op);
        seq![op]
    } else {
        lemma_cpu_insert_shared_enabled(pre, zid, concrete);
        lemma_cpu_insert_shared_projection(pre, post, zid, concrete);
        let op = SoftwareOp::CpuInsertSharedRegion(region);
        lemma_run_software_ops_single(pre.view(), post.view(), op);
        seq![op]
    }
}

proof fn lemma_cpu_remove_region_step_refines(
    pre: SoftwareSpec,
    post: SoftwareSpec,
    zid: nat,
    concrete: MemoryRegion,
) -> (ops: Seq<SoftwareOp>)
    requires
        pre.budget.invariant(),
        BudgetSpec::State::next_by(
            pre.budget,
            post.budget,
            BudgetSpec::Step::cpu_remove_region(zid, concrete),
        ),
    ensures
        post.budget.invariant(),
        run_software_ops(pre.view(), post.view(), ops),
{
    reveal(BudgetSpec::State::next_by);
    let generated = lemma_cpu_remove_region_refines(pre, zid, concrete);
    generated.1
}

proof fn lemma_cpu_clear_step_refines(pre: SoftwareSpec, post: SoftwareSpec, zid: nat) -> (ops: Seq<
    SoftwareOp,
>)
    requires
        pre.budget.invariant(),
        BudgetSpec::State::next_by(pre.budget, post.budget, BudgetSpec::Step::cpu_clear(zid)),
    ensures
        post.budget.invariant(),
        run_software_ops(pre.view(), post.view(), ops),
{
    reveal(BudgetSpec::State::next_by);
    let trace = lemma_cpu_clear_refines(pre, zid);
    let generated = SoftwareSpec { budget: BudgetSpec::take_step::cpu_clear(pre.budget, zid) };
    assert(trace.0.budget == generated.budget);
    trace.1
}

proof fn lemma_iommu_insert_region_step_refines(
    pre: SoftwareSpec,
    post: SoftwareSpec,
    zid: nat,
    concrete: MemoryRegion,
) -> (ops: Seq<SoftwareOp>)
    requires
        pre.budget.invariant(),
        BudgetSpec::State::next_by(
            pre.budget,
            post.budget,
            BudgetSpec::Step::iommu_insert_region(zid, concrete),
        ),
    ensures
        post.budget.invariant(),
        run_software_ops(pre.view(), post.view(), ops),
{
    reveal(BudgetSpec::State::next_by);
    let generated = SoftwareSpec {
        budget: BudgetSpec::take_step::iommu_insert_region(pre.budget, zid, concrete),
    };
    assert(generated.budget.zones == pre.budget.zones.insert(
        zid,
        pre.budget.zones[zid].iommu_insert_region(concrete),
    ));
    let region = region_to_abstract(zid, concrete);
    if region_in_private_budget(zid, concrete) {
        lemma_iommu_insert_private_enabled(pre, zid, concrete);
        lemma_iommu_insert_private_projection(pre, post, zid, concrete);
        let op = SoftwareOp::IommuInsertPrivateRegion(region);
        lemma_run_software_ops_single(pre.view(), post.view(), op);
        seq![op]
    } else {
        lemma_iommu_insert_shared_enabled(pre, zid, concrete);
        lemma_iommu_insert_shared_projection(pre, post, zid, concrete);
        let op = SoftwareOp::IommuInsertSharedRegion(region);
        lemma_run_software_ops_single(pre.view(), post.view(), op);
        seq![op]
    }
}

proof fn lemma_iommu_remove_region_step_refines(
    pre: SoftwareSpec,
    post: SoftwareSpec,
    zid: nat,
    concrete: MemoryRegion,
) -> (ops: Seq<SoftwareOp>)
    requires
        pre.budget.invariant(),
        BudgetSpec::State::next_by(
            pre.budget,
            post.budget,
            BudgetSpec::Step::iommu_remove_region(zid, concrete),
        ),
    ensures
        post.budget.invariant(),
        run_software_ops(pre.view(), post.view(), ops),
{
    reveal(BudgetSpec::State::next_by);
    let generated = lemma_iommu_remove_region_refines(pre, zid, concrete);
    generated.1
}

proof fn lemma_iommu_clear_step_refines(pre: SoftwareSpec, post: SoftwareSpec, zid: nat) -> (ops:
    Seq<SoftwareOp>)
    requires
        pre.budget.invariant(),
        BudgetSpec::State::next_by(pre.budget, post.budget, BudgetSpec::Step::iommu_clear(zid)),
    ensures
        post.budget.invariant(),
        run_software_ops(pre.view(), post.view(), ops),
{
    reveal(BudgetSpec::State::next_by);
    let trace = lemma_iommu_clear_refines(pre, zid);
    let generated = SoftwareSpec { budget: BudgetSpec::take_step::iommu_clear(pre.budget, zid) };
    assert(trace.0.budget == generated.budget);
    trace.1
}

proof fn lemma_remove_zone_step_refines(pre: SoftwareSpec, post: SoftwareSpec, zid: nat) -> (ops:
    Seq<SoftwareOp>)
    requires
        pre.budget.invariant(),
        BudgetSpec::State::next_by(pre.budget, post.budget, BudgetSpec::Step::remove_zone(zid)),
    ensures
        post.budget.invariant(),
        run_software_ops(pre.view(), post.view(), ops),
{
    reveal(BudgetSpec::State::next_by);
    let cpu = lemma_cpu_clear_refines(pre, zid);
    let after_cpu = cpu.0;
    let iommu = lemma_iommu_clear_refines(after_cpu, zid);
    let cleared = iommu.0;
    let vm = VmId(zid);
    assert(cleared.budget.zones[zid].cpu_mem_set.regions == Set::<MemoryRegion>::empty());
    assert(cleared.budget.zones[zid].cpu_mem_set.mappings == Map::<SpecVAddr, SpecFrame>::empty());
    assert(cleared.budget.zones[zid].iommu_mem_set.regions == Set::<MemoryRegion>::empty());
    assert(cleared.budget.zones[zid].iommu_mem_set.mappings == Map::<
        SpecVAddr,
        SpecFrame,
    >::empty());
    assert(SoftwareView::remove_vm_enabled(cleared.view(), vm)) by {
        assert(cleared.view().all_vms.contains(vm));
        assert(cleared.view().s2_private_pages[vm] == Set::<PhysPage>::empty());
        assert(cleared.view().iommu_private_pages[vm] == Set::<PhysPage>::empty());
        assert(forall|key: VmPageKey| #[trigger]
            cleared.view().s2_map.contains_key(key) ==> key.vm != vm);
        assert(forall|key: VmPageKey| #[trigger]
            cleared.view().iommu_s2_map.contains_key(key) ==> key.vm != vm);
    }
    let removed = SoftwareSpec { budget: BudgetSpec::take_step::remove_zone(cleared.budget, zid) };
    assert(removed.budget.zone_ids == cleared.budget.zone_ids.remove(zid));
    assert(removed.budget.zones == cleared.budget.zones.remove(zid));
    assert(removed.view().all_vms =~= cleared.view().all_vms.remove(vm));
    assert(removed.view().s2_private_pages =~= cleared.view().s2_private_pages.remove(vm));
    assert(removed.view().s2_shared_pages =~= cleared.view().s2_shared_pages) by {
        assert forall|page: PhysPage|
            removed.view().s2_shared_pages.contains(page)
                <==> cleared.view().s2_shared_pages.contains(page) by {
            if cleared.view().s2_shared_pages.contains(page) {
                let other = choose|other: nat| #[trigger]
                    cleared.budget.zone_ids.contains(other) && zone_s2_shared_pages(
                        cleared.budget.zones[other],
                    ).contains(page);
                assert(other != zid);
            }
        }
    }
    assert(removed.view().s2_map =~= cleared.view().s2_map);
    assert(removed.view().iommu_private_pages =~= cleared.view().iommu_private_pages.remove(vm));
    assert(removed.view().iommu_shared_pages =~= cleared.view().iommu_shared_pages) by {
        assert forall|page: PhysPage|
            removed.view().iommu_shared_pages.contains(page)
                <==> cleared.view().iommu_shared_pages.contains(page) by {
            if cleared.view().iommu_shared_pages.contains(page) {
                let other = choose|other: nat| #[trigger]
                    cleared.budget.zone_ids.contains(other) && zone_iommu_shared_pages(
                        cleared.budget.zones[other],
                    ).contains(page);
                assert(other != zid);
            }
        }
    }
    assert(removed.view().iommu_s2_map =~= cleared.view().iommu_s2_map);
    let remove_op = SoftwareOp::RemoveVm(vm);
    lemma_run_software_ops_single(cleared.view(), removed.view(), remove_op);
    lemma_run_software_ops_concat(pre.view(), after_cpu.view(), cleared.view(), cpu.1, iommu.1);
    lemma_run_software_ops_concat(
        pre.view(),
        cleared.view(),
        removed.view(),
        cpu.1 + iommu.1,
        seq![remove_op],
    );
    let generated = SoftwareSpec { budget: BudgetSpec::take_step::remove_zone(pre.budget, zid) };
    assert(cleared.budget.zone_ids == pre.budget.zone_ids);
    assert(cleared.budget.zones.remove(zid) =~= pre.budget.zones.remove(zid)) by {
        assert(forall|other: nat| #[trigger]
            cleared.budget.zones.remove(zid).contains_key(other) == pre.budget.zones.remove(
                zid,
            ).contains_key(other));
        assert(forall|other: nat| #[trigger]
            cleared.budget.zones.remove(zid).contains_key(other) ==> cleared.budget.zones.remove(
                zid,
            )[other] == pre.budget.zones.remove(zid)[other]);
    }
    assert(generated.budget.zone_ids == pre.budget.zone_ids.remove(zid));
    assert(generated.budget.zones == pre.budget.zones.remove(zid));
    assert(removed.budget == generated.budget);
    cpu.1 + iommu.1 + seq![remove_op]
}

impl super::SoftwareRefinement for SoftwareSpec {
    type Step = BudgetSpec::Step;

    open spec fn view(&self) -> SoftwareView {
        SoftwareSpec::view(self)
    }

    open spec fn invariants(&self) -> bool {
        self.budget.invariant()
    }

    open spec fn next(pre: Self, post: Self, step: Self::Step) -> bool {
        BudgetSpec::State::next_by(pre.budget, post.budget, step)
    }

    proof fn invariants_imply_view_wf(&self) {
        lemma_budget_projection_wf(*self);
    }

    proof fn step_refines(pre: Self, post: Self, step: Self::Step) -> (ops: Seq<SoftwareOp>) {
        match step {
            BudgetSpec::Step::add_zone(zid) => { lemma_add_zone_step_refines(pre, post, zid) },
            BudgetSpec::Step::remove_zone(zid) => { lemma_remove_zone_step_refines(pre, post, zid)
            },
            BudgetSpec::Step::cpu_insert_region(zid, region) => {
                lemma_cpu_insert_region_step_refines(pre, post, zid, region)
            },
            BudgetSpec::Step::cpu_remove_region(zid, region) => {
                lemma_cpu_remove_region_step_refines(pre, post, zid, region)
            },
            BudgetSpec::Step::cpu_clear(zid) => { lemma_cpu_clear_step_refines(pre, post, zid) },
            BudgetSpec::Step::iommu_insert_region(zid, region) => {
                lemma_iommu_insert_region_step_refines(pre, post, zid, region)
            },
            BudgetSpec::Step::iommu_remove_region(zid, region) => {
                lemma_iommu_remove_region_step_refines(pre, post, zid, region)
            },
            BudgetSpec::Step::iommu_clear(zid) => { lemma_iommu_clear_step_refines(pre, post, zid)
            },
            BudgetSpec::Step::dummy_to_use_type_params(_) => {
                reveal(BudgetSpec::State::next_by);
                assert(false);
                Seq::empty()
            },
        }
    }
}

} // verus!
