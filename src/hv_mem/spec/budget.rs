//! Static physical-page-budget state machine for the hypervisor memory manager.
//!
//! Physical memory is partitioned into zone-private budgets and one global
//! shared budget. A CPU or IOMMU region is admissible when its entire physical
//! footprint lies in either budget. Shared-budget regions may deliberately
//! overlap in physical memory while using different guest addresses or
//! attributes. Within each CPU/IOMMU memory set, zone-private regions remain
//! pairwise non-overlapping in physical memory so removing one region cannot
//! silently release another zone-private mapping's pages.
//!
//! The budgets are static pure functions rather than tokenized fields. Region
//! transitions therefore consume only the zone-local `zones[zid]` shard and
//! retain the read-lock concurrency of the original `BudgetSpec` protocol.
use super::GhostZone;
use crate::{address::region::MemoryRegion, memory_set::SpecMemorySet, model::types::PhysPage};
use verus_state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;

verus! {

use crate::constants::*;

/// Static zone-private physical-page budget of zone `zid`.
pub uninterp spec fn zone_private_pages(zid: nat) -> Set<PhysPage>;

/// Static physical pages that every zone may map.
pub uninterp spec fn global_shared_pages() -> Set<PhysPage>;

/// Axiom: zone-private page budgets of distinct zones are pairwise disjoint.
pub axiom fn zone_private_pages_pairwise_disjoint()
    ensures
        forall|zid1: nat, zid2: nat, page: PhysPage|
            #![trigger zone_private_pages(zid1).contains(page),
                zone_private_pages(zid2).contains(page)]
            zid1 != zid2 && zone_private_pages(zid1).contains(page)
                ==> !zone_private_pages(zid2).contains(page),
;

/// Axiom: no zone-private page is globally shared.
pub axiom fn zone_private_pages_disjoint_from_global_shared()
    ensures
        forall|zid: nat, page: PhysPage| #[trigger]
            zone_private_pages(zid).contains(page) ==> !global_shared_pages().contains(page),
;

/// The physical page occupied by page index `i` of `region`.
pub open spec fn region_phys_page(region: MemoryRegion, i: nat) -> PhysPage {
    PhysPage(region.pstart@.0 / SPEC_PAGE_SIZE + i)
}

/// The complete physical-page footprint of `region`.
pub open spec fn region_phys_pages(region: MemoryRegion) -> Set<PhysPage> {
    Set::new(
        |page: PhysPage|
            exists|i: nat| 0 <= i < region.pages && #[trigger] region_phys_page(region, i) == page,
    )
}

/// `region` lies wholly in zone `zid`'s zone-private page budget.
pub open spec fn region_in_zone_private_budget(zid: nat, region: MemoryRegion) -> bool {
    region_phys_pages(region).subset_of(zone_private_pages(zid))
}

/// `region` lies wholly in the global shared page budget.
pub open spec fn region_in_global_shared_budget(region: MemoryRegion) -> bool {
    region_phys_pages(region).subset_of(global_shared_pages())
}

/// Page-budget authorization for either a CPU or IOMMU region.
pub open spec fn region_in_budget(zid: nat, region: MemoryRegion) -> bool {
    region_in_zone_private_budget(zid, region) || region_in_global_shared_budget(region)
}

/// Whether `region` is physically non-overlapping with every zone-private
/// region already in `mem_set`.
pub open spec fn pmem_nonoverlap_with_zone_private_regions(
    zid: nat,
    mem_set: SpecMemorySet,
    region: MemoryRegion,
) -> bool {
    forall|old_region: MemoryRegion| #[trigger]
        mem_set.regions.contains(old_region) && region_in_zone_private_budget(zid, old_region)
            ==> !old_region.spec_overlaps_pmem(region)
}

/// Zone-private regions in one memory set are pairwise non-overlapping in physical memory.
pub open spec fn private_regions_pmem_nonoverlap(zid: nat, mem_set: SpecMemorySet) -> bool {
    forall|r1: MemoryRegion, r2: MemoryRegion| #[trigger]
        mem_set.regions.contains(r1) && #[trigger] mem_set.regions.contains(r2) && r1 != r2
            && region_in_zone_private_budget(zid, r1) && region_in_zone_private_budget(zid, r2)
            ==> !r1.spec_overlaps_pmem(r2)
}

/// Every region in `mem_set` is authorized by `zid`'s zone-private budget or the
/// global shared budget.
pub open spec fn all_regions_in_budget(zid: nat, mem_set: SpecMemorySet) -> bool {
    forall|region: MemoryRegion| #[trigger]
        mem_set.regions.contains(region) ==> region_in_budget(zid, region)
}

/// A valid global-shared region cannot also lie in any zone-private budget.
pub proof fn lemma_global_shared_region_not_zone_private(zid: nat, region: MemoryRegion)
    requires
        region.spec_valid(),
        region_in_global_shared_budget(region),
    ensures
        !region_in_zone_private_budget(zid, region),
{
    let page = region_phys_page(region, 0);
    assert(region_phys_pages(region).contains(page)) by {
        assert(0 < region.pages);
    };
    zone_private_pages_disjoint_from_global_shared();
    if region_in_zone_private_budget(zid, region) {
        assert(zone_private_pages(zid).contains(page));
        assert(global_shared_pages().contains(page));
        assert(!global_shared_pages().contains(page));
        assert(false);
    }
}

/// A valid zone-private region cannot also lie in the global-shared budget.
pub proof fn lemma_zone_private_region_not_global_shared(zid: nat, region: MemoryRegion)
    requires
        region.spec_valid(),
        region_in_zone_private_budget(zid, region),
    ensures
        !region_in_global_shared_budget(region),
{
    let page = region_phys_page(region, 0);
    assert(region_phys_pages(region).contains(page)) by {
        assert(0 < region.pages);
    };
    zone_private_pages_disjoint_from_global_shared();
    if region_in_global_shared_budget(region) {
        assert(zone_private_pages(zid).contains(page));
        assert(global_shared_pages().contains(page));
        assert(!global_shared_pages().contains(page));
        assert(false);
    }
}

/// Insertion preserves page-budget authorization and zone-private-region pmem non-overlap.
pub proof fn lemma_insert_region_preserves_budget_policy(
    zid: nat,
    mem_set: SpecMemorySet,
    region: MemoryRegion,
)
    requires
        mem_set.wf(),
        all_regions_in_budget(zid, mem_set),
        private_regions_pmem_nonoverlap(zid, mem_set),
        region.spec_valid(),
        region_in_budget(zid, region),
        region_in_zone_private_budget(zid, region) ==> pmem_nonoverlap_with_zone_private_regions(
            zid,
            mem_set,
            region,
        ),
        !mem_set.regions.contains(region),
        !mem_set.overlaps_vmem(region),
    ensures
        all_regions_in_budget(zid, mem_set.insert_region(region)),
        private_regions_pmem_nonoverlap(zid, mem_set.insert_region(region)),
{
    let new_mem_set = mem_set.insert_region(region);
    assert forall|r: MemoryRegion| #[trigger]
        new_mem_set.regions.contains(r) implies region_in_budget(zid, r) by {
        if r != region {
            assert(mem_set.regions.contains(r));
        }
    };
    assert forall|r1: MemoryRegion, r2: MemoryRegion| #[trigger]
        new_mem_set.regions.contains(r1) && #[trigger] new_mem_set.regions.contains(r2) && r1 != r2
            && region_in_zone_private_budget(zid, r1) && region_in_zone_private_budget(
            zid,
            r2,
        ) implies !r1.spec_overlaps_pmem(r2) by {
        if r1 == region {
            assert(mem_set.regions.contains(r2));
            assert(!r2.spec_overlaps_pmem(region));
            assert(r2.spec_valid());
            region.lemma_overlaps_pmem_symmetric(r2);
        } else if r2 == region {
            assert(mem_set.regions.contains(r1));
        } else {
            assert(mem_set.regions.contains(r1));
            assert(mem_set.regions.contains(r2));
        }
    };
}

/// Removing a region only shrinks the set, so it preserves the budget policy.
pub proof fn lemma_remove_region_preserves_budget_policy(
    zid: nat,
    mem_set: SpecMemorySet,
    region: MemoryRegion,
)
    requires
        all_regions_in_budget(zid, mem_set),
        private_regions_pmem_nonoverlap(zid, mem_set),
    ensures
        all_regions_in_budget(zid, mem_set.remove_region_exact(region)),
        private_regions_pmem_nonoverlap(zid, mem_set.remove_region_exact(region)),
{
    let new_mem_set = mem_set.remove_region_exact(region);
    assert forall|r: MemoryRegion| #[trigger]
        new_mem_set.regions.contains(r) implies region_in_budget(zid, r) by {
        assert(mem_set.regions.contains(r));
    };
    assert forall|r1: MemoryRegion, r2: MemoryRegion| #[trigger]
        new_mem_set.regions.contains(r1) && #[trigger] new_mem_set.regions.contains(r2) && r1 != r2
            && region_in_zone_private_budget(zid, r1) && region_in_zone_private_budget(
            zid,
            r2,
        ) implies !r1.spec_overlaps_pmem(r2) by {
        assert(mem_set.regions.contains(r1));
        assert(mem_set.regions.contains(r2));
    };
}

/// An empty memory set satisfies both budget-policy clauses.
pub proof fn lemma_empty_memory_set_budget_policy(zid: nat)
    ensures
        all_regions_in_budget(zid, SpecMemorySet { regions: Set::empty(), mappings: Map::empty() }),
        private_regions_pmem_nonoverlap(
            zid,
            SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
        ),
{
}

tokenized_state_machine! {
    BudgetSpec {
        fields {
            #[sharding(variable)]
            pub zone_ids: Set<nat>,

            #[sharding(map)]
            pub zones: Map<nat, GhostZone>,
        }
        #[invariant]
        pub fn inv_zone_ids(&self) -> bool {
            self.zones.dom() == self.zone_ids
        }

        #[invariant]
        pub fn inv_zones_wf(&self) -> bool {
            forall|zid: nat|
                self.zones.contains_key(zid) ==> #[trigger] self.zones[zid].wf()
        }

        /// Every CPU region lies entirely in one of the two admissible budgets.
        #[invariant]
        pub fn inv_cpu_regions_in_budget(&self) -> bool {
            forall|zid: nat| self.zones.contains_key(zid) ==> all_regions_in_budget(
                zid,
                self.zones[zid].cpu_mem_set,
            )
        }

        /// IOMMU regions obey the same zone-private-or-global-shared policy as CPU regions.
        #[invariant]
        pub fn inv_iommu_regions_in_budget(&self) -> bool {
            forall|zid: nat| self.zones.contains_key(zid) ==> all_regions_in_budget(
                zid,
                self.zones[zid].iommu_mem_set,
            )
        }

        /// Zone-private CPU regions are pairwise non-overlapping in physical memory.
        #[invariant]
        pub fn inv_cpu_private_regions_pmem_nonoverlap(&self) -> bool {
            forall|zid: nat|
                self.zones.contains_key(zid) ==> private_regions_pmem_nonoverlap(
                    zid,
                    self.zones[zid].cpu_mem_set,
                )
        }

        /// Zone-private IOMMU regions are pairwise non-overlapping in physical memory.
        #[invariant]
        pub fn inv_iommu_private_regions_pmem_nonoverlap(&self) -> bool {
            forall|zid: nat|
                self.zones.contains_key(zid) ==> private_regions_pmem_nonoverlap(
                    zid,
                    self.zones[zid].iommu_mem_set,
                )
        }

        init! {
            initialize() {
                init zone_ids = Set::empty();
                init zones = Map::empty();
            }
        }

        transition! {
            add_zone(zid: nat) {
                require(!pre.zone_ids.contains(zid));
                update zone_ids = pre.zone_ids.insert(zid);
                add zones += [zid => GhostZone {
                    cpu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
                    iommu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
                }];
            }
        }

        transition! {
            remove_zone(zid: nat) {
                remove zones -= [zid => let _zone];
                update zone_ids = pre.zone_ids.remove(zid);
            }
        }

        transition! {
            cpu_insert_region(zid: nat, region: MemoryRegion) {
                remove zones -= [zid => let zone];
                require(region.spec_valid());
                require(region_in_budget(zid, region));
                require(region_in_zone_private_budget(zid, region)
                    ==> pmem_nonoverlap_with_zone_private_regions(
                        zid,
                        zone.cpu_mem_set,
                        region,
                    ));
                require(!zone.cpu_mem_set.regions.contains(region));
                require(!zone.cpu_mem_set.overlaps_vmem(region));
                add zones += [zid => zone.cpu_insert_region(region)];
            }
        }

        transition! {
            cpu_remove_region(zid: nat, region: MemoryRegion) {
                remove zones -= [zid => let zone];
                require(zone.cpu_mem_set.regions.contains(region));
                add zones += [zid => zone.cpu_remove_region(region)];
            }
        }

        transition! {
            cpu_clear(zid: nat) {
                remove zones -= [zid => let zone];
                add zones += [zid => zone.cpu_clear()];
            }
        }

        transition! {
            iommu_insert_region(zid: nat, region: MemoryRegion) {
                remove zones -= [zid => let zone];
                require(region.spec_valid());
                require(region_in_budget(zid, region));
                require(region_in_zone_private_budget(zid, region)
                    ==> pmem_nonoverlap_with_zone_private_regions(
                        zid,
                        zone.iommu_mem_set,
                        region,
                    ));
                require(!zone.iommu_mem_set.regions.contains(region));
                require(!zone.iommu_mem_set.overlaps_vmem(region));
                add zones += [zid => zone.iommu_insert_region(region)];
            }
        }

        transition! {
            iommu_remove_region(zid: nat, region: MemoryRegion) {
                remove zones -= [zid => let zone];
                require(zone.iommu_mem_set.regions.contains(region));
                add zones += [zid => zone.iommu_remove_region(region)];
            }
        }

        transition! {
            iommu_clear(zid: nat) {
                remove zones -= [zid => let zone];
                add zones += [zid => zone.iommu_clear()];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(add_zone)]
        fn add_zone_inductive(pre: Self, post: Self, zid: nat) {
            lemma_empty_memory_set_budget_policy(zid);
        }

        #[inductive(remove_zone)]
        fn remove_zone_inductive(pre: Self, post: Self, zid: nat) { }

        #[inductive(cpu_insert_region)]
        fn cpu_insert_region_inductive(pre: Self, post: Self, zid: nat, region: MemoryRegion) {
            let old_zone = pre.zones[zid];
            assert(old_zone.wf());
            old_zone.cpu_mem_set.lemma_insert_region_wf(region);
            lemma_insert_region_preserves_budget_policy(zid, old_zone.cpu_mem_set, region);
        }

        #[inductive(cpu_remove_region)]
        fn cpu_remove_region_inductive(pre: Self, post: Self, zid: nat, region: MemoryRegion) {
            let old_zone = pre.zones[zid];
            assert(old_zone.wf());
            old_zone.cpu_mem_set.lemma_remove_region_exact_wf(region);
            lemma_remove_region_preserves_budget_policy(zid, old_zone.cpu_mem_set, region);
        }

        #[inductive(cpu_clear)]
        fn cpu_clear_inductive(pre: Self, post: Self, zid: nat) {
            let old_zone = pre.zones[zid];
            assert(old_zone.wf());
            lemma_empty_memory_set_budget_policy(zid);
        }

        #[inductive(iommu_insert_region)]
        fn iommu_insert_region_inductive(pre: Self, post: Self, zid: nat, region: MemoryRegion) {
            let old_zone = pre.zones[zid];
            assert(old_zone.wf());
            old_zone.iommu_mem_set.lemma_insert_region_wf(region);
            lemma_insert_region_preserves_budget_policy(zid, old_zone.iommu_mem_set, region);
        }

        #[inductive(iommu_remove_region)]
        fn iommu_remove_region_inductive(pre: Self, post: Self, zid: nat, region: MemoryRegion) {
            let old_zone = pre.zones[zid];
            assert(old_zone.wf());
            old_zone.iommu_mem_set.lemma_remove_region_exact_wf(region);
            lemma_remove_region_preserves_budget_policy(zid, old_zone.iommu_mem_set, region);
        }

        #[inductive(iommu_clear)]
        fn iommu_clear_inductive(pre: Self, post: Self, zid: nat) {
            let old_zone = pre.zones[zid];
            assert(old_zone.wf());
            lemma_empty_memory_set_budget_policy(zid);
        }
    }
}

/// `BudgetSpec` instance token (constant-sharded, shared by reference).
pub type BudgetSpecInstance = BudgetSpec::Instance;

/// Global zone-id set token (variable-sharded; held in the HvMem global lock).
pub type BudgetZoneIdsToken = BudgetSpec::zone_ids;

/// Per-zone zone-state token (map-sharded; lives in the zone-level lock).
pub type BudgetZoneToken = BudgetSpec::zones;

} // verus!
