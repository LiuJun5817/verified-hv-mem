//! Ghost state machine specifications for the hypervisor memory manager.
//!
//! - [`weak_spec`]: assumption-1 (`ClosureSpec`, global `all_regions`) state machine and tokens.
//! - [`strong_spec`]: assumption-2 (`BudgetSpec`, per-zone static budget) state machine and tokens.
pub mod budget;
pub mod closure;

use crate::{
    address::{addr::SpecVAddr, frame::SpecFrame, region::MemoryRegion},
    memory_set::SpecMemorySet,
};
use vstd::{prelude::*, tokens::InstanceId};

pub use budget::{BudgetSpec, BudgetSpecInstance, BudgetZoneIdsToken, BudgetZoneToken};
pub use closure::{
    all_regions, all_regions_disjoint, all_regions_valid, ClosureRegionToken, ClosureSpec,
    ClosureSpecInstance, ClosureZoneIdsToken, ClosureZoneToken,
};

verus! {

/// Ghost state for one zone tracked inside `ClosureSpec` or `BudgetSpec`.
pub ghost struct GhostZone {
    /// Region sequence used by the existing memory-set abstraction.
    pub mem_set: SpecMemorySet,
}

impl GhostZone {
    /// Well-formedness: all regions in the zone are valid and non-overlapping.
    pub open spec fn wf(&self) -> bool {
        self.mem_set.wf()
    }

    /// Region set of this zone.
    pub open spec fn regions(&self) -> Set<MemoryRegion> {
        self.mem_set.regions
    }

    /// Whether a region belongs to this zone.
    pub open spec fn contains_region(&self, region: MemoryRegion) -> bool {
        self.regions().contains(region)
    }

    /// Insert a region into this zone (regions and the page table grow together,
    /// keeping `mem_set` exact-dense).
    pub open spec fn insert_region(&self, region: MemoryRegion) -> Self {
        Self {
            mem_set: SpecMemorySet {
                regions: self.regions().insert(region),
                mappings: self.mem_set.mappings.union_prefer_right(region.spec_mappings()),
            },
        }
    }

    /// Remove a region from this zone.
    pub open spec fn remove_region(&self, region: MemoryRegion) -> Self
        recommends
            self.regions().contains(region),
    {
        Self {
            mem_set: SpecMemorySet {
                regions: self.regions().remove(region),
                mappings: self.mem_set.mappings.remove_keys(region.spec_mappings().dom()),
            },
        }
    }

    /// Inserting a fresh non-overlapping valid region keeps the zone well-formed:
    /// the page table grows by exactly the region's dense mappings, and the new
    /// region's pages are vmem-disjoint from all old ones, so the exact-dense
    /// consistency is preserved.
    pub proof fn lemma_insert_region_wf(&self, region: MemoryRegion)
        requires
            self.wf(),
            region.spec_valid(),
            !self.mem_set.overlaps_vmem(region),
            !self.contains_region(region),
        ensures
            self.insert_region(region).wf(),
    {
        let new = self.insert_region(region);
        let old_maps = self.mem_set.mappings;
        let region_maps = region.spec_mappings();
        assert(new.mem_set.regions =~= self.regions().insert(region));
        assert(new.mem_set.mappings == old_maps.union_prefer_right(region_maps));

        // 1. regions valid
        assert forall|r: MemoryRegion| #[trigger]
            new.mem_set.regions.contains(r) implies r.spec_valid() by {
            if r != region {
                assert(self.regions().contains(r));
            }
        }
        // 2. regions non-overlapping (the new region vs each old one, both directions)
        assert forall|r1: MemoryRegion, r2: MemoryRegion| #[trigger]
            new.mem_set.regions.contains(r1) && #[trigger] new.mem_set.regions.contains(r2) && r1
                != r2 implies !r1.spec_overlaps_vmem(r2) by {
            if r1 == region {
                assert(self.regions().contains(r2) && !r2.spec_overlaps_vmem(region));
                r2.lemma_overlaps_vmem_symmetric(region);
            } else if r2 == region {
                assert(self.regions().contains(r1) && !r1.spec_overlaps_vmem(region));
            } else {
                assert(self.regions().contains(r1) && self.regions().contains(r2));
            }
        }
        // 3. completeness: every region page is mapped to its frame
        assert forall|r: MemoryRegion, i: nat|
            #![trigger new.mem_set.regions.contains(r), r.spec_page_vaddr(i)]
            new.mem_set.regions.contains(r) && 0 <= i
                < r.pages implies new.mem_set.mappings.contains_pair(
            r.spec_page_vaddr(i),
            r.spec_frame(i),
        ) by {
            if r == region {
                region.lemma_mappings_contains_pair(i);
            } else {
                assert(self.regions().contains(r));
                // r's page is not one of `region`'s pages (vmem-disjoint), so the
                // union keeps the old (correct) value.
                assert(!region_maps.contains_key(r.spec_page_vaddr(i))) by {
                    if region_maps.contains_key(r.spec_page_vaddr(i)) {
                        let j = choose|j: nat|
                            0 <= j < region.pages && r.spec_page_vaddr(i) == region.spec_page_vaddr(
                                j,
                            );
                        MemoryRegion::lemma_pages_disjoint(r, region, i, j);
                    }
                }
            }
        }
        // 4. soundness: every mapping is some region page's frame
        assert forall|v: SpecVAddr, f: SpecFrame| #[trigger]
            new.mem_set.mappings.contains_pair(v, f) implies exists|r: MemoryRegion, i: nat|
            #![trigger new.mem_set.regions.contains(r), r.spec_page_vaddr(i)]
            new.mem_set.regions.contains(r) && 0 <= i < r.pages && v == r.spec_page_vaddr(i) && f
                == r.spec_frame(i) by {
            if region_maps.contains_key(v) {
                region.lemma_mappings_sound(v);
                assert(new.mem_set.regions.contains(region));
            } else {
                // v is from the old map (union prefers right only on `region`'s keys),
                // so the old soundness clause supplies an old region witness, which is
                // still a region of the new zone.
                assert(self.mem_set.mappings.contains_pair(v, f));
                let (r2, i2) = choose|r2: MemoryRegion, i2: nat|
                    self.regions().contains(r2) && 0 <= i2 < r2.pages && v == r2.spec_page_vaddr(i2)
                        && f == r2.spec_frame(i2);
                assert(new.mem_set.regions.contains(r2));
            }
        }
    }

    /// Removing a present region keeps the zone well-formed: its (vmem-disjoint)
    /// keys are deleted, leaving exactly the other regions' dense mappings.
    pub proof fn lemma_remove_region_wf(&self, region: MemoryRegion)
        requires
            self.wf(),
            self.contains_region(region),
        ensures
            self.remove_region(region).wf(),
    {
        let new = self.remove_region(region);
        let region_maps = region.spec_mappings();
        assert(new.mem_set.regions =~= self.regions().remove(region));
        assert(new.mem_set.mappings == self.mem_set.mappings.remove_keys(region_maps.dom()));
        assert(region.spec_valid());  // region ∈ regions, self.wf() ⇒ valid

        // 1 & 2: regions are a subset of the old ones.
        assert forall|r: MemoryRegion| #[trigger]
            new.mem_set.regions.contains(r) implies r.spec_valid() by {
            assert(self.regions().contains(r));
        }
        assert forall|r1: MemoryRegion, r2: MemoryRegion| #[trigger]
            new.mem_set.regions.contains(r1) && #[trigger] new.mem_set.regions.contains(r2) && r1
                != r2 implies !r1.spec_overlaps_vmem(r2) by {
            assert(self.regions().contains(r1) && self.regions().contains(r2));
        }
        // 3. completeness: remaining region pages are not `region`'s pages, so they
        // survive the key removal.
        assert forall|r: MemoryRegion, i: nat|
            #![trigger new.mem_set.regions.contains(r), r.spec_page_vaddr(i)]
            new.mem_set.regions.contains(r) && 0 <= i
                < r.pages implies new.mem_set.mappings.contains_pair(
            r.spec_page_vaddr(i),
            r.spec_frame(i),
        ) by {
            assert(self.regions().contains(r) && r != region);
            assert(!region_maps.dom().contains(r.spec_page_vaddr(i))) by {
                if region_maps.contains_key(r.spec_page_vaddr(i)) {
                    let j = choose|j: nat|
                        0 <= j < region.pages && r.spec_page_vaddr(i) == region.spec_page_vaddr(j);
                    MemoryRegion::lemma_pages_disjoint(r, region, i, j);
                }
            }
        }
        // 4. soundness: surviving mappings come from a remaining region (not `region`).
        assert forall|v: SpecVAddr, f: SpecFrame| #[trigger]
            new.mem_set.mappings.contains_pair(v, f) implies exists|r: MemoryRegion, i: nat|
            #![trigger new.mem_set.regions.contains(r), r.spec_page_vaddr(i)]
            new.mem_set.regions.contains(r) && 0 <= i < r.pages && v == r.spec_page_vaddr(i) && f
                == r.spec_frame(i) by {
            // v survived removal ⇒ v ∉ region's pages, so the witnessing region ≠ region.
            assert(self.mem_set.mappings.contains_pair(v, f));
            let (r, i) = choose|r: MemoryRegion, i: nat|
                self.regions().contains(r) && 0 <= i < r.pages && v == r.spec_page_vaddr(i) && f
                    == r.spec_frame(i);
            if r == region {
                region.lemma_mappings_contains_pair(i);  // ⇒ v ∈ region's keys: contradiction
            }
            assert(new.mem_set.regions.contains(r));
        }
    }
}

} // verus!
