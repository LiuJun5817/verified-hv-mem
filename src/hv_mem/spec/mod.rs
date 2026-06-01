//! Ghost state machine specifications for the hypervisor memory manager.
//!
//! - [`weak_spec`]: assumption-1 (`ClosureSpec`, global `all_regions`) state machine and tokens.
//! - [`strong_spec`]: assumption-2 (`BudgetSpec`, per-zone static budget) state machine and tokens.
pub mod budget;
pub mod closure;

use crate::{address::region::MemoryRegion, memory_set::SpecMemorySet};
use vstd::{prelude::*, tokens::InstanceId};

pub use budget::{BudgetSpec, BudgetSpecInstance, BudgetZoneIdsToken, BudgetZoneToken};
pub use closure::{
    ClosureRegionToken, ClosureSpec, ClosureSpecInstance, ClosureZoneIdsToken, ClosureZoneToken,
    all_regions, all_regions_disjoint, all_regions_valid,
};

verus! {

/// Ghost state for one zone tracked inside `ClosureSpec` or `BudgetSpec`.
pub ghost struct GhostZone {
    /// Region sequence used by the existing memory-set abstraction.
    pub cpu_mem_set: SpecMemorySet,
    pub iommu_mem_set: SpecMemorySet,
}

impl GhostZone {
    /// Well-formedness: all regions in the zone are valid and non-overlapping.
    pub open spec fn wf(&self) -> bool {
        &&& self.cpu_mem_set.wf()
        &&& self.iommu_mem_set.wf()
    }

    /// Region set of this zone.
    pub open spec fn regions(&self) -> Set<MemoryRegion> {
        self.cpu_mem_set.regions.union(self.iommu_mem_set.regions)
    }

    /// Whether a region belongs to this zone.
    pub open spec fn contains_region(&self, region: MemoryRegion) -> bool {
        self.regions().contains(region)
    }

    /// Insert a region into the CPU page-table memory set of this zone.
    pub open spec fn cpu_insert_region(&self, region: MemoryRegion) -> Self {
        Self {
            cpu_mem_set: SpecMemorySet { regions: self.cpu_mem_set.regions.insert(region) },
            iommu_mem_set: self.iommu_mem_set,
        }
    }

    /// Remove a region from the CPU page-table memory set of this zone.
    pub open spec fn cpu_remove_region(&self, region: MemoryRegion) -> Self
        recommends
            self.cpu_mem_set.regions.contains(region),
    {
        Self {
            cpu_mem_set: SpecMemorySet { regions: self.cpu_mem_set.regions.remove(region) },
            iommu_mem_set: self.iommu_mem_set,
        }
    }

    /// Insert a region into the IOMMU page-table memory set of this zone.
    pub open spec fn iommu_insert_region(&self, region: MemoryRegion) -> Self {
        Self {
            cpu_mem_set: self.cpu_mem_set,
            iommu_mem_set: SpecMemorySet { regions: self.iommu_mem_set.regions.insert(region) },
        }
    }

    /// Remove a region from the IOMMU page-table memory set of this zone.
    pub open spec fn iommu_remove_region(&self, region: MemoryRegion) -> Self
        recommends
            self.iommu_mem_set.regions.contains(region),
    {
        Self {
            cpu_mem_set: self.cpu_mem_set,
            iommu_mem_set: SpecMemorySet { regions: self.iommu_mem_set.regions.remove(region) },
        }
    }

    /// Compatibility wrapper used by the ClosureSpec path.
    pub open spec fn insert_region(&self, region: MemoryRegion) -> Self {
        self.cpu_insert_region(region)
    }

    /// Compatibility wrapper used by the ClosureSpec path.
    pub open spec fn remove_region(&self, region: MemoryRegion) -> Self
        recommends
            self.cpu_mem_set.regions.contains(region),
    {
        self.cpu_remove_region(region)
    }
}

} // verus!
