//! Ghost state machine specifications for the hypervisor memory manager.
//!
//! - [`weak_spec`]: assumption-1 (`ClosureSpec`, global `all_regions`) state machine and tokens.
//! - [`strong_spec`]: assumption-2 (`BudgetSpec`, per-zone static budget) state machine and tokens.
pub mod budget;
pub mod closure;

use crate::{address::region::MemoryRegion, memory_set::SpecMemorySet};
use vstd::prelude::*;

pub use budget::{BudgetSpec, BudgetSpecInstance, BudgetZoneIdsToken, BudgetZoneToken};

verus! {

pub use closure::{
    all_regions, all_regions_disjoint, all_regions_valid, ClosureRegionToken, ClosureSpec,
    ClosureSpecInstance, ClosureZoneIdsToken, ClosureZoneToken,
};

/// Ghost state for one zone tracked inside `ClosureSpec` or `BudgetSpec`.
///
/// A zone owns two page-table-backed memory sets: the CPU stage-2 set
/// (`cpu_mem_set`, kept in sync with the tokenized MMU) and the IOMMU/SMMU set
/// (`iommu_mem_set`).
pub ghost struct GhostZone {
    /// CPU stage-2 memory set (regions **and** induced mappings).
    pub cpu_mem_set: SpecMemorySet,
    /// IOMMU/SMMU memory set (regions **and** induced mappings).
    pub iommu_mem_set: SpecMemorySet,
}

impl GhostZone {
    /// Well-formedness: both memory sets are internally well-formed.
    pub open spec fn wf(&self) -> bool {
        &&& self.cpu_mem_set.wf()
        &&& self.iommu_mem_set.wf()
    }

    /// Region set of this zone: the union of the CPU and IOMMU region sets.
    pub open spec fn regions(&self) -> Set<MemoryRegion> {
        self.cpu_mem_set.regions.union(self.iommu_mem_set.regions)
    }

    /// Whether a region belongs to this zone (either memory set).
    pub open spec fn contains_region(&self, region: MemoryRegion) -> bool {
        self.regions().contains(region)
    }

    /// Insert a region into the CPU memory set of this zone (regions and the page
    /// table grow together, keeping `cpu_mem_set` exact-dense).
    pub open spec fn cpu_insert_region(&self, region: MemoryRegion) -> Self {
        Self {
            cpu_mem_set: self.cpu_mem_set.insert_region(region),
            iommu_mem_set: self.iommu_mem_set,
        }
    }

    /// Remove a region from the CPU memory set of this zone.
    pub open spec fn cpu_remove_region(&self, region: MemoryRegion) -> Self
        recommends
            self.cpu_mem_set.regions.contains(region),
    {
        Self {
            cpu_mem_set: self.cpu_mem_set.remove_region_exact(region),
            iommu_mem_set: self.iommu_mem_set,
        }
    }

    /// Insert a region into the IOMMU memory set of this zone.
    pub open spec fn iommu_insert_region(&self, region: MemoryRegion) -> Self {
        Self {
            cpu_mem_set: self.cpu_mem_set,
            iommu_mem_set: self.iommu_mem_set.insert_region(region),
        }
    }

    /// Remove a region from the IOMMU memory set of this zone.
    pub open spec fn iommu_remove_region(&self, region: MemoryRegion) -> Self
        recommends
            self.iommu_mem_set.regions.contains(region),
    {
        Self {
            cpu_mem_set: self.cpu_mem_set,
            iommu_mem_set: self.iommu_mem_set.remove_region_exact(region),
        }
    }

    /// Compatibility wrapper used by the ClosureSpec path (CPU side).
    pub open spec fn insert_region(&self, region: MemoryRegion) -> Self {
        self.cpu_insert_region(region)
    }

    /// Compatibility wrapper used by the ClosureSpec path (CPU side).
    pub open spec fn remove_region(&self, region: MemoryRegion) -> Self
        recommends
            self.cpu_mem_set.regions.contains(region),
    {
        self.cpu_remove_region(region)
    }
}

} // verus!
