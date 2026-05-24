//! Ghost state machine specifications for the hypervisor memory manager.
//!
//! - [`weak_spec`]: assumption-1 (`ClosureSpec`, global `all_regions`) state machine and tokens.
//! - [`strong_spec`]: assumption-2 (`BudgetSpec`, per-zone static budget) state machine and tokens.
pub mod budget;
pub mod closure;

use crate::{
    address::{addr::SpecVAddr, region::MemoryRegion},
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
    /// Allocator instance id shared by the whole hypervisor memory manager.
    pub alloc_inst_id: InstanceId,
    /// Region sequence used by the existing memory-set abstraction.
    pub mem_set: SpecMemorySet,
}

impl GhostZone {
    /// Well-formedness relative to the system allocator instance.
    pub open spec fn wf(&self, alloc_inst_id: InstanceId) -> bool {
        &&& self.alloc_inst_id == alloc_inst_id
        &&& self.mem_set.wf()
    }

    /// Region set of this zone.
    pub open spec fn regions(&self) -> Set<MemoryRegion> {
        self.mem_set.regions
    }

    /// Whether a region belongs to this zone.
    pub open spec fn contains_region(&self, region: MemoryRegion) -> bool {
        self.regions().contains(region)
    }

    /// Insert a region into this zone.
    pub open spec fn insert_region(&self, region: MemoryRegion) -> Self {
        Self {
            alloc_inst_id: self.alloc_inst_id,
            mem_set: SpecMemorySet { regions: self.regions().insert(region) },
        }
    }

    /// Remove a region from this zone.
    pub open spec fn remove_region(&self, region: MemoryRegion) -> Self
        recommends
            self.regions().contains(region),
    {
        Self {
            alloc_inst_id: self.alloc_inst_id,
            mem_set: SpecMemorySet { regions: self.regions().remove(region) },
        }
    }
}

/// Minimal spec interface shared by `ZoneState` (ClosureSpec) and `BudgetZoneState`
/// (BudgetSpec). Defined here in the `spec` layer so that `zone.rs` can implement
/// it without depending on the `policy` module, avoiding a circular dependency.
///
/// Used as the bound `P::ZoneToken: ZoneStateOps` in the `HvMemPolicy` trait.
pub trait ZoneStateOps {
    /// The zone ID (key in the `zones` map sharding).
    spec fn zone_id(&self) -> nat;

    /// The ghost zone state (value in the `zones` map sharding).
    spec fn ghost_zone(&self) -> GhostZone;

    /// Well-formedness relative to a spec-instance ID.
    spec fn wf(&self, inst_id: InstanceId) -> bool;
}

} // verus!
