//! Ghost protocols used by the policy-generic `Zone` and `HvMem` layers.
pub mod budget;
pub mod closure;
pub mod enclave;

use super::spec::GhostZone;
use crate::memory_set::SpecMemorySet;
pub use budget::{BudgetGlobalState, BudgetProtocol, BudgetZoneState};
pub use closure::{ClosureGlobalState, ClosureProtocol, ClosureZoneState};
pub use enclave::{EnclaveGlobalState, EnclaveProtocol, EnclaveZoneState};

use vstd::prelude::*;

verus! {

/// Common view of a policy's per-zone ghost token.
pub trait ZoneStateOps {
    /// The zone ID (key in the `zones` map sharding).
    spec fn zone_id(&self) -> nat;

    /// The ghost zone state (value in the `zones` map sharding).
    spec fn ghost_zone(&self) -> GhostZone;

    /// Well-formedness relative to a spec-instance ID.
    spec fn wf(&self, mem_inst_id: InstanceId) -> bool;
}

/// Ghost interface for zone lifecycle operations.
///
/// Region operations remain policy-specific because their global-state access
/// and transition obligations differ.
pub trait ZoneGhostProtocol: Sized {
    /// Per-zone tracked ghost state (map-sharded token from `zones[zid]`).
    type ZoneState: ZoneStateOps;

    /// Global tracked ghost state stored in `HvMem`'s lock content.
    type GlobalState;

    // ─── Spec predicates ─────────────────────────────────────────────────────
    /// Well-formedness: all internal tokens are consistent with each other.
    spec fn global_wf(gs: &Self::GlobalState) -> bool;

    /// The spec-instance ID embedded in the global state.
    spec fn mem_inst_id(gs: &Self::GlobalState) -> InstanceId;

    /// The current set of registered zone IDs.
    spec fn zone_ids(gs: &Self::GlobalState) -> Set<nat>;

    // ─── Proof transitions ────────────────────────────────────────────────────
    /// Register a new empty zone; returns a fresh zone token.
    ///
    /// The zone starts with no regions; use `insert_region` to populate it.
    proof fn add_zone(tracked gs: &mut Self::GlobalState, zid: nat) -> (tracked zt: Self::ZoneState)
        requires
            Self::global_wf(old(gs)),
            !Self::zone_ids(old(gs)).contains(zid),
        ensures
            Self::global_wf(gs),
            Self::mem_inst_id(gs) == Self::mem_inst_id(old(gs)),
            zt.zone_id() == zid,
            zt.ghost_zone().regions() =~= Set::empty(),
            // `Zone::new` requires a fully empty CPU and IOMMU state.
            zt.ghost_zone() == (GhostZone {
                cpu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
                iommu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
            }),
            zt.wf(Self::mem_inst_id(gs)),
            Self::zone_ids(gs) =~= Self::zone_ids(old(gs)).insert(zid),
    ;

    /// Deregister an empty zone; consumes its zone token.
    proof fn remove_zone(tracked gs: &mut Self::GlobalState, tracked zt: Self::ZoneState)
        requires
            Self::global_wf(old(gs)),
            zt.wf(Self::mem_inst_id(old(gs))),
            zt.ghost_zone().cpu_mem_set.empty(),
            zt.ghost_zone().iommu_mem_set.empty(),
        ensures
            Self::global_wf(gs),
            Self::mem_inst_id(gs) == Self::mem_inst_id(old(gs)),
            Self::zone_ids(gs) =~= Self::zone_ids(old(gs)).remove(zt.zone_id()),
    ;
}

} // verus!
