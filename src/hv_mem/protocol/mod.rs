//! Region-assignment protocol abstraction.
//!
//! Abstracts over the two safety assumptions (`ClosureSpec` / `BudgetSpec`) so that
//! `Zone` and `HvMem` are generic over `P: HvMemProtocol` rather than hard-wired.
//!
//! Submodules:
//! - [`weak`]:   assumption-1 ghost state (`ClosureGlobalState`) and `ClosureProtocol`.
//! - [`strong`]: assumption-2 ghost state (`BudgetGlobalState`) and `BudgetProtocol`.
pub mod budget;
pub mod closure;

pub use budget::{BudgetGlobalState, BudgetZoneState, BudgetProtocol};
pub use closure::{ClosureGlobalState, ClosureZoneState, ClosureProtocol};

use super::spec::{GhostZone, ZoneStateOps};
use crate::address::region::MemoryRegion;
use vstd::prelude::*;

verus! {

/// Top-level exec protocol trait that unifies `ClosureSpec` (assumption 1) and
/// `BudgetSpec` (assumption 2) under a single generic interface.
///
/// `Zone<PT, M, A, P>` and `HvMem<PT, M, A, P>` are parameterized by `P: HvMemProtocol`.
/// Swapping `P` switches the entire ghost-state bookkeeping strategy without changing
/// any exec code.
///
/// | Impl            | `ZoneToken`       | `GlobalState`       | Lock for insert    |
/// |-----------------|-------------------|---------------------|--------------------|
/// | `ClosureProtocol` | `ZoneState`       | `ClosureGlobalState`        | global + zone lock |
/// | `BudgetProtocol`  | `BudgetZoneState` | `BudgetGlobalState` | zone lock only     |
pub trait HvMemProtocol: Sized {
    /// Per-zone tracked ghost state (map-sharded token from `zones[zid]`).
    type ZoneToken: ZoneStateOps;

    /// Global tracked ghost state stored inside `HvMem`'s write-lock content.
    ///
    /// `ClosureProtocol`: `ClosureGlobalState` (holds `region_closure_tok` — global write lock required).
    /// `BudgetProtocol`:  `BudgetGlobalState` (no `region_closure_tok` — zone-local insert).
    type GlobalState;

    // ─── Spec predicates ─────────────────────────────────────────────────────
    /// Well-formedness: all internal tokens are consistent with each other.
    spec fn global_wf(gs: &Self::GlobalState) -> bool;

    /// The spec-instance ID embedded in the global state.
    spec fn inst_id(gs: &Self::GlobalState) -> InstanceId;

    /// The current set of registered zone IDs.
    spec fn zone_ids(gs: &Self::GlobalState) -> Set<nat>;

    /// The allocator instance ID stored as a constant in the spec state machine.
    ///
    /// Used to check `GhostZone::wf`: zones entering the system must have been
    /// constructed for this allocator instance.
    spec fn alloc_inst_id(gs: &Self::GlobalState) -> InstanceId;

    /// Policy-specific authorization predicate for adding a zone.
    ///
    /// `ClosureProtocol`: every region in `zone` belongs to `all_regions()` and is
    ///   not yet in the global region closure.
    /// `BudgetProtocol`: every region in `zone` lies within `zone_budget(zid)`.
    spec fn zone_authorized(gs: &Self::GlobalState, zid: nat, zone: GhostZone) -> bool;

    /// Policy-specific authorization predicate for inserting a region.
    ///
    /// `ClosureProtocol`: `region` is in `all_regions()` and not yet in the closure.
    /// `BudgetProtocol`: `region` is in `zone_budget(zt.zone_id())`.
    spec fn region_authorized(gs: &Self::GlobalState, zt: &Self::ZoneToken, region: MemoryRegion) -> bool;

    // ─── Proof transitions ────────────────────────────────────────────────────
    /// Register a new zone; returns a fresh zone token.
    proof fn add_zone(tracked gs: &mut Self::GlobalState, zid: nat, zone: GhostZone) -> (tracked zt:
        Self::ZoneToken)
        requires
            Self::global_wf(old(gs)),
            !Self::zone_ids(old(gs)).contains(zid),
            zone.wf(Self::alloc_inst_id(old(gs))),
            Self::zone_authorized(old(gs), zid, zone),
        ensures
            Self::global_wf(gs),
            Self::inst_id(gs) == Self::inst_id(old(gs)),
            zt.zone_id() == zid,
            zt.ghost_zone() == zone,
            zt.wf(Self::inst_id(gs)),
            Self::zone_ids(gs) =~= Self::zone_ids(old(gs)).insert(zid),
    ;

    /// Deregister a zone; consumes its zone token.
    proof fn remove_zone(tracked gs: &mut Self::GlobalState, tracked zt: Self::ZoneToken)
        requires
            Self::global_wf(old(gs)),
            zt.wf(Self::inst_id(old(gs))),
        ensures
            Self::global_wf(gs),
            Self::inst_id(gs) == Self::inst_id(old(gs)),
            Self::zone_ids(gs) =~= Self::zone_ids(old(gs)).remove(zt.zone_id()),
    ;

    /// Insert a region into a zone and return the updated zone token.
    ///
    /// The region must pass three conditions:
    /// - `!zt.ghost_zone().contains_region(region)`: no duplicate insert.
    /// - `!zt.ghost_zone().mem_set.overlaps_vmem(region)`: no virtual-address clash.
    /// - `Self::region_authorized(...)`: protocol-specific membership check
    ///   (`all_regions` + not in closure for ClosureProtocol; `zone_budget` for BudgetProtocol).
    ///
    /// For `BudgetProtocol` the `gs` argument is not modified (zone-local transition).
    proof fn insert_region(
        tracked gs: &mut Self::GlobalState,
        tracked zt: Self::ZoneToken,
        region: MemoryRegion,
    ) -> (tracked new_zt: Self::ZoneToken)
        requires
            Self::global_wf(old(gs)),
            zt.wf(Self::inst_id(old(gs))),
            !zt.ghost_zone().contains_region(region),
            !zt.ghost_zone().mem_set.overlaps_vmem(region),
            Self::region_authorized(old(gs), &zt, region),
        ensures
            Self::global_wf(gs),
            Self::inst_id(gs) == Self::inst_id(old(gs)),
            new_zt.zone_id() == zt.zone_id(),
            new_zt.wf(Self::inst_id(gs)),
            new_zt.ghost_zone() == zt.ghost_zone().insert_region(region),
    ;

    /// Remove a region from a zone and return the updated zone token.
    proof fn remove_region(
        tracked gs: &mut Self::GlobalState,
        tracked zt: Self::ZoneToken,
        region: MemoryRegion,
    ) -> (tracked new_zt: Self::ZoneToken)
        requires
            Self::global_wf(old(gs)),
            zt.wf(Self::inst_id(old(gs))),
            zt.ghost_zone().contains_region(region),
        ensures
            Self::global_wf(gs),
            Self::inst_id(gs) == Self::inst_id(old(gs)),
            new_zt.zone_id() == zt.zone_id(),
            new_zt.wf(Self::inst_id(gs)),
            new_zt.ghost_zone() == zt.ghost_zone().remove_region(region),
    ;
}

} // verus!
