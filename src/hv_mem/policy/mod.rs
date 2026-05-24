//! Region-assignment policy abstraction.
//!
//! Abstracts over the two safety assumptions (`ClosureSpec` / `BudgetSpec`) so that
//! `Zone` and `HvMem` are generic over `P: HvMemPolicy` rather than hard-wired.
//!
//! Submodules:
//! - [`weak`]:   assumption-1 ghost state (`ClosureGlobalState`) and `ClosurePolicy`.
//! - [`strong`]: assumption-2 ghost state (`BudgetGlobalState`) and `BudgetPolicy`.
pub mod budget;
pub mod closure;

pub use budget::{BudgetGlobalState, BudgetPolicy};
pub use closure::{ClosureGlobalState, ClosurePolicy};

use super::spec::{GhostZone, ZoneStateOps};
use crate::address::region::MemoryRegion;
use vstd::prelude::*;

verus! {

/// Top-level exec policy trait that unifies `ClosureSpec` (assumption 1) and
/// `BudgetSpec` (assumption 2) under a single generic interface.
///
/// `Zone<PT, M, A, P>` and `HvMem<PT, M, A, P>` are parameterized by `P: HvMemPolicy`.
/// Swapping `P` switches the entire ghost-state bookkeeping strategy without changing
/// any exec code.
///
/// | Impl            | `ZoneToken`       | `GlobalState`       | Lock for insert    |
/// |-----------------|-------------------|---------------------|--------------------|
/// | `ClosurePolicy` | `ZoneState`       | `ClosureGlobalState`        | global + zone lock |
/// | `BudgetPolicy`  | `BudgetZoneState` | `BudgetGlobalState` | zone lock only     |
pub trait HvMemPolicy: Sized {
    /// Per-zone tracked ghost state (map-sharded token from `zones[zid]`).
    type ZoneToken: ZoneStateOps;

    /// Global tracked ghost state stored inside `HvMem`'s write-lock content.
    ///
    /// `ClosurePolicy`: `ClosureGlobalState` (holds `region_closure_tok` — global write lock required).
    /// `BudgetPolicy`:  `BudgetGlobalState` (no `region_closure_tok` — zone-local insert).
    type GlobalState;

    // ─── Spec predicates ─────────────────────────────────────────────────────
    /// Well-formedness: all internal tokens are consistent with each other.
    spec fn global_wf(gs: &Self::GlobalState) -> bool;

    /// The spec-instance ID embedded in the global state.
    spec fn inst_id(gs: &Self::GlobalState) -> InstanceId;

    /// The current set of registered zone IDs.
    spec fn zone_ids(gs: &Self::GlobalState) -> Set<nat>;

    // ─── Proof transitions ────────────────────────────────────────────────────
    /// Register a new zone; returns a fresh zone token.
    proof fn add_zone(tracked gs: &mut Self::GlobalState, zid: nat, zone: GhostZone) -> (tracked zt:
        Self::ZoneToken)
        requires
            Self::global_wf(old(gs)),
            !Self::zone_ids(old(gs)).contains(zid),
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
    /// Authorization (`all_regions` or `zone_budget`) is checked at the
    /// Authorization is admitted here; discharge via `HvMemPolicy` preconditions.
    /// For `BudgetPolicy` the `gs` argument is not modified (zone-local transition).
    proof fn insert_region(
        tracked gs: &mut Self::GlobalState,
        tracked zt: Self::ZoneToken,
        region: MemoryRegion,
    ) -> (tracked new_zt: Self::ZoneToken)
        requires
            Self::global_wf(old(gs)),
            zt.wf(Self::inst_id(old(gs))),
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
