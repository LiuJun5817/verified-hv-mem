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

pub use budget::{BudgetGlobalState, BudgetProtocol, BudgetZoneState};
pub use closure::{ClosureGlobalState, ClosureProtocol, ClosureZoneState};

use super::spec::ZoneStateOps;
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
/// | Impl              | `ZoneToken`       | `GlobalState`       | Lock for insert    |
/// |-------------------|-------------------|---------------------|--------------------|
/// | `ClosureProtocol` | `ZoneState`       | `ClosureGlobalState`| global + zone lock |
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
    spec fn mem_inst_id(gs: &Self::GlobalState) -> InstanceId;

    /// The current set of registered zone IDs.
    spec fn zone_ids(gs: &Self::GlobalState) -> Set<nat>;

    /// Policy-specific authorization predicate for inserting a region.
    ///
    /// `ClosureProtocol`: `region` is in `all_regions()` and not yet in the closure.
    /// `BudgetProtocol`: `region` is in `zone_budget(zt.zone_id())`.
    spec fn region_authorized(
        gs: &Self::GlobalState,
        zt: &Self::ZoneToken,
        region: MemoryRegion,
    ) -> bool;

    // ─── Proof transitions ────────────────────────────────────────────────────
    /// Register a new empty zone; returns a fresh zone token.
    ///
    /// The zone starts with no regions; use `insert_region` to populate it.
    proof fn add_zone(tracked gs: &mut Self::GlobalState, zid: nat) -> (tracked zt: Self::ZoneToken)
        requires
            Self::global_wf(old(gs)),
            !Self::zone_ids(old(gs)).contains(zid),
        ensures
            Self::global_wf(gs),
            Self::mem_inst_id(gs) == Self::mem_inst_id(old(gs)),
            zt.zone_id() == zid,
            zt.ghost_zone().regions() =~= Set::empty(),
            zt.wf(Self::mem_inst_id(gs)),
            Self::zone_ids(gs) =~= Self::zone_ids(old(gs)).insert(zid),
    ;

    /// Deregister a zone; consumes its zone token.
    proof fn remove_zone(tracked gs: &mut Self::GlobalState, tracked zt: Self::ZoneToken)
        requires
            Self::global_wf(old(gs)),
            zt.wf(Self::mem_inst_id(old(gs))),
        ensures
            Self::global_wf(gs),
            Self::mem_inst_id(gs) == Self::mem_inst_id(old(gs)),
            Self::zone_ids(gs) =~= Self::zone_ids(old(gs)).remove(zt.zone_id()),
    ;
}

} // verus!
