//! Assumption-2 (strong / BudgetSpec) ghost state and policy.
//!
//! - [`BudgetGlobalState`]: global tracked ghost state (BudgetSpec instance + `zone_ids` token).
//! - [`BudgetPolicy`]: `HvMemPolicy` implementation for assumption 2.
//!
//! `insert_region` under `BudgetPolicy` is zone-local: only the `BudgetSpec::zones[zid]`
//! map-sharded token is updated, so **no global HvMem write lock is required**.
use super::super::spec::{
    budget::{BudgetSpecInstance, BudgetZoneIdsToken},
    GhostZone,
};
use super::super::zone::BudgetZoneState;
use super::HvMemPolicy;
use crate::address::region::MemoryRegion;
use vstd::prelude::*;

verus! {

// ─── BudgetGlobalState ───────────────────────────────────────────────────────
/// Global tracked ghost state for assumption-2 (BudgetSpec).
///
/// Unlike `ClosureGlobalState`, there is no `region_closure_tok` here because
/// `BudgetSpec` tracks ownership via a static per-zone budget function
/// (`zone_budget`) rather than a dynamic global set.  As a result,
/// `insert_region` does **not** need to acquire the `HvMem` write lock.
pub tracked struct BudgetGlobalState {
    /// The `BudgetSpec` instance (constant-sharded; freely duplicable ghost value).
    pub inst: BudgetSpecInstance,
    /// Variable-sharded token tracking the current set of registered zone IDs.
    pub zone_ids_tok: BudgetZoneIdsToken,
}

impl BudgetGlobalState {
    pub open spec fn wf(&self) -> bool {
        self.zone_ids_tok.instance_id() == self.inst.id()
    }

    pub open spec fn inst_id(&self) -> vstd::tokens::InstanceId {
        self.inst.id()
    }

    pub open spec fn zone_ids(&self) -> Set<nat> {
        self.zone_ids_tok.value()
    }
}

// ─── BudgetPolicy ────────────────────────────────────────────────────────────
/// Assumption-2 (BudgetSpec) policy marker.
///
/// When `P = BudgetPolicy`:
/// - `Zone<PT, M, A, BudgetPolicy>` holds a `BudgetZoneState` ghost token.
/// - `HvMem<PT, M, A, BudgetPolicy>` holds `BudgetGlobalState` as global state.
/// - `insert_region` is **zone-local**: `gs` (global state) is not modified,
///   so the HvMem write lock does **not** need to be held for insertion.
///   This is the key performance benefit of assumption 2.
pub struct BudgetPolicy;

impl HvMemPolicy for BudgetPolicy {
    type ZoneToken = BudgetZoneState;

    type GlobalState = BudgetGlobalState;

    open spec fn global_wf(gs: &BudgetGlobalState) -> bool {
        gs.wf()
    }

    open spec fn inst_id(gs: &BudgetGlobalState) -> vstd::tokens::InstanceId {
        gs.inst_id()
    }

    open spec fn zone_ids(gs: &BudgetGlobalState) -> Set<nat> {
        gs.zone_ids()
    }

    proof fn add_zone(tracked gs: &mut BudgetGlobalState, zid: nat, zone: GhostZone) -> (tracked zt:
        BudgetZoneState) {
        let tracked zone_tok = gs.inst.add_zone(zid, zone, &mut gs.zone_ids_tok);
        admit();
        BudgetZoneState { zone_tok }
    }

    proof fn remove_zone(tracked gs: &mut BudgetGlobalState, tracked zt: BudgetZoneState) {
        let zid = zt.zone_id();
        let tracked BudgetZoneState { zone_tok } = zt;
        gs.inst.remove_zone(zid, &mut gs.zone_ids_tok, zone_tok);
        admit();
    }

    proof fn insert_region(
        tracked gs: &mut BudgetGlobalState,
        tracked zt: BudgetZoneState,
        region: MemoryRegion,
    ) -> (tracked new_zt: BudgetZoneState) {
        // Zone-local: only the BudgetSpec::zones[zid] token is updated.
        // gs (holding zone_ids_tok) is not touched — no global lock needed.
        let zid = zt.zone_id();
        let tracked new_tok = gs.inst.insert_region(zid, region, zt.zone_tok);
        admit();
        BudgetZoneState { zone_tok: new_tok }
    }

    proof fn remove_region(
        tracked gs: &mut BudgetGlobalState,
        tracked zt: BudgetZoneState,
        region: MemoryRegion,
    ) -> (tracked new_zt: BudgetZoneState) {
        let zid = zt.zone_id();
        let tracked new_tok = gs.inst.remove_region(zid, region, zt.zone_tok);
        admit();
        BudgetZoneState { zone_tok: new_tok }
    }
}

} // verus!
