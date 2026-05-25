//! Assumption-2 (strong / BudgetSpec) ghost state and protocol.
//!
//! - [`BudgetGlobalState`]: global tracked ghost state (BudgetSpec instance + `zone_ids` token).
//! - [`BudgetProtocol`]: `HvMemProtocol` implementation for assumption 2.
//!
//! `insert_region` under `BudgetProtocol` is zone-local: only the `BudgetSpec::zones[zid]`
//! map-sharded token is updated, so **no global HvMem write lock is required**.
use super::super::spec::{
    budget::{zone_budget, BudgetSpecInstance, BudgetZoneIdsToken, BudgetZoneToken},
    GhostZone, ZoneStateOps,
};
use super::HvMemProtocol;
use crate::address::region::MemoryRegion;
use vstd::prelude::*;

verus! {

/// Per-zone tracked ghost state for `BudgetSpec` (assumption 2).
///
/// Parallel to `ZoneState` for `ClosureSpec`, but wraps a `BudgetZoneToken`
/// (map-sharded `BudgetSpec::zones` entry) instead of a `ClosureZoneToken`.
/// Stored in the zone-level lock alongside no budget token — the budget is
/// accessed as the pure spec function `zone_budget(zid)` instead.
pub tracked struct BudgetZoneState {
    pub zone_tok: BudgetZoneToken,
}

impl BudgetZoneState {
    /// Well-formedness: the zone token belongs to the given `BudgetSpec` instance.
    pub open spec fn wf(&self, inst_id: InstanceId) -> bool {
        self.zone_tok.instance_id() == inst_id
    }

    /// The zone ID (key in the `zones` map sharding).
    pub open spec fn zone_id(&self) -> nat {
        self.zone_tok.key()
    }

    /// The ghost zone state (value in the `zones` map sharding).
    pub open spec fn ghost_zone(&self) -> GhostZone {
        self.zone_tok.value()
    }
}

impl ZoneStateOps for BudgetZoneState {
    open spec fn zone_id(&self) -> nat {
        self.zone_tok.key()
    }

    open spec fn ghost_zone(&self) -> GhostZone {
        self.zone_tok.value()
    }

    open spec fn wf(&self, inst_id: InstanceId) -> bool {
        self.zone_tok.instance_id() == inst_id
    }
}

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

// ─── BudgetProtocol ────────────────────────────────────────────────────────────
/// Assumption-2 (BudgetSpec) protocol marker.
///
/// When `P = BudgetProtocol`:
/// - `Zone<PT, M, A, BudgetProtocol>` holds a `BudgetZoneState` ghost token.
/// - `HvMem<PT, M, A, BudgetProtocol>` holds `BudgetGlobalState` as global state.
/// - `insert_region` is **zone-local**: `gs` (global state) is not modified,
///   so the HvMem write lock does **not** need to be held for insertion.
///   This is the key performance benefit of assumption 2.
pub struct BudgetProtocol;

impl HvMemProtocol for BudgetProtocol {
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

    open spec fn alloc_inst_id(gs: &BudgetGlobalState) -> InstanceId {
        gs.inst.alloc_inst_id()
    }

    open spec fn zone_authorized(gs: &BudgetGlobalState, zid: nat, zone: GhostZone) -> bool {
        forall|r: MemoryRegion| #[trigger] zone.regions().contains(r) ==> zone_budget(zid).contains(r)
    }

    open spec fn region_authorized(gs: &BudgetGlobalState, zt: &BudgetZoneState, region: MemoryRegion) -> bool {
        zone_budget(zt.zone_id()).contains(region)
    }

    proof fn add_zone(tracked gs: &mut BudgetGlobalState, zid: nat, zone: GhostZone) -> (tracked zt:
        BudgetZoneState) {
        // All BudgetSpec::add_zone preconditions are satisfied:
        // !zone_ids.contains(zid), zone.wf(alloc_inst_id), zone_authorized (budget membership).
        let tracked zone_tok = gs.inst.add_zone(zid, zone, &mut gs.zone_ids_tok);
        BudgetZoneState { zone_tok }
    }

    proof fn remove_zone(tracked gs: &mut BudgetGlobalState, tracked zt: BudgetZoneState) {
        let zid = zt.zone_id();
        let tracked BudgetZoneState { zone_tok } = zt;
        gs.inst.remove_zone(zid, &mut gs.zone_ids_tok, zone_tok);
    }

    proof fn insert_region(
        tracked gs: &mut BudgetGlobalState,
        tracked zt: BudgetZoneState,
        region: MemoryRegion,
    ) -> (tracked new_zt: BudgetZoneState) {
        // Zone-local: only the BudgetSpec::zones[zid] token is updated.
        // gs (holding zone_ids_tok) is not touched — no global lock needed.
        // All BudgetSpec::insert_region preconditions are satisfied:
        // zone_budget membership from region_authorized, !contains_region and
        // !overlaps_vmem from the trait requires.
        let zid = zt.zone_id();
        let tracked new_tok = gs.inst.insert_region(zid, region, zt.zone_tok);
        BudgetZoneState { zone_tok: new_tok }
    }

    proof fn remove_region(
        tracked gs: &mut BudgetGlobalState,
        tracked zt: BudgetZoneState,
        region: MemoryRegion,
    ) -> (tracked new_zt: BudgetZoneState) {
        let zid = zt.zone_id();
        let tracked new_tok = gs.inst.remove_region(zid, region, zt.zone_tok);
        BudgetZoneState { zone_tok: new_tok }
    }
}

} // verus!
