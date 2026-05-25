//! Assumption-1 (weak / ClosureSpec) ghost state and policy.
//!
//! - [`ClosureGlobalState`]: global tracked ghost state (ClosureSpec instance +
//!   `zone_ids` + `region_closure` tokens).
//! - [`ClosurePolicy`]: `HvMemPolicy` implementation for assumption 1.
use super::super::spec::{
    all_regions, ClosureRegionToken, ClosureSpecInstance, ClosureZoneIdsToken, ClosureZoneToken,
    GhostZone, ZoneStateOps,
};
use super::HvMemPolicy;
use crate::address::region::MemoryRegion;
use vstd::{prelude::*, tokens::InstanceId};

verus! {

/// Per-zone tracked ghost state, holding the zone's entry in `ClosureSpec::zones`.
///
/// One `ClosureZoneState` is created for each zone when it is added via `ClosureGlobalState::add_zone`,
/// and consumed when the zone is removed via `ClosureGlobalState::remove_zone`.
///
/// `ClosureZoneState` is typically stored inside the zone-level lock, so that only the thread
/// holding the zone lock can invoke `insert_region`/`remove_region`.
pub tracked struct ClosureZoneState {
    pub zone_tok: ClosureZoneToken,
}

impl ClosureZoneState {
    /// Well-formedness: the zone token belongs to the given `ClosureSpec` instance.
    pub open spec fn wf(&self, alloc_inst_id: InstanceId) -> bool {
        self.zone_tok.instance_id() == alloc_inst_id
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

impl ZoneStateOps for ClosureZoneState {
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

// ─── ClosureGlobalState ──────────────────────────────────────────────────────────────
/// Global tracked ghost state held by the hypervisor memory manager under
/// assumption 1 (ClosureSpec).
///
/// Wraps the `ClosureSpec` instance and the variable-sharded tokens
/// (`zone_ids`, `region_closure`) that are not distributed to individual zones.
///
/// Typically stored inside a `Mutex`/write-lock so that `add_zone`/`remove_zone`
/// are mutually exclusive.  Per-zone `ZoneState` tokens are distributed to
/// zone-level locks independently, mirroring the `AllocatorState`/`ClientState`
/// split in `global_allocator`.
pub tracked struct ClosureGlobalState {
    pub inst: ClosureSpecInstance,
    pub zone_ids_tok: ClosureZoneIdsToken,
    pub region_closure_tok: ClosureRegionToken,
}

impl ClosureGlobalState {
    /// Core well-formedness: all tokens belong to the same `ClosureSpec` instance.
    pub open spec fn wf(&self) -> bool {
        &&& self.zone_ids_tok.instance_id() == self.inst.id()
        &&& self.region_closure_tok.instance_id() == self.inst.id()
    }

    /// The `ClosureSpec` instance ID.
    pub open spec fn inst_id(&self) -> InstanceId {
        self.inst.id()
    }

    /// The current set of registered zone IDs.
    pub open spec fn zone_ids(&self) -> Set<nat> {
        self.zone_ids_tok.value()
    }

    /// The current global region closure.
    pub open spec fn region_closure(&self) -> Set<MemoryRegion> {
        self.region_closure_tok.value()
    }

    /// Construct an initial (empty) `ClosureGlobalState` from a freshly-created `ClosureSpec`
    /// instance. Callers obtain the tokens from `ClosureSpec::Instance::initialize`.
    pub proof fn new(
        tracked inst: ClosureSpecInstance,
        tracked zone_ids_tok: ClosureZoneIdsToken,
        tracked region_closure_tok: ClosureRegionToken,
    ) -> (tracked state: ClosureGlobalState)
        requires
            zone_ids_tok.instance_id() == inst.id(),
            zone_ids_tok.value() =~= Set::empty(),
            region_closure_tok.instance_id() == inst.id(),
            region_closure_tok.value() =~= Set::empty(),
        ensures
            state.wf(),
            state.inst_id() == inst.id(),
            state.zone_ids() =~= Set::empty(),
            state.region_closure() =~= Set::empty(),
    {
        ClosureGlobalState { inst, zone_ids_tok, region_closure_tok }
    }

    /// Add a fully constructed zone to the system.
    ///
    /// The caller must prove every region in `zone` belongs to `all_regions()` (static
    /// configuration membership) and is not already in the current `region_closure`
    /// (no duplicate ownership).  Disjointness from the existing closure then follows
    /// automatically from `all_regions_disjoint()`.  Returns a fresh `ZoneState` token
    /// for the new zone, which should be stored inside the zone-level lock.
    pub proof fn add_zone(tracked &mut self, zid: nat, zone: GhostZone) -> (tracked zone_state:
        ClosureZoneState)
        requires
            old(self).wf(),
            !old(self).zone_ids().contains(zid),
            zone.wf(old(self).inst.alloc_inst_id()),
            forall|r: MemoryRegion| #[trigger]
                zone.regions().contains(r) ==> all_regions().contains(r),
            forall|r: MemoryRegion| #[trigger]
                zone.regions().contains(r) ==> !old(self).region_closure().contains(r),
        ensures
            self.wf(),
            self.inst_id() == old(self).inst_id(),
            self.zone_ids() =~= old(self).zone_ids().insert(zid),
            self.region_closure() =~= old(self).region_closure().union(zone.regions()),
            zone_state.wf(self.inst_id()),
            zone_state.zone_id() == zid,
            zone_state.ghost_zone() == zone,
    {
        let tracked zone_tok = self.inst.add_zone(
            zid,
            zone,
            &mut self.zone_ids_tok,
            &mut self.region_closure_tok,
        );
        ClosureZoneState { zone_tok }
    }

    /// Remove an entire zone from the system, consuming its `ZoneState` token.
    ///
    /// The zone's regions are subtracted from `region_closure`.  Callers are
    /// responsible for draining page-table frames before invoking this.
    pub proof fn remove_zone(tracked &mut self, tracked zone_state: ClosureZoneState)
        requires
            old(self).wf(),
            zone_state.wf(old(self).inst_id()),
        ensures
            self.wf(),
            self.inst_id() == old(self).inst_id(),
            self.zone_ids() =~= old(self).zone_ids().remove(zone_state.zone_id()),
            self.region_closure() =~= old(self).region_closure().difference(
                zone_state.ghost_zone().regions(),
            ),
    {
        let tracked ClosureZoneState { zone_tok } = zone_state;
        let zid = zone_tok.key();
        self.inst.remove_zone(zid, &mut self.zone_ids_tok, zone_tok, &mut self.region_closure_tok);
    }

    /// Insert one region into an existing zone.
    ///
    /// Consumes `zone_state` and returns an updated `ZoneState` with the region
    /// added.  Also extends `region_closure` by `region`.
    ///
    /// The caller must prove `region` belongs to `all_regions()` (static configuration
    /// membership) and is not already in the current `region_closure` (no duplicate
    /// ownership).  Disjointness from all existing regions then follows automatically
    /// from `all_regions_disjoint()`.
    pub proof fn insert_region(
        tracked &mut self,
        tracked zone_state: ClosureZoneState,
        region: MemoryRegion,
    ) -> (tracked new_zone_state: ClosureZoneState)
        requires
            old(self).wf(),
            zone_state.wf(old(self).inst_id()),
            region.spec_valid(),
            all_regions().contains(region),
            !old(self).region_closure().contains(region),
            !zone_state.ghost_zone().mem_set.overlaps_vmem(region),
        ensures
            self.wf(),
            self.inst_id() == old(self).inst_id(),
            new_zone_state.wf(self.inst_id()),
            new_zone_state.zone_id() == zone_state.zone_id(),
            self.region_closure() =~= old(self).region_closure().insert(region),
            new_zone_state.ghost_zone() == zone_state.ghost_zone().insert_region(region),
    {
        let tracked ClosureZoneState { zone_tok } = zone_state;
        let zid = zone_tok.key();
        let tracked new_zone_tok = self.inst.insert_region(
            zid,
            region,
            zone_tok,
            &mut self.region_closure_tok,
        );
        ClosureZoneState { zone_tok: new_zone_tok }
    }

    /// Remove one region from an existing zone.
    ///
    /// Consumes `zone_state` and returns an updated `ZoneState` with the region
    /// removed.  Also shrinks `region_closure` by `region`.
    pub proof fn remove_region(
        tracked &mut self,
        tracked zone_state: ClosureZoneState,
        region: MemoryRegion,
    ) -> (tracked new_zone_state: ClosureZoneState)
        requires
            old(self).wf(),
            zone_state.wf(old(self).inst_id()),
            zone_state.ghost_zone().contains_region(region),
        ensures
            self.wf(),
            self.inst_id() == old(self).inst_id(),
            new_zone_state.wf(self.inst_id()),
            new_zone_state.zone_id() == zone_state.zone_id(),
            self.region_closure() =~= old(self).region_closure().remove(region),
            new_zone_state.ghost_zone() == zone_state.ghost_zone().remove_region(region),
    {
        let tracked ClosureZoneState { zone_tok } = zone_state;
        let zid = zone_tok.key();
        let tracked new_zone_tok = self.inst.remove_region(
            zid,
            region,
            zone_tok,
            &mut self.region_closure_tok,
        );
        ClosureZoneState { zone_tok: new_zone_tok }
    }
}

// ─── ClosurePolicy ───────────────────────────────────────────────────────────
/// Assumption-1 (ClosureSpec) policy marker.
///
/// When `P = ClosurePolicy`:
/// - `Zone<PT, M, A, ClosurePolicy>` holds a `ZoneState` ghost token.
/// - `HvMem<PT, M, A, ClosurePolicy>` holds `ClosureGlobalState` as global state.
/// - `insert_region` requires holding the HvMem **write lock** (because
///   `ClosureGlobalState::region_closure_tok` must be updated globally).
pub struct ClosurePolicy;

impl HvMemPolicy for ClosurePolicy {
    type ZoneToken = ClosureZoneState;

    type GlobalState = ClosureGlobalState;

    open spec fn global_wf(gs: &ClosureGlobalState) -> bool {
        gs.wf()
    }

    open spec fn inst_id(gs: &ClosureGlobalState) -> InstanceId {
        gs.inst_id()
    }

    open spec fn zone_ids(gs: &ClosureGlobalState) -> Set<nat> {
        gs.zone_ids()
    }

    open spec fn alloc_inst_id(gs: &ClosureGlobalState) -> InstanceId {
        gs.inst.alloc_inst_id()
    }

    open spec fn zone_authorized(gs: &ClosureGlobalState, zid: nat, zone: GhostZone) -> bool {
        &&& (forall|r: MemoryRegion| #[trigger] zone.regions().contains(r) ==> all_regions().contains(r))
        &&& (forall|r: MemoryRegion| #[trigger] zone.regions().contains(r) ==> !gs.region_closure().contains(r))
    }

    open spec fn region_authorized(gs: &ClosureGlobalState, zt: &ClosureZoneState, region: MemoryRegion) -> bool {
        &&& region.spec_valid()
        &&& all_regions().contains(region)
        &&& !gs.region_closure().contains(region)
    }

    proof fn add_zone(
        tracked gs: &mut ClosureGlobalState,
        zid: nat,
        zone: GhostZone,
    ) -> (tracked zt: ClosureZoneState) {
        // All ClosureGlobalState::add_zone preconditions are satisfied by the
        // trait requires: global_wf, !zone_ids.contains, zone.wf(alloc_inst_id),
        // zone_authorized (covers all_regions + !region_closure conditions).
        gs.add_zone(zid, zone)
    }

    proof fn remove_zone(tracked gs: &mut ClosureGlobalState, tracked zt: ClosureZoneState) {
        gs.remove_zone(zt)
    }

    proof fn insert_region(
        tracked gs: &mut ClosureGlobalState,
        tracked zt: ClosureZoneState,
        region: MemoryRegion,
    ) -> (tracked new_zt: ClosureZoneState) {
        // All ClosureGlobalState::insert_region preconditions are satisfied:
        // region_authorized covers spec_valid + all_regions + !region_closure;
        // !overlaps_vmem comes from the trait requires.
        gs.insert_region(zt, region)
    }

    proof fn remove_region(
        tracked gs: &mut ClosureGlobalState,
        tracked zt: ClosureZoneState,
        region: MemoryRegion,
    ) -> (tracked new_zt: ClosureZoneState) {
        gs.remove_region(zt, region)
    }
}

} // verus!
