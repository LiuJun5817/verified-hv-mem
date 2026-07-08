//! Assumption-1 (weak / ClosureSpec) ghost state and protocol.
//!
//! - [`ClosureGlobalState`]: global tracked ghost state (ClosureSpec instance +
//!   `zone_ids` plus the prototype `zones_view` token).
//! - [`ClosureProtocol`]: `ZoneGhostProtocol` implementation for assumption 1.
use super::super::spec::{
    all_regions, cpu_insert_region_allowed, iommu_insert_region_allowed, ClosureSpecInstance,
    ClosureZoneIdsToken, ClosureZoneToken, ClosureZonesViewToken, GhostZone,
};
use super::{ZoneGhostProtocol, ZoneStateOps};
use crate::address::region::MemoryRegion;
use crate::memory_set::SpecMemorySet;
use vstd::{prelude::*, tokens::InstanceId};

verus! {

/// Per-zone tracked ghost state, holding the zone's entry in `ClosureSpec::zones`.
///
/// One `ClosureZoneState` is created for each zone when it is added via
/// `ClosureGlobalState::add_zone`, and consumed when the zone is removed via
/// `ClosureGlobalState::remove_zone`.
///
/// `ClosureZoneState` is typically stored inside the zone-level lock, so that
/// only the thread holding the zone lock can invoke region operations.
pub tracked struct ClosureZoneState {
    pub zone_tok: ClosureZoneToken,
}

impl ZoneStateOps for ClosureZoneState {
    /// The zone ID (key in the `zones` map sharding).
    open spec fn zone_id(&self) -> nat {
        self.zone_tok.key()
    }

    /// The ghost zone state (value in the `zones` map sharding).
    open spec fn ghost_zone(&self) -> GhostZone {
        self.zone_tok.value()
    }

    /// Well-formedness: the zone token belongs to the given `ClosureSpec` instance.
    open spec fn wf(&self, mem_inst_id: InstanceId) -> bool {
        self.zone_tok.instance_id() == mem_inst_id
    }
}

// ─── ClosureGlobalState ──────────────────────────────────────────────────────
/// Global tracked ghost state held by the hypervisor memory manager under
/// assumption 1 (`ClosureSpec`).
///
/// The old CPU/IOMMU region-closure tokens are intentionally gone. The prototype
/// keeps one `zones_view` mirror token so transitions can state global overlap
/// guards while zone ownership still lives in map-sharded per-zone tokens.
pub tracked struct ClosureGlobalState {
    pub inst: ClosureSpecInstance,
    pub zone_ids_tok: ClosureZoneIdsToken,
    pub zones_view_tok: ClosureZonesViewToken,
}

impl ClosureGlobalState {
    /// Core well-formedness: all tokens belong to the same `ClosureSpec` instance.
    pub open spec fn wf(&self) -> bool {
        &&& self.zone_ids_tok.instance_id() == self.inst.id()
        &&& self.zones_view_tok.instance_id() == self.inst.id()
    }

    /// The `ClosureSpec` instance ID.
    pub open spec fn mem_inst_id(&self) -> InstanceId {
        self.inst.id()
    }

    /// The current set of registered zone IDs.
    pub open spec fn zone_ids(&self) -> Set<nat> {
        self.zone_ids_tok.value()
    }

    /// Global mirror of all zone states, used by ClosureSpec insertion guards.
    pub open spec fn zones_view(&self) -> Map<nat, GhostZone> {
        self.zones_view_tok.value()
    }

    /// Construct an initial (empty) `ClosureGlobalState` from a freshly-created
    /// `ClosureSpec` instance. Callers obtain the tokens from
    /// `ClosureSpec::Instance::initialize`.
    pub proof fn new(
        tracked inst: ClosureSpecInstance,
        tracked zone_ids_tok: ClosureZoneIdsToken,
        tracked zones_view_tok: ClosureZonesViewToken,
    ) -> (tracked state: ClosureGlobalState)
        requires
            zone_ids_tok.instance_id() == inst.id(),
            zone_ids_tok.value() =~= Set::empty(),
            zones_view_tok.instance_id() == inst.id(),
            zones_view_tok.value() =~= Map::empty(),
        ensures
            state.wf(),
            state.mem_inst_id() == inst.id(),
            state.zone_ids() =~= Set::empty(),
            state.zones_view() =~= Map::empty(),
    {
        ClosureGlobalState { inst, zone_ids_tok, zones_view_tok }
    }

    /// Add an empty zone to the system.
    ///
    /// Returns a fresh `ClosureZoneState` token for the new zone.
    /// The zone starts with no regions; use region insertions to populate it.
    pub proof fn add_zone(tracked &mut self, zid: nat) -> (tracked zone_state: ClosureZoneState)
        requires
            old(self).wf(),
            !old(self).zone_ids().contains(zid),
        ensures
            self.wf(),
            self.mem_inst_id() == old(self).mem_inst_id(),
            self.zone_ids() =~= old(self).zone_ids().insert(zid),
            self.zones_view() =~= old(self).zones_view().insert(zid, zone_state.ghost_zone()),
            zone_state.wf(self.mem_inst_id()),
            zone_state.zone_id() == zid,
            zone_state.ghost_zone().regions() =~= Set::empty(),
            zone_state.ghost_zone() == (GhostZone {
                cpu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
                iommu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
            }),
    {
        let tracked zone_tok = self.inst.add_zone(
            zid,
            &mut self.zone_ids_tok,
            &mut self.zones_view_tok,
        );
        ClosureZoneState { zone_tok }
    }

    /// Remove an entire zone from the system, consuming its `ZoneState` token.
    ///
    /// Callers are responsible for draining page-table frames before invoking this.
    pub proof fn remove_zone(tracked &mut self, tracked zone_state: ClosureZoneState)
        requires
            old(self).wf(),
            zone_state.wf(old(self).mem_inst_id()),
        ensures
            self.wf(),
            self.mem_inst_id() == old(self).mem_inst_id(),
            self.zone_ids() =~= old(self).zone_ids().remove(zone_state.zone_id()),
            self.zones_view() =~= old(self).zones_view().remove(zone_state.zone_id()),
    {
        let tracked ClosureZoneState { zone_tok } = zone_state;
        let zid = zone_tok.key();
        self.inst.remove_zone(zid, &mut self.zone_ids_tok, zone_tok, &mut self.zones_view_tok);
    }

    /// Insert one CPU-visible region into an existing zone.
    ///
    /// The guard is intentionally global: the region must be configured, disjoint
    /// from the GIC, and disjoint from all existing CPU regions plus other-zone
    /// IOMMU regions.
    pub proof fn cpu_insert_region(
        tracked &mut self,
        tracked zone_state: ClosureZoneState,
        region: MemoryRegion,
    ) -> (tracked new_zone_state: ClosureZoneState)
        requires
            old(self).wf(),
            zone_state.wf(old(self).mem_inst_id()),
            region.spec_valid(),
            cpu_insert_region_allowed(old(self).zones_view(), zone_state.zone_id(), region),
            !zone_state.ghost_zone().cpu_mem_set.regions.contains(region),
            !zone_state.ghost_zone().cpu_mem_set.overlaps_vmem(region),
        ensures
            self.wf(),
            self.mem_inst_id() == old(self).mem_inst_id(),
            self.zone_ids() == old(self).zone_ids(),
            new_zone_state.wf(self.mem_inst_id()),
            new_zone_state.zone_id() == zone_state.zone_id(),
            self.zones_view() =~= old(self).zones_view().insert(
                zone_state.zone_id(),
                zone_state.ghost_zone().cpu_insert_region(region),
            ),
            new_zone_state.ghost_zone() == zone_state.ghost_zone().cpu_insert_region(region),
    {
        let tracked ClosureZoneState { zone_tok } = zone_state;
        let zid = zone_tok.key();
        let tracked new_zone_tok = self.inst.cpu_insert_region(
            zid,
            region,
            zone_tok,
            &mut self.zones_view_tok,
        );
        ClosureZoneState { zone_tok: new_zone_tok }
    }

    /// Remove one CPU-visible region from an existing zone.
    pub proof fn cpu_remove_region(
        tracked &mut self,
        tracked zone_state: ClosureZoneState,
        region: MemoryRegion,
    ) -> (tracked new_zone_state: ClosureZoneState)
        requires
            old(self).wf(),
            zone_state.wf(old(self).mem_inst_id()),
            zone_state.ghost_zone().cpu_mem_set.regions.contains(region),
        ensures
            self.wf(),
            self.mem_inst_id() == old(self).mem_inst_id(),
            self.zone_ids() == old(self).zone_ids(),
            new_zone_state.wf(self.mem_inst_id()),
            new_zone_state.zone_id() == zone_state.zone_id(),
            self.zones_view() =~= old(self).zones_view().insert(
                zone_state.zone_id(),
                zone_state.ghost_zone().cpu_remove_region(region),
            ),
            new_zone_state.ghost_zone() == zone_state.ghost_zone().cpu_remove_region(region),
    {
        let tracked ClosureZoneState { zone_tok } = zone_state;
        let zid = zone_tok.key();
        let tracked new_zone_tok = self.inst.cpu_remove_region(
            zid,
            region,
            zone_tok,
            &mut self.zones_view_tok,
        );
        ClosureZoneState { zone_tok: new_zone_tok }
    }

    /// Insert one IOMMU-visible region into an existing zone.
    ///
    /// The GIC region is the only cross-zone sharing exception; same-zone
    /// CPU/IOMMU overlap is allowed.
    pub proof fn iommu_insert_region(
        tracked &mut self,
        tracked zone_state: ClosureZoneState,
        region: MemoryRegion,
    ) -> (tracked new_zone_state: ClosureZoneState)
        requires
            old(self).wf(),
            zone_state.wf(old(self).mem_inst_id()),
            region.spec_valid(),
            iommu_insert_region_allowed(old(self).zones_view(), zone_state.zone_id(), region),
            !zone_state.ghost_zone().iommu_mem_set.regions.contains(region),
            !zone_state.ghost_zone().iommu_mem_set.overlaps_vmem(region),
        ensures
            self.wf(),
            self.mem_inst_id() == old(self).mem_inst_id(),
            self.zone_ids() == old(self).zone_ids(),
            new_zone_state.wf(self.mem_inst_id()),
            new_zone_state.zone_id() == zone_state.zone_id(),
            self.zones_view() =~= old(self).zones_view().insert(
                zone_state.zone_id(),
                zone_state.ghost_zone().iommu_insert_region(region),
            ),
            new_zone_state.ghost_zone() == zone_state.ghost_zone().iommu_insert_region(region),
    {
        let tracked ClosureZoneState { zone_tok } = zone_state;
        let zid = zone_tok.key();
        let tracked new_zone_tok = self.inst.iommu_insert_region(
            zid,
            region,
            zone_tok,
            &mut self.zones_view_tok,
        );
        ClosureZoneState { zone_tok: new_zone_tok }
    }

    /// Remove one IOMMU-visible region from an existing zone.
    pub proof fn iommu_remove_region(
        tracked &mut self,
        tracked zone_state: ClosureZoneState,
        region: MemoryRegion,
    ) -> (tracked new_zone_state: ClosureZoneState)
        requires
            old(self).wf(),
            zone_state.wf(old(self).mem_inst_id()),
            zone_state.ghost_zone().iommu_mem_set.regions.contains(region),
        ensures
            self.wf(),
            self.mem_inst_id() == old(self).mem_inst_id(),
            self.zone_ids() == old(self).zone_ids(),
            new_zone_state.wf(self.mem_inst_id()),
            new_zone_state.zone_id() == zone_state.zone_id(),
            self.zones_view() =~= old(self).zones_view().insert(
                zone_state.zone_id(),
                zone_state.ghost_zone().iommu_remove_region(region),
            ),
            new_zone_state.ghost_zone() == zone_state.ghost_zone().iommu_remove_region(region),
    {
        let tracked ClosureZoneState { zone_tok } = zone_state;
        let zid = zone_tok.key();
        let tracked new_zone_tok = self.inst.iommu_remove_region(
            zid,
            region,
            zone_tok,
            &mut self.zones_view_tok,
        );
        ClosureZoneState { zone_tok: new_zone_tok }
    }
}

// ─── ClosureProtocol ─────────────────────────────────────────────────────────
/// Assumption-1 (`ClosureSpec`) protocol marker.
///
/// When `P = ClosureProtocol`:
/// - `Zone<PT, M, A, ClosureProtocol>` holds a `ClosureZoneState` ghost token.
/// - `HvMem<PT, M, A, ClosureProtocol>` holds `ClosureGlobalState` as global state.
/// - CPU/IOMMU region insertions consult the global `zones_view` token to enforce
///   the prototype's cross-zone overlap policy.
pub struct ClosureProtocol;

impl ZoneGhostProtocol for ClosureProtocol {
    type ZoneToken = ClosureZoneState;

    type GlobalState = ClosureGlobalState;

    open spec fn global_wf(gs: &ClosureGlobalState) -> bool {
        gs.wf()
    }

    open spec fn mem_inst_id(gs: &ClosureGlobalState) -> InstanceId {
        gs.mem_inst_id()
    }

    open spec fn zone_ids(gs: &ClosureGlobalState) -> Set<nat> {
        gs.zone_ids()
    }

    proof fn add_zone(tracked gs: &mut ClosureGlobalState, zid: nat) -> (tracked zt:
        ClosureZoneState) {
        gs.add_zone(zid)
    }

    proof fn remove_zone(tracked gs: &mut ClosureGlobalState, tracked zt: ClosureZoneState) {
        gs.remove_zone(zt)
    }
}

impl ClosureProtocol {
    /// Insert a CPU-visible region into a zone under `ClosureSpec`.
    pub proof fn cpu_insert_region(
        tracked gs: &mut ClosureGlobalState,
        tracked zt: ClosureZoneState,
        region: MemoryRegion,
    ) -> (tracked new_zt: ClosureZoneState)
        requires
            old(gs).wf(),
            zt.wf(old(gs).mem_inst_id()),
            region.spec_valid(),
            cpu_insert_region_allowed(old(gs).zones_view(), zt.zone_id(), region),
            !zt.ghost_zone().cpu_mem_set.regions.contains(region),
            !zt.ghost_zone().cpu_mem_set.overlaps_vmem(region),
        ensures
            gs.wf(),
            gs.mem_inst_id() == old(gs).mem_inst_id(),
            gs.zone_ids() == old(gs).zone_ids(),
            new_zt.zone_id() == zt.zone_id(),
            new_zt.wf(gs.mem_inst_id()),
            gs.zones_view() =~= old(gs).zones_view().insert(
                zt.zone_id(),
                zt.ghost_zone().cpu_insert_region(region),
            ),
            new_zt.ghost_zone() == zt.ghost_zone().cpu_insert_region(region),
    {
        gs.cpu_insert_region(zt, region)
    }

    /// Remove a CPU-visible region from a zone under `ClosureSpec`.
    pub proof fn cpu_remove_region(
        tracked gs: &mut ClosureGlobalState,
        tracked zt: ClosureZoneState,
        region: MemoryRegion,
    ) -> (tracked new_zt: ClosureZoneState)
        requires
            old(gs).wf(),
            zt.wf(old(gs).mem_inst_id()),
            zt.ghost_zone().cpu_mem_set.regions.contains(region),
        ensures
            gs.wf(),
            gs.mem_inst_id() == old(gs).mem_inst_id(),
            gs.zone_ids() == old(gs).zone_ids(),
            new_zt.zone_id() == zt.zone_id(),
            new_zt.wf(gs.mem_inst_id()),
            gs.zones_view() =~= old(gs).zones_view().insert(
                zt.zone_id(),
                zt.ghost_zone().cpu_remove_region(region),
            ),
            new_zt.ghost_zone() == zt.ghost_zone().cpu_remove_region(region),
    {
        gs.cpu_remove_region(zt, region)
    }

    /// Insert an IOMMU-visible region into a zone under `ClosureSpec`.
    pub proof fn iommu_insert_region(
        tracked gs: &mut ClosureGlobalState,
        tracked zt: ClosureZoneState,
        region: MemoryRegion,
    ) -> (tracked new_zt: ClosureZoneState)
        requires
            old(gs).wf(),
            zt.wf(old(gs).mem_inst_id()),
            region.spec_valid(),
            iommu_insert_region_allowed(old(gs).zones_view(), zt.zone_id(), region),
            !zt.ghost_zone().iommu_mem_set.regions.contains(region),
            !zt.ghost_zone().iommu_mem_set.overlaps_vmem(region),
        ensures
            gs.wf(),
            gs.mem_inst_id() == old(gs).mem_inst_id(),
            gs.zone_ids() == old(gs).zone_ids(),
            new_zt.zone_id() == zt.zone_id(),
            new_zt.wf(gs.mem_inst_id()),
            gs.zones_view() =~= old(gs).zones_view().insert(
                zt.zone_id(),
                zt.ghost_zone().iommu_insert_region(region),
            ),
            new_zt.ghost_zone() == zt.ghost_zone().iommu_insert_region(region),
    {
        gs.iommu_insert_region(zt, region)
    }

    /// Remove an IOMMU-visible region from a zone under `ClosureSpec`.
    pub proof fn iommu_remove_region(
        tracked gs: &mut ClosureGlobalState,
        tracked zt: ClosureZoneState,
        region: MemoryRegion,
    ) -> (tracked new_zt: ClosureZoneState)
        requires
            old(gs).wf(),
            zt.wf(old(gs).mem_inst_id()),
            zt.ghost_zone().iommu_mem_set.regions.contains(region),
        ensures
            gs.wf(),
            gs.mem_inst_id() == old(gs).mem_inst_id(),
            gs.zone_ids() == old(gs).zone_ids(),
            new_zt.zone_id() == zt.zone_id(),
            new_zt.wf(gs.mem_inst_id()),
            gs.zones_view() =~= old(gs).zones_view().insert(
                zt.zone_id(),
                zt.ghost_zone().iommu_remove_region(region),
            ),
            new_zt.ghost_zone() == zt.ghost_zone().iommu_remove_region(region),
    {
        gs.iommu_remove_region(zt, region)
    }
}

} // verus!
