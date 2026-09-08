//! Token wrappers for the draft HyperEnclave four-class policy.
//!
//! Unlike `BudgetProtocol`, enclave-private insertion consults a global
//! `enclave_private_regions_view`.
//! Structural operations and CPU operations that change the dynamic private or
//! Shared views mutate that global state while holding the `HvMem` write lock.
use super::super::spec::GhostZone;
use super::{ZoneGhostProtocol, ZoneStateOps};
use crate::address::region::MemoryRegion;
use crate::memory_set::SpecMemorySet;
use vstd::prelude::*;

verus! {

use super::super::spec::hyperenclave::*;

/// Per-zone token kept in the corresponding `Zone` lock.
pub tracked struct HyperEnclaveZoneState {
    pub zone_tok: HyperEnclaveZoneToken,
}

impl ZoneStateOps for HyperEnclaveZoneState {
    open spec fn zone_id(&self) -> nat {
        self.zone_tok.key()
    }

    open spec fn ghost_zone(&self) -> GhostZone {
        self.zone_tok.value()
    }

    open spec fn wf(&self, mem_inst_id: InstanceId) -> bool {
        self.zone_tok.instance_id() == mem_inst_id
    }
}

/// Global protocol tokens protected by `HvMem`'s outer lock. They are mutated
/// only while holding the write lock and observed by zone-local operations
/// while holding a read lock.
pub tracked struct HyperEnclaveGlobalState {
    pub inst: HyperEnclaveSpecInstance,
    pub zone_ids_tok: HyperEnclaveZoneIdsToken,
    pub enclave_private_regions_view_tok: HyperEnclavePrivateRegionsViewToken,
    pub shared_regions_tok: HyperEnclaveSharedRegionsToken,
}

impl HyperEnclaveGlobalState {
    pub open spec fn wf(&self) -> bool {
        &&& self.zone_ids_tok.instance_id() == self.inst.id()
        &&& self.enclave_private_regions_view_tok.instance_id() == self.inst.id()
        &&& self.shared_regions_tok.instance_id() == self.inst.id()
        &&& self.enclave_private_regions_view().dom() == self.zone_ids()
        &&& self.shared_regions().dom() == self.zone_ids()
    }

    pub open spec fn mem_inst_id(&self) -> InstanceId {
        self.inst.id()
    }

    pub open spec fn zone_ids(&self) -> Set<nat> {
        self.zone_ids_tok.value()
    }

    pub open spec fn enclave_private_regions_view(&self) -> Map<nat, Set<MemoryRegion>> {
        self.enclave_private_regions_view_tok.value()
    }

    pub open spec fn shared_regions(&self) -> Map<nat, Set<MemoryRegion>> {
        self.shared_regions_tok.value()
    }

    pub proof fn new(
        tracked inst: HyperEnclaveSpecInstance,
        tracked zone_ids_tok: HyperEnclaveZoneIdsToken,
        tracked enclave_private_regions_view_tok: HyperEnclavePrivateRegionsViewToken,
        tracked shared_regions_tok: HyperEnclaveSharedRegionsToken,
    ) -> (tracked state: Self)
        requires
            zone_ids_tok.instance_id() == inst.id(),
            zone_ids_tok.value() =~= Set::empty(),
            enclave_private_regions_view_tok.instance_id() == inst.id(),
            enclave_private_regions_view_tok.value() =~= Map::empty(),
            shared_regions_tok.instance_id() == inst.id(),
            shared_regions_tok.value() =~= Map::empty(),
        ensures
            state.wf(),
            state.mem_inst_id() == inst.id(),
            state.zone_ids() =~= Set::empty(),
            state.enclave_private_regions_view() =~= Map::empty(),
            state.shared_regions() =~= Map::empty(),
    {
        Self { inst, zone_ids_tok, enclave_private_regions_view_tok, shared_regions_tok }
    }

    proof fn lemma_insert_existing_keeps_domain(
        map: Map<nat, Set<MemoryRegion>>,
        zid: nat,
        regions: Set<MemoryRegion>,
    )
        requires
            map.contains_key(zid),
        ensures
            map.insert(zid, regions).dom() =~= map.dom(),
    {
        assert forall|key: nat|
            map.insert(zid, regions).dom().contains(key) == map.dom().contains(key) by {
            if key == zid {
                assert(map.dom().contains(key));
            }
        }
    }

    proof fn lemma_existing_zone_update_preserves_wf(
        tracked &self,
        old_view: Map<nat, Set<MemoryRegion>>,
        old_ids: Set<nat>,
        zid: nat,
        regions: Set<MemoryRegion>,
    )
        requires
            self.zone_ids_tok.instance_id() == self.inst.id(),
            self.enclave_private_regions_view_tok.instance_id() == self.inst.id(),
            self.shared_regions_tok.instance_id() == self.inst.id(),
            old_view.dom() == old_ids,
            self.shared_regions().dom() == old_ids,
            old_ids.contains(zid),
            self.zone_ids() == old_ids,
            self.enclave_private_regions_view() =~= old_view.insert(zid, regions),
        ensures
            self.wf(),
    {
        Self::lemma_insert_existing_keeps_domain(old_view, zid, regions);
    }

    proof fn lemma_existing_shared_update_preserves_wf(
        tracked &self,
        old_shared: Map<nat, Set<MemoryRegion>>,
        old_ids: Set<nat>,
        zid: nat,
        regions: Set<MemoryRegion>,
    )
        requires
            self.zone_ids_tok.instance_id() == self.inst.id(),
            self.enclave_private_regions_view_tok.instance_id() == self.inst.id(),
            self.shared_regions_tok.instance_id() == self.inst.id(),
            self.enclave_private_regions_view().dom() == old_ids,
            old_shared.dom() == old_ids,
            old_ids.contains(zid),
            self.zone_ids() == old_ids,
            self.shared_regions() =~= old_shared.insert(zid, regions),
        ensures
            self.wf(),
    {
        Self::lemma_insert_existing_keeps_domain(old_shared, zid, regions);
    }

    pub proof fn add_zone(tracked &mut self, zid: nat) -> (tracked state: HyperEnclaveZoneState)
        requires
            old(self).wf(),
            !old(self).zone_ids().contains(zid),
        ensures
            self.wf(),
            self.mem_inst_id() == old(self).mem_inst_id(),
            self.zone_ids() =~= old(self).zone_ids().insert(zid),
            self.enclave_private_regions_view() =~= old(self).enclave_private_regions_view().insert(
                zid,
                state.ghost_zone().cpu_mem_set.regions,
            ),
            self.shared_regions() =~= old(self).shared_regions().insert(
                zid,
                Set::empty(),
            ),
            state.wf(self.mem_inst_id()),
            state.zone_id() == zid,
            state.ghost_zone() == (GhostZone {
                cpu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
                iommu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
            }),
    {
        let tracked zone_tok = self.inst.add_zone(
            zid,
            &mut self.zone_ids_tok,
            &mut self.enclave_private_regions_view_tok,
            &mut self.shared_regions_tok,
        );
        HyperEnclaveZoneState { zone_tok }
    }

    pub proof fn remove_zone(tracked &mut self, tracked state: HyperEnclaveZoneState)
        requires
            old(self).wf(),
            state.wf(old(self).mem_inst_id()),
            state.ghost_zone().cpu_mem_set.empty(),
            state.ghost_zone().iommu_mem_set.empty(),
        ensures
            self.wf(),
            self.mem_inst_id() == old(self).mem_inst_id(),
            self.zone_ids() =~= old(self).zone_ids().remove(state.zone_id()),
            self.enclave_private_regions_view()
                =~= old(self).enclave_private_regions_view().remove(state.zone_id()),
            self.shared_regions() =~= old(self).shared_regions().remove(
                state.zone_id(),
            ),
    {
        let tracked HyperEnclaveZoneState { zone_tok } = state;
        let zid = zone_tok.key();
        self.inst.remove_zone(
            zid,
            &mut self.zone_ids_tok,
            zone_tok,
            &mut self.enclave_private_regions_view_tok,
            &mut self.shared_regions_tok,
        );
    }

    /// Refresh one conservative private-region entry after reopening the zone
    /// lock. Abstract memory state is unchanged; the returned equality lets
    /// the executable scan prove the private-region insertion guard.
    pub proof fn synchronize_enclave_private_regions_view(
        tracked &mut self,
        tracked state: HyperEnclaveZoneState,
    ) -> (tracked new_state: HyperEnclaveZoneState)
        requires
            old(self).wf(),
            state.wf(old(self).mem_inst_id()),
            old(self).zone_ids().contains(state.zone_id()),
        ensures
            self.wf(),
            self.mem_inst_id() == old(self).mem_inst_id(),
            self.zone_ids() == old(self).zone_ids(),
            new_state.wf(self.mem_inst_id()),
            new_state.zone_id() == state.zone_id(),
            new_state.ghost_zone() == state.ghost_zone(),
            self.enclave_private_regions_view()
                =~= old(self).enclave_private_regions_view().insert(
                state.zone_id(),
                live_enclave_private_regions(state.zone_id(), state.ghost_zone()),
            ),
            self.enclave_private_regions_view().contains_pair(
                state.zone_id(),
                live_enclave_private_regions(state.zone_id(), state.ghost_zone()),
            ),
    {
        let ghost old_view = self.enclave_private_regions_view();
        let ghost old_ids = self.zone_ids();
        let ghost old_regions = live_enclave_private_regions(
            state.zone_id(),
            state.ghost_zone(),
        );
        let tracked HyperEnclaveZoneState { zone_tok } = state;
        let zid = zone_tok.key();
        let tracked new_zone_tok = self.inst.synchronize_enclave_private_regions_view(
            zid,
            zone_tok,
            &mut self.enclave_private_regions_view_tok,
        );
        self.lemma_existing_zone_update_preserves_wf(old_view, old_ids, zid, old_regions);
        HyperEnclaveZoneState { zone_tok: new_zone_tok }
    }

    /// Record a normal-world CPU mapping in root zone zero.
    pub proof fn cpu_insert_normal_region(
        tracked &self,
        tracked state: HyperEnclaveZoneState,
        region: MemoryRegion,
    ) -> (tracked new_state: HyperEnclaveZoneState)
        requires
            self.wf(),
            state.wf(self.mem_inst_id()),
            self.zone_ids().contains(state.zone_id()),
            state.zone_id() == root_zone_id(),
            region.spec_valid(),
            region_in_normal_memory(region),
            !state.ghost_zone().cpu_mem_set.regions.contains(region),
            !state.ghost_zone().cpu_mem_set.overlaps_vmem(region),
        ensures
            self.wf(),
            new_state.wf(self.mem_inst_id()),
            new_state.zone_id() == root_zone_id(),
            new_state.ghost_zone() == state.ghost_zone().cpu_insert_region(region),
    {
        let tracked HyperEnclaveZoneState { zone_tok } = state;
        let tracked new_zone_tok = self.inst.cpu_insert_normal_region(region, zone_tok);
        HyperEnclaveZoneState { zone_tok: new_zone_tok }
    }

    /// Dynamically assign an EPC or enclave GPT backing region to an enclave.
    pub proof fn cpu_insert_enclave_private_region(
        tracked &mut self,
        tracked state: HyperEnclaveZoneState,
        region: MemoryRegion,
    ) -> (tracked new_state: HyperEnclaveZoneState)
        requires
            old(self).wf(),
            state.wf(old(self).mem_inst_id()),
            old(self).zone_ids().contains(state.zone_id()),
            state.zone_id() != root_zone_id(),
            region.spec_valid(),
            region_in_enclave_memory(state.zone_id(), region),
            enclave_insert_allowed(
                old(self).enclave_private_regions_view(),
                state.zone_id(),
                region,
            ),
            !state.ghost_zone().cpu_mem_set.regions.contains(region),
            !state.ghost_zone().cpu_mem_set.overlaps_vmem(region),
        ensures
            self.wf(),
            self.mem_inst_id() == old(self).mem_inst_id(),
            self.zone_ids() == old(self).zone_ids(),
            new_state.wf(self.mem_inst_id()),
            new_state.zone_id() == state.zone_id(),
            new_state.ghost_zone() == state.ghost_zone().cpu_insert_region(region),
            self.enclave_private_regions_view()
                =~= old(self).enclave_private_regions_view().insert(
                state.zone_id(),
                live_enclave_private_regions(
                    state.zone_id(),
                    state.ghost_zone().cpu_insert_region(region),
                ),
            ),
    {
        let ghost old_view = self.enclave_private_regions_view();
        let ghost old_ids = self.zone_ids();
        let ghost new_regions = live_enclave_private_regions(
            state.zone_id(),
            state.ghost_zone().cpu_insert_region(region),
        );
        let tracked HyperEnclaveZoneState { zone_tok } = state;
        let zid = zone_tok.key();
        let tracked new_zone_tok = self.inst.cpu_insert_enclave_private_region(
            zid,
            region,
            zone_tok,
            &mut self.enclave_private_regions_view_tok,
        );
        self.lemma_existing_zone_update_preserves_wf(
            old_view,
            old_ids,
            zid,
            new_regions,
        );
        HyperEnclaveZoneState { zone_tok: new_zone_tok }
    }

    /// Record one active normal-memory Shared mapping in an enclave zone.
    /// HyperEnclave supplies the marshalling-buffer authorization premise;
    /// this transition records only the mapping's dynamic Shared status.
    pub proof fn cpu_insert_enclave_shared_region(
        tracked &mut self,
        tracked state: HyperEnclaveZoneState,
        region: MemoryRegion,
    ) -> (tracked new_state: HyperEnclaveZoneState)
        requires
            old(self).wf(),
            state.wf(old(self).mem_inst_id()),
            old(self).zone_ids().contains(state.zone_id()),
            state.zone_id() != root_zone_id(),
            region.spec_valid(),
            region_in_normal_memory(region),
            !state.ghost_zone().cpu_mem_set.regions.contains(region),
            !state.ghost_zone().cpu_mem_set.overlaps_vmem(region),
        ensures
            self.wf(),
            self.mem_inst_id() == old(self).mem_inst_id(),
            self.zone_ids() == old(self).zone_ids(),
            self.enclave_private_regions_view() == old(self).enclave_private_regions_view(),
            new_state.wf(self.mem_inst_id()),
            new_state.zone_id() == state.zone_id(),
            new_state.ghost_zone() == state.ghost_zone().cpu_insert_region(region),
            self.shared_regions() =~= old(self).shared_regions().insert(
                state.zone_id(),
                live_shared_regions(
                    state.zone_id(),
                    state.ghost_zone().cpu_insert_region(region),
                ),
            ),
    {
        let ghost old_shared = self.shared_regions();
        let ghost old_ids = self.zone_ids();
        let ghost new_regions = live_shared_regions(
            state.zone_id(),
            state.ghost_zone().cpu_insert_region(region),
        );
        let tracked HyperEnclaveZoneState { zone_tok } = state;
        let zid = zone_tok.key();
        let tracked new_zone_tok = self.inst.cpu_insert_enclave_shared_region(
            zid,
            region,
            zone_tok,
            &mut self.shared_regions_tok,
        );
        self.lemma_existing_shared_update_preserves_wf(
            old_shared,
            old_ids,
            zid,
            new_regions,
        );
        HyperEnclaveZoneState { zone_tok: new_zone_tok }
    }

    pub proof fn cpu_remove_region(
        tracked &mut self,
        tracked state: HyperEnclaveZoneState,
        region: MemoryRegion,
    ) -> (tracked new_state: HyperEnclaveZoneState)
        requires
            old(self).wf(),
            state.wf(old(self).mem_inst_id()),
            old(self).zone_ids().contains(state.zone_id()),
            state.ghost_zone().cpu_mem_set.regions.contains(region),
        ensures
            self.wf(),
            self.mem_inst_id() == old(self).mem_inst_id(),
            self.zone_ids() == old(self).zone_ids(),
            self.enclave_private_regions_view() == old(self).enclave_private_regions_view(),
            new_state.wf(self.mem_inst_id()),
            new_state.zone_id() == state.zone_id(),
            new_state.ghost_zone() == state.ghost_zone().cpu_remove_region(region),
            self.shared_regions() =~= old(self).shared_regions().insert(
                state.zone_id(),
                live_shared_regions(
                    state.zone_id(),
                    state.ghost_zone().cpu_remove_region(region),
                ),
            ),
    {
        let ghost old_shared = self.shared_regions();
        let ghost old_ids = self.zone_ids();
        let ghost new_regions = live_shared_regions(
            state.zone_id(),
            state.ghost_zone().cpu_remove_region(region),
        );
        let tracked HyperEnclaveZoneState { zone_tok } = state;
        let zid = zone_tok.key();
        let tracked new_zone_tok = self.inst.cpu_remove_region(
            zid,
            region,
            zone_tok,
            &mut self.shared_regions_tok,
        );
        self.lemma_existing_shared_update_preserves_wf(
            old_shared,
            old_ids,
            zid,
            new_regions,
        );
        HyperEnclaveZoneState { zone_tok: new_zone_tok }
    }

    pub proof fn cpu_clear_enclave_regions(
        tracked &mut self,
        tracked state: HyperEnclaveZoneState,
    ) -> (tracked new_state: HyperEnclaveZoneState)
        requires
            old(self).wf(),
            state.wf(old(self).mem_inst_id()),
            old(self).zone_ids().contains(state.zone_id()),
            state.zone_id() != root_zone_id(),
        ensures
            self.wf(),
            self.mem_inst_id() == old(self).mem_inst_id(),
            self.zone_ids() == old(self).zone_ids(),
            self.enclave_private_regions_view() == old(self).enclave_private_regions_view(),
            new_state.wf(self.mem_inst_id()),
            new_state.zone_id() == state.zone_id(),
            new_state.ghost_zone() == state.ghost_zone().cpu_clear(),
            self.shared_regions() =~= old(self).shared_regions().insert(
                state.zone_id(),
                Set::empty(),
            ),
    {
        let ghost old_shared = self.shared_regions();
        let ghost old_ids = self.zone_ids();
        let tracked HyperEnclaveZoneState { zone_tok } = state;
        let zid = zone_tok.key();
        let tracked new_zone_tok = self.inst.cpu_clear_enclave_regions(
            zid,
            zone_tok,
            &mut self.shared_regions_tok,
        );
        self.lemma_existing_shared_update_preserves_wf(
            old_shared,
            old_ids,
            zid,
            Set::empty(),
        );
        HyperEnclaveZoneState { zone_tok: new_zone_tok }
    }

    /// Record a root-only IOMMU mapping. No corresponding transition exists for
    /// an enclave zone.
    pub proof fn iommu_insert_region(
        tracked &self,
        tracked state: HyperEnclaveZoneState,
        region: MemoryRegion,
    ) -> (tracked new_state: HyperEnclaveZoneState)
        requires
            self.wf(),
            state.wf(self.mem_inst_id()),
            self.zone_ids().contains(state.zone_id()),
            state.zone_id() == root_zone_id(),
            region.spec_valid(),
            region_in_dma_memory(region),
            !state.ghost_zone().iommu_mem_set.regions.contains(region),
            !state.ghost_zone().iommu_mem_set.overlaps_vmem(region),
            !state.ghost_zone().iommu_mem_set.overlaps_pmem(region),
        ensures
            self.wf(),
            new_state.wf(self.mem_inst_id()),
            new_state.zone_id() == root_zone_id(),
            new_state.ghost_zone() == state.ghost_zone().iommu_insert_region(region),
    {
        let tracked HyperEnclaveZoneState { zone_tok } = state;
        let tracked new_zone_tok = self.inst.iommu_insert_region(region, zone_tok);
        HyperEnclaveZoneState { zone_tok: new_zone_tok }
    }

    pub proof fn iommu_remove_region(
        tracked &self,
        tracked state: HyperEnclaveZoneState,
        region: MemoryRegion,
    ) -> (tracked new_state: HyperEnclaveZoneState)
        requires
            self.wf(),
            state.wf(self.mem_inst_id()),
            self.zone_ids().contains(state.zone_id()),
            state.zone_id() == root_zone_id(),
            state.ghost_zone().iommu_mem_set.regions.contains(region),
        ensures
            self.wf(),
            new_state.wf(self.mem_inst_id()),
            new_state.zone_id() == root_zone_id(),
            new_state.ghost_zone() == state.ghost_zone().iommu_remove_region(region),
    {
        let tracked HyperEnclaveZoneState { zone_tok } = state;
        let tracked new_zone_tok = self.inst.iommu_remove_region(region, zone_tok);
        HyperEnclaveZoneState { zone_tok: new_zone_tok }
    }

    pub proof fn iommu_clear_regions(
        tracked &self,
        tracked state: HyperEnclaveZoneState,
    ) -> (tracked new_state: HyperEnclaveZoneState)
        requires
            self.wf(),
            state.wf(self.mem_inst_id()),
            self.zone_ids().contains(state.zone_id()),
            state.zone_id() == root_zone_id(),
        ensures
            self.wf(),
            new_state.wf(self.mem_inst_id()),
            new_state.zone_id() == root_zone_id(),
            new_state.ghost_zone() == state.ghost_zone().iommu_clear(),
    {
        let tracked HyperEnclaveZoneState { zone_tok } = state;
        let tracked new_zone_tok = self.inst.iommu_clear_regions(zone_tok);
        HyperEnclaveZoneState { zone_tok: new_zone_tok }
    }
}

/// Marker used as `HvMem`'s protocol type parameter.
pub struct HyperEnclaveProtocol;

impl ZoneGhostProtocol for HyperEnclaveProtocol {
    type ZoneState = HyperEnclaveZoneState;

    type GlobalState = HyperEnclaveGlobalState;

    open spec fn global_wf(gs: &Self::GlobalState) -> bool {
        gs.wf()
    }

    open spec fn mem_inst_id(gs: &Self::GlobalState) -> InstanceId {
        gs.mem_inst_id()
    }

    open spec fn zone_ids(gs: &Self::GlobalState) -> Set<nat> {
        gs.zone_ids()
    }

    proof fn add_zone(tracked gs: &mut Self::GlobalState, zid: nat) -> (tracked state:
        Self::ZoneState) {
        gs.add_zone(zid)
    }

    proof fn remove_zone(tracked gs: &mut Self::GlobalState, tracked state: Self::ZoneState) {
        gs.remove_zone(state)
    }
}

} // verus!
