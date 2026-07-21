//! Core ghost state machine for the hypervisor memory manager (assumption 1: `all_regions`).
//!
//! Defines:
//! - `all_regions()`: the system-wide set of valid, disjoint physical memory regions.
//! - `gic_region()`: the distinguished shared GIC region, also drawn from `all_regions()`.
//! - `ClosureSpec`: prototype tokenized state machine tracking zone membership plus a
//!   global zone view used to state CPU/IOMMU overlap guards directly.
//! - Token type aliases derived from `ClosureSpec`.
//!
//! The two axioms `all_regions_valid` and `all_regions_disjoint` represent the assumption that
//! physical memory partitioning is correct by construction (guaranteed by the configuration
//! toolchain), without requiring a runtime proof.
//!
//! This is the weak (assumption-1) specification. It is a prototype used to
//! show how tokenized state machines can expose multi-grained concurrency for a
//! TSM-enabled design. The active implementation uses the stronger per-zone-budget
//! variant (`BudgetSpec`).
use super::GhostZone;
use crate::{
    address::{addr::SpecVAddr, region::MemoryRegion},
    memory_set::SpecMemorySet,
};
use verus_state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;

verus! {

/// Abstract function representing the set of all possible memory regions that can be
/// statically configured in the system.
pub uninterp spec fn all_regions() -> Set<MemoryRegion>;

/// The distinguished shared GIC region. IOMMU mappings may share this region
/// across zones; CPU mappings must stay disjoint from it.
pub uninterp spec fn gic_region() -> MemoryRegion;

/// Axiom: all regions in `all_regions()` are valid. This is guaranteed by configuration tools.
pub axiom fn all_regions_valid()
    ensures
        forall|r: MemoryRegion| #[trigger] all_regions().contains(r) ==> r.spec_valid(),
;

/// Axiom: all regions in `all_regions()` do not overlap in physical memory.
pub axiom fn all_regions_disjoint()
    ensures
        forall|r1: MemoryRegion, r2: MemoryRegion| #[trigger]
            all_regions().contains(r1) && #[trigger] all_regions().contains(r2) && r1 != r2
                ==> !r1.spec_overlaps_pmem(r2),
;

/// Axiom: the shared GIC region is a configured region.
pub axiom fn gic_region_in_all_regions()
    ensures
        all_regions().contains(gic_region()),
;

/// CPU insertion guard. A CPU region must be configured, disjoint from the
/// shared GIC, and disjoint from existing CPU regions plus other zones' IOMMU
/// regions. Same-zone CPU/IOMMU overlap is intentionally allowed.
pub open spec fn cpu_insert_region_allowed(
    zones: Map<nat, GhostZone>,
    zid: nat,
    region: MemoryRegion,
) -> bool {
    &&& all_regions().contains(region)
    &&& !region.spec_overlaps_pmem(gic_region())
    &&& forall|other_zid: nat, r: MemoryRegion|
        zones.contains_key(other_zid) && (#[trigger] zones[other_zid].cpu_mem_set.regions.contains(
            r,
        ) || (other_zid != zid && #[trigger] zones[other_zid].iommu_mem_set.regions.contains(r)))
            ==> !region.spec_overlaps_pmem(r)
}

/// IOMMU insertion guard. A private IOMMU region must be configured and
/// disjoint from other zones' CPU/IOMMU regions. The GIC region is the only
/// cross-zone sharing exception. Same-zone CPU/IOMMU overlap is intentionally
/// allowed.
pub open spec fn iommu_insert_region_allowed(
    zones: Map<nat, GhostZone>,
    zid: nat,
    region: MemoryRegion,
) -> bool {
    &&& all_regions().contains(region)
    &&& forall|other_zid: nat, r: MemoryRegion|
        zones.contains_key(other_zid) && other_zid != zid && (
        #[trigger] zones[other_zid].cpu_mem_set.regions.contains(r)
            || #[trigger] zones[other_zid].iommu_mem_set.regions.contains(r)) ==> region
            == gic_region() || r == gic_region() || !region.spec_overlaps_pmem(r)
}

// Assumption-1 prototype state machine. The per-zone `zones` field remains
// map-sharded so each zone keeps its local token. The variable `zones_view`
// mirrors the full map and is used only by the prototype's global overlap guards.
tokenized_state_machine! {
    ClosureSpec {
        fields {
            /// Mirror of `zones.dom()`, kept as a variable field so zone creation can use
            /// a simple absence check before `map` insertion.
            #[sharding(variable)]
            pub zone_ids: Set<nat>,

            /// Per-zone memory state. One zone token can be placed in one zone-local `Mutex`.
            #[sharding(map)]
            pub zones: Map<nat, GhostZone>,

            /// Global mirror of `zones`. It replaces the old CPU/IOMMU closure shards and
            /// lets insertion transitions state overlap guards over all existing zones.
            #[sharding(variable)]
            pub zones_view: Map<nat, GhostZone>,
        }

        /// `zone_ids` is always the exact set of keys in `zones`.
        #[invariant]
        pub fn inv_zone_ids(&self) -> bool {
            self.zones.dom() == self.zone_ids
        }

        /// `zones_view` is the global mirror of the map-sharded `zones` field.
        #[invariant]
        pub fn inv_zones_view(&self) -> bool {
            self.zones_view == self.zones
        }

        /// All zones are well-formed (regions valid and non-overlapping in vmem).
        #[invariant]
        pub fn inv_zones_wf(&self) -> bool {
            forall|zid: nat|
                self.zones.contains_key(zid) ==> #[trigger] self.zones[zid].wf()
        }

        /// Every CPU or IOMMU region in every zone comes from `all_regions()`.
        #[invariant]
        pub fn inv_regions_in_all_regions(&self) -> bool {
            forall|zid: nat, r: MemoryRegion|
                self.zones.contains_key(zid) && #[trigger] self.zones[zid].contains_region(r)
                    ==> all_regions().contains(r)
        }

        /// CPU mappings never overlap the shared GIC region.
        #[invariant]
        pub fn inv_cpu_disjoint_from_gic(&self) -> bool {
            forall|zid: nat, r: MemoryRegion|
                self.zones.contains_key(zid) && #[trigger] self.zones[zid].cpu_mem_set.regions.contains(r)
                    ==> !r.spec_overlaps_pmem(gic_region())
        }

        /// Non-GIC regions from distinct zones are physically disjoint, regardless of
        /// whether they appear on the CPU side or the IOMMU side.
        ///
        /// This is the direct state-machine form of the intended rule: an IOMMU
        /// region may overlap its own zone's CPU region, and the GIC may be shared
        /// across zones, but private regions cannot overlap across zones.
        #[invariant]
        pub fn inv_cross_zone_non_gic_disjoint(&self) -> bool {
            forall|zid1: nat, zid2: nat, r1: MemoryRegion, r2: MemoryRegion|
                self.zones.contains_key(zid1) && self.zones.contains_key(zid2) && zid1 != zid2
                && #[trigger] self.zones[zid1].contains_region(r1)
                && #[trigger] self.zones[zid2].contains_region(r2)
                && r1 != gic_region() && r2 != gic_region()
                    ==> !r1.spec_overlaps_pmem(r2)
        }

        // Properties are read-only lemmas that zone-token holders can invoke to learn
        // facts about the global state, analogous to `free_client_disjoint` in `AllocSpec`.

        /// Any CPU region that belongs to zone `zid` is drawn from `all_regions()`.
        property! {
            zone_cpu_region_in_all_regions(zid: nat, zone: GhostZone) {
                have zones >= [zid => zone];
                assert(forall|r: MemoryRegion|
                    #[trigger] zone.cpu_mem_set.regions.contains(r)
                        ==> all_regions().contains(r)
                ) by {
                    assert forall|r: MemoryRegion| #[trigger] zone.cpu_mem_set.regions.contains(r)
                        implies all_regions().contains(r) by {
                        assert(pre.zones.contains_key(zid));
                        assert(pre.zones[zid].contains_region(r));
                    };
                };
            }
        }

        /// Any IOMMU region that belongs to zone `zid` is drawn from `all_regions()`.
        property! {
            zone_iommu_region_in_all_regions(zid: nat, zone: GhostZone) {
                have zones >= [zid => zone];
                assert(forall|r: MemoryRegion|
                    #[trigger] zone.iommu_mem_set.regions.contains(r)
                        ==> all_regions().contains(r)
                ) by {
                    assert forall|r: MemoryRegion| #[trigger] zone.iommu_mem_set.regions.contains(r)
                        implies all_regions().contains(r) by {
                        assert(pre.zones.contains_key(zid));
                        assert(pre.zones[zid].contains_region(r));
                    };
                };
            }
        }

        /// Regions from two distinct zones are mutually non-overlapping unless one
        /// side is the shared GIC region.
        property! {
            cross_zone_disjoint_except_gic(zid1: nat, zone1: GhostZone, zid2: nat, zone2: GhostZone) {
                have zones >= [zid1 => zone1];
                have zones >= [zid2 => zone2];
                require(zid1 != zid2);
                assert(forall|r1: MemoryRegion, r2: MemoryRegion| #![auto]
                    zone1.regions().contains(r1) && zone2.regions().contains(r2)
                    && r1 != gic_region() && r2 != gic_region()
                        ==> !r1.spec_overlaps_pmem(r2)
                ) by {
                    assert forall|r1: MemoryRegion, r2: MemoryRegion| #![auto]
                        zone1.regions().contains(r1) && zone2.regions().contains(r2)
                        && r1 != gic_region() && r2 != gic_region()
                        implies !r1.spec_overlaps_pmem(r2) by {
                        assert(pre.zones.contains_key(zid1) && pre.zones[zid1].contains_region(r1));
                        assert(pre.zones.contains_key(zid2) && pre.zones[zid2].contains_region(r2));
                    };
                };
            }
        }

        /// CPU-side ZoneIsolated property: every CPU translation in a zone stays
        /// within the declaring region's physical range.
        property! {
            zone_isolated(zid: nat, zone: GhostZone, v: SpecVAddr) {
                have zones >= [zid => zone];
                require(zone.cpu_mem_set.contains_vaddr(v));
                assert(zone.wf());
                assert({
                    let paddr = zone.cpu_mem_set.translate(v);
                    let r = choose|r: MemoryRegion|
                        zone.cpu_mem_set.regions.contains(r) && #[trigger] r.spec_contains_vaddr(v);
                    r.spec_contains_paddr(paddr)
                }) by {
                    let paddr = zone.cpu_mem_set.translate(v);
                    assert(zone.cpu_mem_set.wf());
                    assert(zone.cpu_mem_set.contains_vaddr(v));
                    let r = choose|r: MemoryRegion|
                        zone.cpu_mem_set.regions.contains(r) && #[trigger] r.spec_contains_vaddr(v);
                    assert(zone.cpu_mem_set.regions.contains(r) && r.spec_contains_vaddr(v));
                    assert(r.spec_valid());
                    r.lemma_contains_vaddr_implies_contains_paddr(v);
                    assert(r.spec_contains_paddr(paddr));
                };
            }
        }

        /// IOMMU-side ZoneIsolated property: every IOMMU translation in a zone stays
        /// within the declaring region's physical range.
        property! {
            iommu_zone_isolated(zid: nat, zone: GhostZone, v: SpecVAddr) {
                have zones >= [zid => zone];
                require(zone.iommu_mem_set.contains_vaddr(v));
                assert(zone.wf());
                assert({
                    let paddr = zone.iommu_mem_set.translate(v);
                    let r = choose|r: MemoryRegion|
                        zone.iommu_mem_set.regions.contains(r) && #[trigger] r.spec_contains_vaddr(v);
                    r.spec_contains_paddr(paddr)
                }) by {
                    let paddr = zone.iommu_mem_set.translate(v);
                    assert(zone.iommu_mem_set.wf());
                    assert(zone.iommu_mem_set.contains_vaddr(v));
                    let r = choose|r: MemoryRegion|
                        zone.iommu_mem_set.regions.contains(r) && #[trigger] r.spec_contains_vaddr(v);
                    assert(zone.iommu_mem_set.regions.contains(r) && r.spec_contains_vaddr(v));
                    assert(r.spec_valid());
                    r.lemma_contains_vaddr_implies_contains_paddr(v);
                    assert(r.spec_contains_paddr(paddr));
                };
            }
        }

        init! {
            initialize() {
                init zone_ids = Set::empty();
                init zones = Map::empty();
                init zones_view = Map::empty();
            }
        }

        /// Add an empty zone. CPU and IOMMU regions are inserted afterwards via the
        /// domain-specific transitions.
        transition! {
            add_zone(zid: nat) {
                require(!pre.zone_ids.contains(zid));
                update zone_ids = pre.zone_ids.insert(zid);
                add zones += [zid => GhostZone {
                    cpu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
                    iommu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
                }];
                update zones_view = pre.zones_view.insert(zid, GhostZone {
                    cpu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
                    iommu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
                });
            }
        }

        /// Remove an entire zone.
        ///
        /// Note: callers are responsible for draining page-table frames and physical
        /// memory before invoking this transition; the prototype token is simply dropped.
        transition! {
            remove_zone(zid: nat) {
                remove zones -= [zid => let _zone];
                update zone_ids = pre.zone_ids.remove(zid);
                update zones_view = pre.zones_view.remove(zid);
            }
        }

        /// Insert one CPU-visible region into an existing zone.
        transition! {
            cpu_insert_region(zid: nat, region: MemoryRegion) {
                remove zones -= [zid => let zone];
                require(region.spec_valid());
                require(cpu_insert_region_allowed(pre.zones_view, zid, region));
                require(!zone.cpu_mem_set.regions.contains(region));
                require(!zone.cpu_mem_set.overlaps_vmem(region));
                add zones += [zid => zone.cpu_insert_region(region)];
                update zones_view = pre.zones_view.insert(zid, zone.cpu_insert_region(region));
            }
        }

        /// Remove one CPU-visible region from an existing zone.
        transition! {
            cpu_remove_region(zid: nat, region: MemoryRegion) {
                remove zones -= [zid => let zone];
                require(zone.cpu_mem_set.regions.contains(region));
                add zones += [zid => zone.cpu_remove_region(region)];
                update zones_view = pre.zones_view.insert(zid, zone.cpu_remove_region(region));
            }
        }

        /// Insert one IOMMU-visible region into an existing zone.
        transition! {
            iommu_insert_region(zid: nat, region: MemoryRegion) {
                remove zones -= [zid => let zone];
                require(region.spec_valid());
                require(iommu_insert_region_allowed(pre.zones_view, zid, region));
                require(!zone.iommu_mem_set.regions.contains(region));
                require(!zone.iommu_mem_set.overlaps_vmem(region));
                add zones += [zid => zone.iommu_insert_region(region)];
                update zones_view = pre.zones_view.insert(zid, zone.iommu_insert_region(region));
            }
        }

        /// Remove one IOMMU-visible region from an existing zone.
        transition! {
            iommu_remove_region(zid: nat, region: MemoryRegion) {
                remove zones -= [zid => let zone];
                require(zone.iommu_mem_set.regions.contains(region));
                add zones += [zid => zone.iommu_remove_region(region)];
                update zones_view = pre.zones_view.insert(zid, zone.iommu_remove_region(region));
            }
        }

        // This prototype is not on the active implementation path. Its purpose is
        // to show the TSM shape for CPU/IOMMU multi-grained concurrency, so the
        // invariant preservation obligations are intentionally trusted here.
        #[inductive(initialize)]
        fn initialize_inductive(post: Self) {
            admit();
        }

        #[inductive(add_zone)]
        fn add_zone_inductive(pre: Self, post: Self, zid: nat) {
            admit();
        }

        #[inductive(remove_zone)]
        fn remove_zone_inductive(pre: Self, post: Self, zid: nat) {
            admit();
        }

        #[inductive(cpu_insert_region)]
        fn cpu_insert_region_inductive(pre: Self, post: Self, zid: nat, region: MemoryRegion) {
            admit();
        }

        #[inductive(cpu_remove_region)]
        fn cpu_remove_region_inductive(pre: Self, post: Self, zid: nat, region: MemoryRegion) {
            admit();
        }

        #[inductive(iommu_insert_region)]
        fn iommu_insert_region_inductive(pre: Self, post: Self, zid: nat, region: MemoryRegion) {
            admit();
        }

        #[inductive(iommu_remove_region)]
        fn iommu_remove_region_inductive(pre: Self, post: Self, zid: nat, region: MemoryRegion) {
            admit();
        }
    }
}
// Token type aliases.


pub type ClosureSpecInstance = ClosureSpec::Instance;

pub type ClosureZoneIdsToken = ClosureSpec::zone_ids;

pub type ClosureZoneToken = ClosureSpec::zones;

pub type ClosureZonesViewToken = ClosureSpec::zones_view;

} // verus!
