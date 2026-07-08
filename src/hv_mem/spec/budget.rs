//! Assumption-2 per-zone region state machine for the hypervisor memory manager.
//!
//! Under assumption 2 each zone is pre-allocated a fixed set of physical memory
//! regions at boot time. A zone may only insert regions that are within its own
//! configured region set, so `insert_region` needs only the zone-local `zones`
//! token — no global lock is needed.
//!
//! Compared to [`super::ClosureSpec`]:
//! - `ClosureSpec` has a `#[sharding(variable)]` `zones_view` mirror, whose
//!   global token lets the prototype state cross-zone overlap guards directly.
//! - `BudgetSpec` uses external uninterpreted spec functions to model static
//!   per-zone regions (`zone_regions`) and static GIC regions (`gic_region`).
//!   No budget token exists in the state machine, so there is less token plumbing.
//!
//! P1 only needs the following facts:
//! - regions currently assigned to a zone stay inside that zone's `zone_regions`;
//! - different zones' configured regions are physically disjoint;
//! - `gic_region` is physically disjoint from every zone's configured regions.
use super::GhostZone;
use crate::address::region::MemoryRegion;
use crate::memory_set::SpecMemorySet;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::{prelude::*, tokens::InstanceId};

verus! {

/// Static configured regions owned by one zone.
pub uninterp spec fn zone_regions(zid: nat) -> Set<MemoryRegion>;

/// Static configured GIC region.
pub uninterp spec fn gic_region() -> MemoryRegion;

/// Axiom: all configured zone and GIC regions are valid memory regions.
pub axiom fn configured_regions_valid()
    ensures
        forall|zid: nat, r: MemoryRegion| #[trigger]
            zone_regions(zid).contains(r) ==> r.spec_valid(),
        gic_region().spec_valid(),
;

/// Axiom: configured regions within one zone are physically disjoint.
pub axiom fn zone_regions_internal_disjoint()
    ensures
        forall|zid: nat, r1: MemoryRegion, r2: MemoryRegion|
            #![auto]
            zone_regions(zid).contains(r1) && zone_regions(zid).contains(r2) && r1 != r2
                ==> !r1.spec_overlaps_pmem(r2),
;

/// Axiom: configured regions of distinct zones are physically disjoint.
pub axiom fn zone_regions_pairwise_disjoint()
    ensures
        forall|zid1: nat, zid2: nat, r1: MemoryRegion, r2: MemoryRegion|
            #![auto]
            zid1 != zid2 && zone_regions(zid1).contains(r1) && zone_regions(zid2).contains(r2)
                ==> !r1.spec_overlaps_pmem(r2),
;

/// Axiom: GIC region is physically disjoint from every zone region.
pub axiom fn gic_region_disjoint_from_zones()
    ensures
        forall|zid: nat, r: MemoryRegion|
            #![auto]
            zone_regions(zid).contains(r) ==> !gic_region().spec_overlaps_pmem(r),
;

// Per-zone-budget state machine
tokenized_state_machine! {
    BudgetSpec {
        fields {
            #[sharding(variable)]
            pub zone_ids: Set<nat>,

            #[sharding(map)]
            pub zones: Map<nat, GhostZone>,
        }

        // ── Invariants ─────────────────────────────────────────────────────────────

        /// `zone_ids` and `zones.dom()` are always identical.
        #[invariant]
        pub fn inv_zone_ids(&self) -> bool {
            self.zones.dom() == self.zone_ids
        }

        /// All zones are well-formed (regions valid and non-overlapping).
        #[invariant]
        pub fn inv_zones_wf(&self) -> bool {
            forall|zid: nat|
                self.zones.contains_key(zid) ==> #[trigger] self.zones[zid].wf()
        }

        /// CPU-owned dynamic regions must come from the zone's ordinary region set.
        #[invariant]
        pub fn inv_cpu_in_zone_regions(&self) -> bool {
            forall|zid: nat, r: MemoryRegion|
                self.zones.contains_key(zid) && #[trigger] self.zones[zid].cpu_mem_set.regions.contains(r)
                    ==> #[trigger] zone_regions(zid).contains(r)
        }

        /// IOMMU-owned dynamic regions may come from the zone's ordinary region
        /// set, or from the distinguished GIC region.
        #[invariant]
        pub fn inv_iommu_in_zone_regions(&self) -> bool {
            forall|zid: nat, r: MemoryRegion|
                self.zones.contains_key(zid) && #[trigger] self.zones[zid].iommu_mem_set.regions.contains(r)
                    ==> #[trigger] zone_regions(zid).contains(r) || r == gic_region()
        }

        // ── Properties ─────────────────────────────────────────────────────────────

        property! {
            cross_zone_disjoint(zid1: nat, zone1: GhostZone, zid2: nat, zone2: GhostZone) {
                have zones >= [zid1 => zone1];
                have zones >= [zid2 => zone2];
                require(zid1 != zid2);
                assert(forall|r1: MemoryRegion, r2: MemoryRegion| #![auto]
                    zone1.cpu_mem_set.regions.contains(r1) && zone2.cpu_mem_set.regions.contains(r2)
                        ==> !r1.spec_overlaps_pmem(r2)
                ) by {
                    assert forall|r1: MemoryRegion, r2: MemoryRegion| #![auto]
                        zone1.cpu_mem_set.regions.contains(r1) && zone2.cpu_mem_set.regions.contains(r2)
                        implies !r1.spec_overlaps_pmem(r2) by {
                        assert(pre.zones.contains_key(zid1));
                        assert(pre.zones.contains_key(zid2));
                        assert(pre.zones[zid1] == zone1);
                        assert(pre.zones[zid2] == zone2);

                        assert(zone_regions(zid1).contains(r1));
                        assert(zone_regions(zid2).contains(r2));

                        zone_regions_pairwise_disjoint();
                    };
                };
            }
        }

        // ── Transitions ─────────────────────────────────────────────────────────────

        init! {
            initialize() {
                init zone_ids = Set::empty();
                init zones = Map::empty();
            }
        }

        transition! {
            add_zone(zid: nat) {
                require(!pre.zone_ids.contains(zid));
                update zone_ids = pre.zone_ids.insert(zid);
                add zones += [zid => GhostZone {
                    cpu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
                    iommu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
                }];
            }
        }

        /// Remove a zone.
        transition! {
            remove_zone(zid: nat) {
                remove zones -= [zid => let _zone];
                update zone_ids = pre.zone_ids.remove(zid);
            }
        }

        transition! {
            cpu_insert_region(zid: nat, region: MemoryRegion) {
                remove zones -= [zid => let zone];
                require(zone_regions(zid).contains(region));
                require(!zone.cpu_mem_set.regions.contains(region));
                require(!zone.cpu_mem_set.overlaps_vmem(region));
                add zones += [zid => zone.cpu_insert_region(region)];
            }
        }

        transition! {
            cpu_remove_region(zid: nat, region: MemoryRegion) {
                remove zones -= [zid => let zone];
                require(zone.cpu_mem_set.regions.contains(region));
                add zones += [zid => zone.cpu_remove_region(region)];
            }
        }

        transition! {
            iommu_insert_region(zid: nat, region: MemoryRegion) {
                remove zones -= [zid => let zone];
                require(zone_regions(zid).contains(region) || region == gic_region());
                require(!zone.iommu_mem_set.regions.contains(region));
                require(!zone.iommu_mem_set.overlaps_vmem(region));
                add zones += [zid => zone.iommu_insert_region(region)];
            }
        }

        transition! {
            iommu_remove_region(zid: nat, region: MemoryRegion) {
                remove zones -= [zid => let zone];
                require(zone.iommu_mem_set.regions.contains(region));
                add zones += [zid => zone.iommu_remove_region(region)];
            }
        }

        // ── Inductive proofs ────────────────────────────────────────────────────────

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(add_zone)]
        fn add_zone_inductive(pre: Self, post: Self, zid: nat) {
            // The new zone is always empty; all invariants are trivially preserved.
            assert(post.zones.dom() == post.zone_ids);
            // inv_zones_wf: empty zone has SpecMemorySet::wf() vacuously true.
            assert forall|zid2: nat| post.zones.contains_key(zid2)
                implies #[trigger] post.zones[zid2].wf() by {
                if zid2 != zid {
                    assert(post.zones[zid2] == pre.zones[zid2]);
                }
            };
            // inv_zone_within_budget: new zone is empty so the forall is vacuously true.
            assert forall|zid2: nat, r: MemoryRegion|
                post.zones.contains_key(zid2) && #[trigger] post.zones[zid2].cpu_mem_set.regions.contains(r)
                implies #[trigger] zone_regions(zid2).contains(r) by {
                if zid2 == zid {
                    assert(post.zones[zid].cpu_mem_set.regions =~= Set::empty());
                } else {
                    assert(post.zones[zid2] == pre.zones[zid2]);
                    assert(pre.zones.contains_key(zid2));
                }
            };
            assert forall|zid2: nat, r: MemoryRegion|
                post.zones.contains_key(zid2) && #[trigger] post.zones[zid2].iommu_mem_set.regions.contains(r)
                implies #[trigger] zone_regions(zid2).contains(r) || r == gic_region() by {
                if zid2 == zid {
                    assert(post.zones[zid].iommu_mem_set.regions =~= Set::empty());
                } else {
                    assert(post.zones[zid2] == pre.zones[zid2]);
                    assert(pre.zones.contains_key(zid2));
                }
            };
        }

        #[inductive(remove_zone)]
        fn remove_zone_inductive(pre: Self, post: Self, zid: nat) {
            // inv_zone_ids: dom(pre.zones.remove(zid)) == pre.zone_ids.remove(zid)
            assert(post.zones.dom() == post.zone_ids);
            // inv_zones_wf: only remaining zones (all != zid), unchanged from pre
            assert forall|zid2: nat| post.zones.contains_key(zid2)
                implies #[trigger] post.zones[zid2].wf() by {
                assert(post.zones[zid2] == pre.zones[zid2]);
            };
            // inv_zone_within_budget: remaining zones unchanged
            assert forall|zid2: nat, r: MemoryRegion|
                post.zones.contains_key(zid2) && #[trigger] post.zones[zid2].cpu_mem_set.regions.contains(r)
                implies #[trigger] zone_regions(zid2).contains(r) by {
                assert(post.zones[zid2] == pre.zones[zid2]);
                assert(pre.zones.contains_key(zid2));
            };
            assert forall|zid2: nat, r: MemoryRegion|
                post.zones.contains_key(zid2) && #[trigger] post.zones[zid2].iommu_mem_set.regions.contains(r)
                implies #[trigger] zone_regions(zid2).contains(r) || r == gic_region() by {
                assert(post.zones[zid2] == pre.zones[zid2]);
                assert(pre.zones.contains_key(zid2));
            };
        }

        #[inductive(cpu_insert_region)]
        fn cpu_insert_region_inductive(pre: Self, post: Self, zid: nat, region: MemoryRegion) {
            let old_zone = pre.zones[zid];
            let new_zone = post.zones[zid];
            // inv_zone_ids: zone_ids unchanged; zones replaces value at zid only
            assert(post.zones.dom() == post.zone_ids);
            // inv_zones_wf
            assert forall|zid2: nat| post.zones.contains_key(zid2)
                implies #[trigger] post.zones[zid2].wf() by {
                if zid2 == zid {
                    assert(old_zone.wf());
                    assert(new_zone == old_zone.cpu_insert_region(region));
                    // `region` is valid (in zone_regions, which are valid); the transition
                    // requires non-overlap and non-membership on the CPU set, so the
                    // SpecMemorySet wf-preservation lemma discharges `new_zone.cpu_mem_set.wf()`.
                    configured_regions_valid();
                    assert(region.spec_valid());
                    assert(new_zone.cpu_mem_set == old_zone.cpu_mem_set.insert_region(region));
                    old_zone.cpu_mem_set.lemma_insert_region_wf(region);
                    assert(new_zone.iommu_mem_set == old_zone.iommu_mem_set);
                    assert(new_zone.wf());
                } else {
                    assert(post.zones[zid2] == pre.zones[zid2]);
                }
            };
            // inv_zone_within_budget: new region by require; old regions and other zones from pre
            assert forall|zid2: nat, r: MemoryRegion|
                post.zones.contains_key(zid2) && #[trigger] post.zones[zid2].cpu_mem_set.regions.contains(r)
                implies #[trigger] zone_regions(zid2).contains(r) by {
                if zid2 == zid {
                    assert(new_zone == old_zone.cpu_insert_region(region));
                    if r != region {
                        assert(old_zone.cpu_mem_set.regions.contains(r));
                        assert(pre.zones.contains_key(zid));
                    }
                } else {
                    assert(post.zones[zid2] == pre.zones[zid2]);
                    assert(pre.zones.contains_key(zid2));
                }
            };
            assert forall|zid2: nat, r: MemoryRegion|
                post.zones.contains_key(zid2) && #[trigger] post.zones[zid2].iommu_mem_set.regions.contains(r)
                implies #[trigger] zone_regions(zid2).contains(r) || r == gic_region() by {
                if zid2 == zid {
                    assert(new_zone.iommu_mem_set == old_zone.iommu_mem_set);
                } else {
                    assert(post.zones[zid2] == pre.zones[zid2]);
                    assert(pre.zones.contains_key(zid2));
                }
            };
        }

        #[inductive(cpu_remove_region)]
        fn cpu_remove_region_inductive(pre: Self, post: Self, zid: nat, region: MemoryRegion) {
            let old_zone = pre.zones[zid];
            let new_zone = post.zones[zid];
            // inv_zone_ids: zone_ids unchanged; zones replaces value at zid only
            assert(post.zones.dom() == post.zone_ids);
            // inv_zones_wf: removing a region preserves wf (regions() shrinks)
            assert forall|zid2: nat| post.zones.contains_key(zid2)
                implies #[trigger] post.zones[zid2].wf() by {
                if zid2 == zid {
                    assert(old_zone.wf());
                    assert(new_zone == old_zone.cpu_remove_region(region));
                    // transition requires `region` is present in the CPU set; the
                    // wf-preservation lemma discharges `new_zone.cpu_mem_set.wf()`.
                    assert(new_zone.cpu_mem_set == old_zone.cpu_mem_set.remove_region_exact(region));
                    old_zone.cpu_mem_set.lemma_remove_region_exact_wf(region);
                    assert(new_zone.iommu_mem_set == old_zone.iommu_mem_set);
                    assert(new_zone.wf());
                } else {
                    assert(post.zones[zid2] == pre.zones[zid2]);
                }
            };
            assert forall|zid2: nat, r: MemoryRegion|
                post.zones.contains_key(zid2) && #[trigger] post.zones[zid2].cpu_mem_set.regions.contains(r)
                implies #[trigger] zone_regions(zid2).contains(r) by {
                if zid2 == zid {
                    assert(new_zone == old_zone.cpu_remove_region(region));
                    assert(old_zone.cpu_mem_set.regions.contains(r));
                    assert(pre.zones.contains_key(zid));
                } else {
                    assert(post.zones[zid2] == pre.zones[zid2]);
                    assert(pre.zones.contains_key(zid2));
                }
            };
            assert forall|zid2: nat, r: MemoryRegion|
                post.zones.contains_key(zid2) && #[trigger] post.zones[zid2].iommu_mem_set.regions.contains(r)
                implies #[trigger] zone_regions(zid2).contains(r) || r == gic_region() by {
                if zid2 == zid {
                    assert(new_zone.iommu_mem_set == old_zone.iommu_mem_set);
                } else {
                    assert(post.zones[zid2] == pre.zones[zid2]);
                    assert(pre.zones.contains_key(zid2));
                }
            };
        }

        #[inductive(iommu_insert_region)]
        fn iommu_insert_region_inductive(pre: Self, post: Self, zid: nat, region: MemoryRegion) {
            let old_zone = pre.zones[zid];
            let new_zone = post.zones[zid];
            // inv_zone_ids: zone_ids unchanged; zones replaces value at zid only
            assert(post.zones.dom() == post.zone_ids);
            // inv_zones_wf
            assert forall|zid2: nat| post.zones.contains_key(zid2)
                implies #[trigger] post.zones[zid2].wf() by {
                if zid2 == zid {
                    assert(old_zone.wf());
                    assert(new_zone == old_zone.iommu_insert_region(region));
                    // `region` is valid (in zone_regions or the GIC region, both valid);
                    // the transition requires non-overlap and non-membership on the IOMMU set.
                    configured_regions_valid();
                    assert(region.spec_valid());
                    assert(new_zone.iommu_mem_set == old_zone.iommu_mem_set.insert_region(region));
                    old_zone.iommu_mem_set.lemma_insert_region_wf(region);
                    assert(new_zone.cpu_mem_set == old_zone.cpu_mem_set);
                    assert(new_zone.wf());
                } else {
                    assert(post.zones[zid2] == pre.zones[zid2]);
                }
            };
            assert forall|zid2: nat, r: MemoryRegion|
                post.zones.contains_key(zid2) && #[trigger] post.zones[zid2].cpu_mem_set.regions.contains(r)
                implies #[trigger] zone_regions(zid2).contains(r) by {
                if zid2 == zid {
                    assert(new_zone.cpu_mem_set == old_zone.cpu_mem_set);
                } else {
                    assert(post.zones[zid2] == pre.zones[zid2]);
                    assert(pre.zones.contains_key(zid2));
                }
            };
            assert forall|zid2: nat, r: MemoryRegion|
                post.zones.contains_key(zid2) && #[trigger] post.zones[zid2].iommu_mem_set.regions.contains(r)
                implies #[trigger] zone_regions(zid2).contains(r) || r == gic_region() by {
                if zid2 == zid {
                    assert(new_zone == old_zone.iommu_insert_region(region));
                    if r != region {
                        assert(old_zone.iommu_mem_set.regions.contains(r));
                        assert(pre.zones.contains_key(zid));
                    }
                } else {
                    assert(post.zones[zid2] == pre.zones[zid2]);
                    assert(pre.zones.contains_key(zid2));
                }
            };
        }

        #[inductive(iommu_remove_region)]
        fn iommu_remove_region_inductive(pre: Self, post: Self, zid: nat, region: MemoryRegion) {
            let old_zone = pre.zones[zid];
            let new_zone = post.zones[zid];
            // inv_zone_ids: zone_ids unchanged; zones replaces value at zid only
            assert(post.zones.dom() == post.zone_ids);
            // inv_zones_wf
            assert forall|zid2: nat| post.zones.contains_key(zid2)
                implies #[trigger] post.zones[zid2].wf() by {
                if zid2 == zid {
                    assert(old_zone.wf());
                    assert(new_zone == old_zone.iommu_remove_region(region));
                    // transition requires `region` is present in the IOMMU set.
                    assert(new_zone.iommu_mem_set == old_zone.iommu_mem_set.remove_region_exact(region));
                    old_zone.iommu_mem_set.lemma_remove_region_exact_wf(region);
                    assert(new_zone.cpu_mem_set == old_zone.cpu_mem_set);
                    assert(new_zone.wf());
                } else {
                    assert(post.zones[zid2] == pre.zones[zid2]);
                }
            };
            assert forall|zid2: nat, r: MemoryRegion|
                post.zones.contains_key(zid2) && #[trigger] post.zones[zid2].cpu_mem_set.regions.contains(r)
                implies #[trigger] zone_regions(zid2).contains(r) by {
                if zid2 == zid {
                    assert(new_zone.cpu_mem_set == old_zone.cpu_mem_set);
                } else {
                    assert(post.zones[zid2] == pre.zones[zid2]);
                    assert(pre.zones.contains_key(zid2));
                }
            };
            assert forall|zid2: nat, r: MemoryRegion|
                post.zones.contains_key(zid2) && #[trigger] post.zones[zid2].iommu_mem_set.regions.contains(r)
                implies #[trigger] zone_regions(zid2).contains(r) || r == gic_region() by {
                if zid2 == zid {
                    assert(new_zone == old_zone.iommu_remove_region(region));
                    assert(old_zone.iommu_mem_set.regions.contains(r));
                    assert(pre.zones.contains_key(zid));
                } else {
                    assert(post.zones[zid2] == pre.zones[zid2]);
                    assert(pre.zones.contains_key(zid2));
                }
            };
        }
    }
}
// ── Token type aliases ─────────────────────────────────────────────────────────


/// `BudgetSpec` instance token (constant-sharded, shared by reference).
pub type BudgetSpecInstance = BudgetSpec::Instance;

/// Global zone-id set token (variable-sharded; held in the HvMem global lock).
pub type BudgetZoneIdsToken = BudgetSpec::zone_ids;

/// Per-zone zone-state token (map-sharded; lives in the zone-level lock).
pub type BudgetZoneToken = BudgetSpec::zones;

} // verus!
