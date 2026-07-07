//! Core ghost state machine for the hypervisor memory manager (assumption 1: `all_regions`).
//!
//! Defines:
//! - `all_regions()`: the system-wide set of valid, disjoint physical memory regions.
//! - `GhostZone`: per-zone ghost state bundling allocator instance and memory-set spec.
//! - `ClosureSpec`: tokenized state machine tracking zone membership and the global region closure.
//! - Token type aliases derived from `ClosureSpec`.
//!
//! The two axioms `all_regions_valid` and `all_regions_disjoint` represent the assumption that
//! physical memory partitioning is correct by construction (guaranteed by the configuration
//! toolchain), without requiring a runtime proof.
//!
//! This is the **weak** (assumption-1) specification.  The stronger per-zone-budget variant
//! lives in `strong_spec` (`BudgetSpec`).
use super::GhostZone;
use crate::{
    address::{addr::SpecVAddr, region::MemoryRegion},
    memory_set::SpecMemorySet,
};
use verus_state_machines_macros::tokenized_state_machine;
use vstd::{prelude::*, tokens::InstanceId};

verus! {

/// Abstract function representing the set of all possible memory regions that can be
/// statically configured in the system.
pub uninterp spec fn all_regions() -> Set<MemoryRegion>;

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

// Assumption-1 state machine: tracks the global region closure across all zones.
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

            /// Union of all regions from all zones.
            #[sharding(variable)]
            pub region_closure: Set<MemoryRegion>,
        }

        /// `zone_ids` is always the exact set of keys in `zones`
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

        /// `region_closure` is exactly the union of all zones' region sets.
        #[invariant]
        pub fn inv_region_closure(&self) -> bool {
            forall|region: MemoryRegion|
                self.region_closure.contains(region) <==> exists|zid: nat|
                    self.zones.contains_key(zid) && #[trigger] self.zones[zid].contains_region(region)
        }

        /// `region_closure` is a subset of `all_regions()`.
        ///
        /// Combined with the `all_regions_disjoint()` axiom, this implies P1 (RegionDisjoint):
        /// any two distinct regions in `region_closure` are non-overlapping, because they both
        /// live in `all_regions()` which is axiomatically pairwise disjoint.
        #[invariant]
        pub fn inv_region_closure_subset(&self) -> bool {
            forall|r: MemoryRegion| #[trigger] self.region_closure.contains(r) ==> all_regions().contains(r)
        }

        /// Each region belongs to at most one zone.
        ///
        /// Together with `inv_region_closure_subset` and `all_regions_disjoint()`, this
        /// closes the proof of P1 (RegionDisjoint): `inv_region_closure_subset` handles
        /// the `r1 ≠ r2` case via the axiom, and `inv_region_unique_owner` rules out the
        /// `r1 = r2` case for distinct zones.  It is preserved by `insert_region` because
        /// the precondition `!region_closure.contains(region)` forbids adding a region
        /// already owned by any zone.
        #[invariant]
        pub fn inv_region_unique_owner(&self) -> bool {
            forall|r: MemoryRegion, zid1: nat, zid2: nat|
                self.zones.contains_key(zid1) && self.zones.contains_key(zid2)
                && #[trigger] self.zones[zid1].contains_region(r)
                && #[trigger] self.zones[zid2].contains_region(r)
                    ==> zid1 == zid2
        }

        // ── Properties ────────────────────────────────────────────────────────────
        // Properties are read-only lemmas that zone-token holders can invoke to learn
        // facts about the global state, analogous to `free_client_disjoint` in `AllocSpec`.

        /// Any region that belongs to zone `zid` is tracked in the global `region_closure`.
        ///
        /// Proof sketch: `have zones >= [zid => zone]` gives `pre.zones[zid] == zone` and
        /// `pre.zones.contains_key(zid)`.  For any `r` in `zone.region_set`:
        ///   `zone.contains_region(r)` = `pre.zones[zid].contains_region(r)`, so the
        ///   existential in `inv_region_closure` is satisfied, hence `region_closure.contains(r)`.
        property! {
            zone_region_in_closure(zid: nat, zone: GhostZone) {
                have zones >= [zid => zone];
                assert(forall|r: MemoryRegion|
                    #[trigger] zone.regions().contains(r) ==> pre.region_closure.contains(r)
                ) by {
                    assert forall|r: MemoryRegion| #[trigger] zone.regions().contains(r)
                        implies pre.region_closure.contains(r) by {
                        assert(pre.zones.contains_key(zid) && pre.zones[zid].contains_region(r));
                    };
                };
            }
        }

        /// Regions from two *distinct* zones are mutually non-overlapping.
        ///
        /// Proof sketch (P1 derivation):
        /// - From `inv_region_closure`, every region of either zone is in `region_closure`.
        /// - From `inv_region_closure_subset`, every region in `region_closure` is in `all_regions()`.
        /// - If r1 ≠ r2: `all_regions_disjoint()` gives `!r1.spec_overlaps_pmem(r2)` directly.
        /// - If r1 = r2: `inv_region_unique_owner` says the same region cannot belong to two
        ///   different zones (`zid1 != zid2`), so this case is vacuously impossible.
        property! {
            cross_zone_disjoint(zid1: nat, zone1: GhostZone, zid2: nat, zone2: GhostZone) {
                have zones >= [zid1 => zone1];
                have zones >= [zid2 => zone2];
                require(zid1 != zid2);
                assert(forall|r1: MemoryRegion, r2: MemoryRegion| #![auto]
                    zone1.regions().contains(r1) && zone2.regions().contains(r2)
                        ==> !r1.spec_overlaps_pmem(r2)
                ) by {
                    assert forall|r1: MemoryRegion, r2: MemoryRegion| #![auto]
                        zone1.regions().contains(r1) && zone2.regions().contains(r2) implies !r1.spec_overlaps_pmem(r2) by {
                        assert(pre.zones.contains_key(zid1) && pre.zones[zid1].contains_region(r1));
                        assert(pre.zones.contains_key(zid2) && pre.zones[zid2].contains_region(r2));
                        if r1 != r2 {
                            // Both are in region_closure (via inv_region_closure), hence in
                            // all_regions() (via inv_region_closure_subset). Apply the axiom.
                            assert(pre.region_closure.contains(r1) && pre.region_closure.contains(r2));
                            assert(all_regions().contains(r1) && all_regions().contains(r2));
                            all_regions_disjoint();
                        } else {
                            // r1 == r2 but zid1 != zid2 contradicts inv_region_unique_owner.
                            assert(false);
                        }
                    }
                };
            }
        }

        /// P2 (ZoneIsolated): every mapped translation in a zone stays within the declaring
        /// region's physical range.
        ///
        /// Derivation: `inv_zones_wf` gives `zone.wf()` which includes `zone.cpu_mem_set.wf()`,
        /// so every region `r` in the zone satisfies `r.spec_valid()`.  For any virtual
        /// address `v` mapped in the zone, `SpecMemorySet::translate` chooses the same `r`
        /// that `contains_vaddr` witnesses.  `MemoryRegion::lemma_contains_vaddr_implies_contains_paddr`
        /// then gives `r.spec_contains_paddr(r.spec_translate(v))`, which is exactly P2.
        property! {
            zone_isolated(zid: nat, zone: GhostZone, v: SpecVAddr) {
                have zones >= [zid => zone];
                require(zone.cpu_mem_set.contains_vaddr(v));
                assert(zone.wf());
                assert({
                    let paddr = zone.cpu_mem_set.translate(v);
                    // Same predicate as `contains_vaddr` / `translate`, so the same
                    // region witness is chosen.
                    let r = choose|r: MemoryRegion|
                        zone.cpu_mem_set.regions.contains(r) && #[trigger] r.spec_contains_vaddr(v);
                    r.spec_contains_paddr(paddr)
                }) by {
                    // inv_zones_wf => zone.wf() => zone.cpu_mem_set.wf()
                    let paddr = zone.cpu_mem_set.translate(v);
                    assert(zone.cpu_mem_set.wf());
                    assert(zone.cpu_mem_set.contains_vaddr(v));  // from require
                    let r = choose|r: MemoryRegion|
                        zone.cpu_mem_set.regions.contains(r) && #[trigger] r.spec_contains_vaddr(v);
                    assert(zone.cpu_mem_set.regions.contains(r) && r.spec_contains_vaddr(v));
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
                init region_closure = Set::empty();
            }
        }

        /// Add an empty zone. Regions are inserted afterwards via `insert_region`.
        ///
        /// Because the new zone is always empty, no region-membership or
        /// disjointness conditions are needed at zone-creation time.
        /// `region_closure` is left unchanged.
        transition! {
            add_zone(zid: nat) {
                require(!pre.zone_ids.contains(zid));
                update zone_ids = pre.zone_ids.insert(zid);
                add zones += [zid => GhostZone {
                    cpu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
                    iommu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
                }];
                // region_closure is unchanged — empty zone contributes no regions.
            }
        }

        /// Remove an entire zone and subtract its regions from the closure.
        ///
        /// Note: callers are responsible for draining all page-table frames and physical
        /// memory before invoking this transition; the spec-level token is simply dropped.
        transition! {
            remove_zone(zid: nat) {
                remove zones -= [zid => let zone];
                update zone_ids = pre.zone_ids.remove(zid);
                update region_closure = pre.region_closure.difference(zone.regions());
            }
        }

        /// Insert one region into an existing zone.
        ///
        /// The key preconditions are:
        /// - `region` belongs to `all_regions()` (static configuration membership), which
        ///   maintains `inv_region_closure_subset` and, via `all_regions_disjoint()`, implies
        ///   disjointness from every existing region in the closure.
        /// - `region` is not already in `region_closure`, which maintains
        ///   `inv_region_unique_owner` (rules out the same-region case where two zones would
        ///   both claim the region).
        transition! {
            insert_region(zid: nat, region: MemoryRegion) {
                remove zones -= [zid => let zone];
                require(region.spec_valid());
                require(all_regions().contains(region));
                require(!zone.cpu_mem_set.overlaps_vmem(region));
                require(!pre.region_closure.contains(region));
                add zones += [zid => zone.insert_region(region)];
                update region_closure = pre.region_closure.insert(region);
            }
        }

        /// Remove one region from an existing zone.
        transition! {
            remove_region(zid: nat, region: MemoryRegion) {
                remove zones -= [zid => let zone];
                require(zone.contains_region(region));
                add zones += [zid => zone.remove_region(region)];
                update region_closure = pre.region_closure.remove(region);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(add_zone)]
        fn add_zone_inductive(pre: Self, post: Self, zid: nat) {
            // - inv_zone_ids: trivially preserved (dom update matches zone_ids update).
            assert(post.zones.dom() == post.zone_ids);
            // - inv_zones_wf: empty zone has SpecMemorySet::wf() vacuously true.
            assert(forall|zid2: nat| post.zones.contains_key(zid2) ==> #[trigger] post.zones[zid2].wf());
            // - inv_region_closure: region_closure is unchanged; new zone is empty so
            //                       it contributes no regions to either side of the iff.
            assert forall|region: MemoryRegion| post.region_closure.contains(region) <==>
                (exists|zid2: nat| post.zones.contains_key(zid2)
                    && #[trigger] post.zones[zid2].contains_region(region)) by {
                // ── forward: post.region_closure == pre.region_closure => use pre invariant ──
                if post.region_closure.contains(region) {
                    assert(exists|z: nat|
                        pre.zones.contains_key(z) && #[trigger] pre.zones[z].contains_region(region));
                    let zid2 = choose|z: nat|
                        pre.zones.contains_key(z) && #[trigger] pre.zones[z].contains_region(region);
                    // zid was absent from pre.zones, so zid2 != zid
                    assert(zid2 != zid);
                    assert(post.zones[zid2] == pre.zones[zid2]);
                }
                // ── backward: new zone is empty, so only pre zones contribute ─────────────
                if exists|z: nat| post.zones.contains_key(z) &&
                    #[trigger] post.zones[z].contains_region(region) {
                    let zid2 = choose|z: nat| post.zones.contains_key(z) &&
                        #[trigger] post.zones[z].contains_region(region);
                    if zid2 == zid {
                        // empty zone — region cannot be contained; contradiction
                        assert(post.zones[zid].regions() =~= Set::empty());
                        assert(false);
                    } else {
                        assert(pre.zones.contains_key(zid2));
                        assert(pre.zones[zid2].contains_region(region));
                        assert(post.zones[zid2] == pre.zones[zid2]);
                    }
                }
            };
            // - inv_region_closure_subset: region_closure unchanged; subset preserved.
            // - inv_region_unique_owner: new zone is empty, no new region ownership.
        }

        #[inductive(remove_zone)]
        fn remove_zone_inductive(pre: Self, post: Self, zid: nat) {
            // - inv_zone_ids:              post.zone_ids = pre.zone_ids.remove(zid).
            assert(post.zones.dom() == post.zone_ids);
            // - inv_zones_wf:              only old zones remain, all wf by induction.
            assert(forall|zid2: nat| post.zones.contains_key(zid2) ==> #[trigger] post.zones[zid2].wf());
            // - inv_region_closure:        post.region_closure = pre.region_closure.difference(zone.regions());
            //                             a region is in post.closure iff it's in some remaining zone,
            //                             using Set::difference semantics + inv_region_closure on pre.
            let removed = pre.zones[zid];
            assert forall|region: MemoryRegion| post.region_closure.contains(region) <==>
                (exists|zid2: nat| post.zones.contains_key(zid2)
                    && #[trigger] post.zones[zid2].contains_region(region)) by {
                // ── forward: post.region_closure => exists zid2 in post.zones ───────
                if post.region_closure.contains(region) {
                    // post.region_closure = pre.region_closure.difference(removed.regions()), so
                    // region ∈ pre.region_closure AND region ∉ removed.regions()
                    assert(!removed.regions().contains(region));
                    // pre.inv_region_closure gives us a witness in pre.zones
                    assert(exists|z: nat|
                        pre.zones.contains_key(z) && #[trigger] pre.zones[z].contains_region(region));
                    let zid2 = choose|z: nat|
                        pre.zones.contains_key(z) && #[trigger] pre.zones[z].contains_region(region);
                    // zid2 != zid: region ∉ removed.regions() = pre.zones[zid].regions()
                    assert(zid2 != zid);
                    // post.zones = pre.zones.remove(zid); for zid2 != zid the value is unchanged
                    assert(post.zones.contains_key(zid2));
                    assert(post.zones[zid2] == pre.zones[zid2]);
                    assert(post.zones[zid2].contains_region(region));
                }
                // ── backward: exists zid2 in post.zones => post.region_closure ───────
                if exists|z: nat| post.zones.contains_key(z) &&
                    #[trigger] post.zones[z].contains_region(region) {
                    let zid2 = choose|z: nat| post.zones.contains_key(z) &&
                        #[trigger] post.zones[z].contains_region(region);
                    if zid2 == zid {
                        // contradiction: zid was removed from post.zones
                        assert(false);
                    } else {
                        // zid2 was already in pre.zones; pre.inv_region_closure gives containment
                        assert(pre.zones.contains_key(zid2));
                        assert(post.zones[zid2] == pre.zones[zid2]);
                        assert(pre.zones[zid2].contains_region(region));
                        // region ∉ removed.regions(): by inv_region_unique_owner, only zid2 owns
                        // region; if zid also owned it, inv_region_unique_owner would force zid == zid2.
                        assert(!removed.regions().contains(region)) by {
                            if removed.regions().contains(region) {
                                assert(pre.zones.contains_key(zid) && pre.zones[zid].contains_region(region));
                                // inv_region_unique_owner forces zid == zid2, contradicting zid2 != zid
                                assert(zid == zid2);
                            }
                        };
                        // post.region_closure = pre.region_closure.difference(removed.regions())
                        assert(post.region_closure.contains(region));
                    }
                }
            };
            // - inv_region_closure_subset: post.region_closure ⊆ pre.region_closure ⊆ all_regions();
            //                             Set::difference only removes elements, subset preserved.
            assert(forall|r: MemoryRegion| #[trigger] post.region_closure.contains(r) ==> all_regions().contains(r));
            // - inv_region_unique_owner:   subset of pre.zones, unique-owner preserved.
            assert(forall|r: MemoryRegion, zid1: nat, zid2: nat|
                post.zones.contains_key(zid1) && post.zones.contains_key(zid2)
                && #[trigger] post.zones[zid1].contains_region(r)
                && #[trigger] post.zones[zid2].contains_region(r)
                    ==> zid1 == zid2
            );
        }

        #[inductive(insert_region)]
        fn insert_region_inductive(pre: Self, post: Self, zid: nat, region: MemoryRegion) {
            let old_zone = pre.zones[zid];
            let new_zone = post.zones[zid];
            // - inv_zone_ids:              zones changes key zid's value only; zone_ids unchanged.
            // - inv_zones_wf:              for zid: require(region.spec_valid()) + require(all_regions())
            //                              + pre zone wf => post zone wf (via insert_region spec fn);
            //                              other zids unchanged.
            assert forall|zid2: nat| post.zones.contains_key(zid2)
                implies #[trigger] post.zones[zid2].wf() by {
                if zid2 == zid {
                    assert(old_zone.wf());
                    assert(new_zone == old_zone.insert_region(region));
                    // `region` is not already in this zone: `!pre.region_closure.contains(region)`
                    // + `inv_region_closure` ⇒ it is in no zone.  Then the SpecMemorySet
                    // wf-preservation lemma discharges `new_zone.cpu_mem_set.wf()`.
                    assert(!old_zone.contains_region(region)) by {
                        if old_zone.contains_region(region) {
                            assert(pre.region_closure.contains(region));
                        }
                    }
                    assert(!old_zone.cpu_mem_set.regions.contains(region));
                    assert(new_zone.cpu_mem_set == old_zone.cpu_mem_set.insert_region(region));
                    old_zone.cpu_mem_set.lemma_insert_region_wf(region);
                    assert(new_zone.iommu_mem_set == old_zone.iommu_mem_set);
                    assert(new_zone.wf());
                } else {
                    assert(post.zones[zid2] == pre.zones[zid2]);
                }
            }
            // - inv_region_closure:        post.region_closure = pre.region_closure.insert(region);
            //                             the new region is in post.zones[zid].region_set.
            assert forall|region2: MemoryRegion| post.region_closure.contains(region2) <==>
                (exists|zid2: nat| post.zones.contains_key(zid2)
                    && #[trigger] post.zones[zid2].contains_region(region2)) by {
                // ── forward: post.region_closure => exists zid2 in post.zones ───────
                if post.region_closure.contains(region2) {
                    // post.region_closure = pre.region_closure.union(new_zone.regions())
                    if region2 != region {
                        assert(pre.region_closure.contains(region2));
                        // pre.inv_region_closure gives us a witness in pre.zones
                        assert(exists|z: nat|
                            pre.zones.contains_key(z) && #[trigger] pre.zones[z].contains_region(region2));
                        let zid2 = choose|z: nat|
                            pre.zones.contains_key(z) && #[trigger] pre.zones[z].contains_region(region2);
                        assert(post.zones.contains_key(zid2));
                        if zid2 == zid {
                            assert(post.zones[zid] == new_zone);
                            assert(new_zone == old_zone.insert_region(region));
                            assert(old_zone.contains_region(region2));
                            assert(post.zones[zid2].contains_region(region2));
                        } else {
                            assert(post.zones[zid2] == pre.zones[zid2]);
                            assert(post.zones[zid2].contains_region(region2));
                        }
                    } else {
                        // region must be in new_zone.regions() (the other part of the union)
                        assert(new_zone.regions().contains(region2));
                        // post.zones[zid] = new_zone
                        assert(post.zones.contains_key(zid) && post.zones[zid] == new_zone);
                        assert(post.zones[zid].contains_region(region2));
                    }
                }
                // ── backward: exists zid2 in post.zones => post.region_closure ───────
                if exists|z: nat| post.zones.contains_key(z) &&
                    #[trigger] post.zones[z].contains_region(region2) {
                    let zid2 = choose|z: nat| post.zones.contains_key(z) &&
                        #[trigger] post.zones[z].contains_region(region2);
                    if zid2 == zid {
                        // post.zones[zid] = new_zone; for post.region_closure=pre.insert(region),
                        // split on whether region2 is the newly inserted region.
                        assert(post.zones[zid] == new_zone);
                        if region2 == region {
                            assert(post.region_closure.contains(region2));
                        } else {
                            assert(new_zone == old_zone.insert_region(region));
                            assert(old_zone.contains_region(region2));
                            assert(pre.zones.contains_key(zid) && pre.zones[zid].contains_region(region2));
                            assert(pre.region_closure.contains(region2));
                            assert(post.region_closure.contains(region2));
                        }
                    } else {
                        // zid2 was already in pre.zones; pre.inv_region_closure gives containment
                        assert(pre.zones.contains_key(zid2));
                        assert(pre.zones[zid2].contains_region(region2));
                        assert(pre.region_closure.contains(region2));
                        assert(post.zones[zid2] == pre.zones[zid2]);
                        // pre.region_closure ⊆ post.region_closure (union includes it)
                        assert(post.region_closure.contains(region2));
                    }
                }
            };
            // - inv_region_closure_subset: require(all_regions().contains(region)) covers the new region;
            //                             pre.region_closure ⊆ all_regions() by induction; union preserved.
            // - inv_region_unique_owner:   require(!pre.region_closure.contains(region)) ensures the
            //                             region was not already in any zone; now only in zid.
            admit();
        }

        #[inductive(remove_region)]
        fn remove_region_inductive(pre: Self, post: Self, zid: nat, region: MemoryRegion) {
            // TODO: discharge:
            // - inv_zone_ids:              zones changes key zid's value only; zone_ids unchanged.
            // - inv_zones_wf:              removing a region from a wf zone keeps it wf.
            // - inv_region_closure:        post.region_closure = pre.region_closure.remove(region);
            //                             the removed region is no longer in any zone.
            // - inv_region_closure_subset: post.region_closure ⊆ pre.region_closure ⊆ all_regions();
            //                             Set::remove only removes elements, subset preserved.
            // - inv_region_unique_owner:   subset of pre.zones[zid].region_set; preserved.
            // P2 (zone_isolated) is a derived property, not an invariant; no discharge needed.
            admit();
        }
    }
}
// ── Token type aliases ────────────────────────────────────────────────────────


pub type ClosureSpecInstance = ClosureSpec::Instance;

pub type ClosureZoneIdsToken = ClosureSpec::zone_ids;

pub type ClosureZoneToken = ClosureSpec::zones;

pub type ClosureRegionToken = ClosureSpec::region_closure;

} // verus!
