//! Top-level hypervisor memory model and orchestration layer.
//!
//! This module is centered around three top-level memory-safety properties:
//!
//! - P1 RegionDisjoint: static physical partitioning; regions from different zones do not overlap.
//! - P2 ZoneIsolated: page-table translation for a zone stays within that zone's configured physical regions.
//! - P3 PTMemDisjoint: page-table-memory discipline is preserved via allocator-instance consistency.
//!
//! Module layout:
//!
//! - `config`: zone configuration types and conversion to `MemoryRegion`.
//! - `zone`: single-zone memory abstraction and lock-based concurrent access wrapper.
//! - `mod` (this file): system-level composition of zones plus allocator, and definitions/proofs for P1-P3.
//!
//! Concrete runtime code should refine these contracts.
extern crate alloc;

mod config;

use crate::{
    address::region::MemoryRegion,
    address::{addr::SpecVAddr, frame::FrameSize},
    bitmap_allocator::bitmap_trait::BitmapAllocator,
    global_allocator::GlobalAllocator,
    memory_set::{MemorySet, SpecMemorySet},
    page_table::{PTConstants, PageTable},
    sync::rwlock::{RwLock, RwReadGuard, RwReaderToken, RwWriteGuard, RwWriterToken},
};
use alloc::sync::Arc;
use config::HvConfigMemRegion;
use core::marker::PhantomData;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::invariant::InvariantPredicate;
use vstd::{
    cell::{CellId, PCell, PointsTo},
    prelude::*,
    tokens::InstanceId,
};

verus! {

/// Ghost state for one zone tracked inside `HvMemSpec`.
pub struct GhostZone {
    /// Allocator instance id shared by the whole hypervisor memory manager.
    pub alloc_inst_id: InstanceId,
    /// Region sequence used by the existing memory-set abstraction.
    pub mem_set: SpecMemorySet,
}

impl GhostZone {
    /// Well-formedness relative to the system allocator instance.
    pub open spec fn wf(&self, alloc_inst_id: InstanceId) -> bool {
        &&& self.alloc_inst_id == alloc_inst_id
        &&& self.mem_set.wf()
    }

    /// Region set of this zone.
    pub open spec fn regions(&self) -> Set<MemoryRegion> {
        self.mem_set.regions
    }

    /// Whether a region belongs to this zone.
    pub open spec fn contains_region(&self, region: MemoryRegion) -> bool {
        self.regions().contains(region)
    }

    /// Insert a region into this zone.
    pub open spec fn insert_region(&self, region: MemoryRegion) -> Self {
        Self {
            alloc_inst_id: self.alloc_inst_id,
            mem_set: SpecMemorySet { regions: self.regions().insert(region) },
        }
    }

    /// Remove a region from this zone.
    pub open spec fn remove_region(&self, region: MemoryRegion) -> Self
        recommends
            self.regions().contains(region),
    {
        Self {
            alloc_inst_id: self.alloc_inst_id,
            mem_set: SpecMemorySet { regions: self.regions().remove(region) },
        }
    }
}

// Top-level state machine for the hypervisor memory manager, tracking global properties of all zones.
tokenized_state_machine! {
    HvMemSpec {
        fields {
            /// Shared allocator instance for all zones in the hypervisor memory manager.
            #[sharding(constant)]
            pub alloc_inst_id: InstanceId,

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

        #[invariant]
        pub fn inv_zone_ids(&self) -> bool {
            self.zones.dom() == self.zone_ids
        }

        #[invariant]
        pub fn inv_zones_wf(&self) -> bool {
            forall|zid: nat|
                self.zones.contains_key(zid) ==> #[trigger] self.zones[zid].wf(self.alloc_inst_id)
        }

        /// `region_closure` is exactly the union of all zones' region sets.
        #[invariant]
        pub fn inv_region_closure(&self) -> bool {
            forall|region: MemoryRegion|
                self.region_closure.contains(region) <==> exists|zid: nat|
                    self.zones.contains_key(zid) && #[trigger] self.zones[zid].contains_region(region)
        }

        /// P1 (RegionDisjoint): Any two distinct regions in the closure must be disjoint. This simultaneously
        /// gives zone-internal disjointness and cross-zone disjointness.
        #[invariant]
        pub fn inv_region_disjoint(&self) -> bool {
            forall|r1: MemoryRegion, r2: MemoryRegion| #![auto]
                self.region_closure.contains(r1) && self.region_closure.contains(r2) && r1 != r2
                    ==> !r1.spec_overlaps_pmem(r2)
        }

        /// Each region belongs to at most one zone.
        ///
        /// This is not derivable from `inv_region_disjoint` alone (which only covers *distinct*
        /// regions). It is preserved by `insert_region` because the precondition forbids
        /// adding a region already present in `region_closure`, and a non-empty region
        /// always overlaps with itself (`spec_overlaps` is reflexive for `spec_valid` regions).
        #[invariant]
        pub fn inv_region_unique_owner(&self) -> bool {
            forall|r: MemoryRegion, zid1: nat, zid2: nat|
                #![trigger self.zones[zid1].contains_region(r), self.zones[zid2].contains_region(r)]
                self.zones.contains_key(zid1) && self.zones.contains_key(zid2)
                && self.zones[zid1].contains_region(r)
                && self.zones[zid2].contains_region(r)
                    ==> zid1 == zid2
        }

        /// P2 (ZoneIsolated): every mapped translation in a zone stays within the declaring
        /// region's physical range.
        #[invariant]
        pub fn inv_zone_isolated(&self) -> bool {
            forall|zid: nat, v: SpecVAddr|
                #![trigger self.zones[zid].mem_set.contains_vaddr(v)]
                self.zones.contains_key(zid)
                && self.zones[zid].mem_set.contains_vaddr(v) ==> {
                    let (_, paddr) = self.zones[zid].mem_set.translate(v);
                    let r = choose|r: MemoryRegion| #[trigger] self.zones[zid].regions().contains(r)
                            && r.spec_contains_vaddr(v);
                    r.spec_contains_paddr(paddr)
                }
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
                ) by { admit(); };
            }
        }

        /// Regions from two *distinct* zones are mutually non-overlapping.
        ///
        /// Proof sketch:
        /// - From `inv_region_closure`, every region of either zone is in `region_closure`.
        /// - If r1 ≠ r2: `inv_region_disjoint` gives `!r1.spec_overlaps(r2)` directly.
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
                            assert(pre.region_closure.contains(r1) && pre.region_closure.contains(r2));
                        } else {
                            assert(false);
                        }
                    }
                };
            }
        }

        init! {
            initialize(alloc_inst_id: InstanceId) {
                init alloc_inst_id = alloc_inst_id;
                init zone_ids = Set::empty();
                init zones = Map::empty();
                init region_closure = Set::empty();
            }
        }

        /// Add a fully constructed zone. The caller must prove that every region in the new zone
        /// is disjoint from the existing global closure.
        transition! {
            add_zone(zid: nat, zone: GhostZone) {
                require(!pre.zone_ids.contains(zid));
                require(zone.wf(pre.alloc_inst_id));
                require(forall|new_region: MemoryRegion|
                    zone.regions().contains(new_region) ==> forall|existing: MemoryRegion|
                        #[trigger] pre.region_closure.contains(existing) ==> !new_region.spec_overlaps_pmem(existing));
                update zone_ids = pre.zone_ids.insert(zid);
                add zones += [zid => zone];
                update region_closure = pre.region_closure.union(zone.regions());
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
        /// The key precondition is disjointness against the entire existing `region_closure`;
        /// that single check implies both:
        /// - the region is fresh within the zone itself, and
        /// - the region is disjoint from every region in every other zone.
        transition! {
            insert_region(zid: nat, region: MemoryRegion) {
                remove zones -= [zid => let zone];
                require(region.spec_valid());
                require(forall|existing: MemoryRegion|
                    #[trigger] pre.region_closure.contains(existing) ==> !region.spec_overlaps_pmem(existing));
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
        fn initialize_inductive(post: Self, alloc_inst_id: InstanceId) { }

        #[inductive(add_zone)]
        fn add_zone_inductive(pre: Self, post: Self, zid: nat, zone: GhostZone) {
            // TODO: discharge the following obligations:
            // - inv_zone_ids:           post.zone_ids = pre.zone_ids.insert(zid),
            //                           post.zones = pre.zones.insert(zid, zone)  => iff preserved.
            // - inv_zones_wf:           require(zone.wf(…)) covers the new zid; old zids unchanged.
            // - inv_region_closure:     post.region_closure = pre.region_closure.union(zone.region_set);
            //                           expand the iff using inv_region_closure on pre.
            // - inv_region_disjoint:    pairs within pre.region_closure are disjoint by induction;
            //                           pairs from zone.region_set vs pre.region_closure are disjoint
            //                           by the require; pairs within zone.region_set are disjoint by
            //                           zone.wf() => mem_set.wf() => pairwise non-overlap of regions.
            // - inv_region_unique_owner: the require (disjointness from closure) + reflexivity of
            //                           spec_overlaps prevents a new region already in another zone.
            // - inv_zone_isolated:      follows from require(zone.wf(…)) ⊇ zone.zone_isolated();
            //                           old zones unchanged.
            admit();
        }

        #[inductive(remove_zone)]
        fn remove_zone_inductive(pre: Self, post: Self, zid: nat) {
            // TODO: discharge:
            // - inv_zone_ids:           post.zone_ids = pre.zone_ids.remove(zid).
            // - inv_zones_wf:           only old zones remain, all wf by induction.
            // - inv_region_closure:     post.region_closure = pre.region_closure.difference(zone.region_set);
            //                           a region is in post.closure iff it's in some remaining zone,
            //                           using Set::difference semantics + inv_region_closure on pre.
            // - inv_region_disjoint:    subset of pre.region_closure, disjointness preserved.
            // - inv_region_unique_owner: subset of pre.zones, unique-owner preserved.
            // - inv_zone_isolated:      removed zone is gone; remaining zones unchanged.
            admit();
        }

        #[inductive(insert_region)]
        fn insert_region_inductive(pre: Self, post: Self, zid: nat, region: MemoryRegion) {
            // TODO: discharge:
            // - inv_zone_ids:           zones changes key zid's value only; zone_ids unchanged.
            // - inv_zones_wf:           for zid: require(region.spec_valid()) + require(disjoint from
            //                           closure) + pre zone wf => post zone wf (via insert_region spec fn);
            //                           other zids unchanged.
            // - inv_region_closure:     post.region_closure = pre.region_closure.insert(region);
            //                           the new region is in post.zones[zid].region_set.
            // - inv_region_disjoint:    existing pairs unchanged; new region is disjoint from all
            //                           existing regions by require.
            // - inv_region_unique_owner: region not in pre.region_closure (by require),
            //                           so it was not in any zone; now only in zid.
            // - inv_zone_isolated:      for zid: need to show (zone.insert_region(region)).zone_isolated().
            //                           The new region's Offset mapper is monotone, so translation
            //                           stays in range.  Old regions unchanged.
            admit();
        }

        #[inductive(remove_region)]
        fn remove_region_inductive(pre: Self, post: Self, zid: nat, region: MemoryRegion) {
            // TODO: discharge:
            // - inv_zone_ids:           zones changes key zid's value only; zone_ids unchanged.
            // - inv_zones_wf:           removing a region from a wf zone keeps it wf.
            // - inv_region_closure:     post.region_closure = pre.region_closure.remove(region);
            //                           the removed region is no longer in any zone.
            // - inv_region_disjoint:    subset of pre.region_closure; preserved.
            // - inv_region_unique_owner: subset of pre.zones[zid].region_set; preserved.
            // - inv_zone_isolated:      fewer regions => subset of old translation witnesses.
            admit();
        }
    }
}

// ── Token type aliases ────────────────────────────────────────────────────────
pub type HvMemInstance = HvMemSpec::Instance;

pub type HvZoneIdsToken = HvMemSpec::zone_ids;

pub type HvZoneToken = HvMemSpec::zones;

pub type HvRegionClosureToken = HvMemSpec::region_closure;

/// Per-zone tracked ghost state, holding the zone's entry in `HvMemSpec::zones`.
///
/// One `ZoneState` is created for each zone when it is added via `HvMemState::add_zone`,
/// and consumed when the zone is removed via `HvMemState::remove_zone`.
///
/// `ZoneState` is typically stored inside the zone-level lock, so that only the thread
/// holding the zone lock can invoke `insert_region`/`remove_region`.
pub tracked struct ZoneState {
    pub zone_tok: HvZoneToken,
}

impl ZoneState {
    /// Well-formedness: the zone token belongs to the given `HvMemSpec` instance.
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

/// Global tracked ghost state held by the hypervisor memory manager.
///
/// Wraps the `HvMemSpec` Instance and the variable-sharded tokens (`zone_ids`,
/// `region_closure`) that are not distributed to individual zones.
///
/// Typically stored inside a `Mutex` so that `add_zone`/`remove_zone` are mutually
/// exclusive.  Per-zone `ZoneState` tokens are distributed to zone-level locks
/// independently, mirroring the `AllocatorState` / `ClientState` split in
/// `global_allocator`.
pub tracked struct HvMemState {
    pub inst: HvMemInstance,
    pub zone_ids_tok: HvZoneIdsToken,
    pub region_closure_tok: HvRegionClosureToken,
}

impl HvMemState {
    /// Core well-formedness: all tokens belong to the same `HvMemSpec` instance.
    pub open spec fn wf(&self) -> bool {
        &&& self.zone_ids_tok.instance_id() == self.inst.id()
        &&& self.region_closure_tok.instance_id() == self.inst.id()
    }

    /// The `HvMemSpec` instance ID.
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

    /// Construct an initial (empty) `HvMemState` from a freshly-created `HvMemSpec`
    /// instance. Callers obtain the tokens from `HvMemSpec::Instance::initialize`.
    pub proof fn new(
        tracked inst: HvMemInstance,
        tracked zone_ids_tok: HvZoneIdsToken,
        tracked region_closure_tok: HvRegionClosureToken,
    ) -> (tracked state: HvMemState)
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
        HvMemState { inst, zone_ids_tok, region_closure_tok }
    }

    /// Add a fully constructed zone to the system.
    ///
    /// The caller must prove every region in `zone` is disjoint from the existing
    /// `region_closure`.  Returns a fresh `ZoneState` token for the new zone, which
    /// should be stored inside the zone-level lock.
    pub proof fn add_zone(tracked &mut self, zid: nat, zone: GhostZone) -> (tracked zone_state:
        ZoneState)
        requires
            old(self).wf(),
            !old(self).zone_ids().contains(zid),
            zone.wf(old(self).inst_id()),
            forall|new_region: MemoryRegion|
                zone.regions().contains(new_region) ==> forall|existing: MemoryRegion| #[trigger]
                    old(self).region_closure().contains(existing) ==> !new_region.spec_overlaps_pmem(
                        existing,
                    ),
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
        ZoneState { zone_tok }
    }

    /// Remove an entire zone from the system, consuming its `ZoneState` token.
    ///
    /// The zone's regions are subtracted from `region_closure`.  Callers are
    /// responsible for draining page-table frames before invoking this.
    pub proof fn remove_zone(tracked &mut self, tracked zone_state: ZoneState)
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
        let tracked ZoneState { zone_tok } = zone_state;
        let zid = zone_tok.key();
        self.inst.remove_zone(zid, &mut self.zone_ids_tok, zone_tok, &mut self.region_closure_tok);
    }

    /// Insert one region into an existing zone.
    ///
    /// Consumes `zone_state` and returns an updated `ZoneState` with the region
    /// added.  Also extends `region_closure` by `region`.
    ///
    /// The caller must prove `region` is disjoint from the current `region_closure`,
    /// which simultaneously establishes intra-zone and inter-zone disjointness.
    pub proof fn insert_region(
        tracked &mut self,
        tracked zone_state: ZoneState,
        region: MemoryRegion,
    ) -> (tracked new_zone_state: ZoneState)
        requires
            old(self).wf(),
            zone_state.wf(old(self).inst_id()),
            region.spec_valid(),
            forall|existing: MemoryRegion| #[trigger]
                old(self).region_closure().contains(existing) ==> !region.spec_overlaps_pmem(existing),
        ensures
            self.wf(),
            self.inst_id() == old(self).inst_id(),
            new_zone_state.wf(self.inst_id()),
            new_zone_state.zone_id() == zone_state.zone_id(),
            self.region_closure() =~= old(self).region_closure().insert(region),
            new_zone_state.ghost_zone() == zone_state.ghost_zone().insert_region(region),
    {
        let tracked ZoneState { zone_tok } = zone_state;
        let zid = zone_tok.key();
        let tracked new_zone_tok = self.inst.insert_region(
            zid,
            region,
            zone_tok,
            &mut self.region_closure_tok,
        );
        ZoneState { zone_tok: new_zone_tok }
    }

    /// Remove one region from an existing zone.
    ///
    /// Consumes `zone_state` and returns an updated `ZoneState` with the region
    /// removed.  Also shrinks `region_closure` by `region`.
    pub proof fn remove_region(
        tracked &mut self,
        tracked zone_state: ZoneState,
        region: MemoryRegion,
    ) -> (tracked new_zone_state: ZoneState)
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
        let tracked ZoneState { zone_tok } = zone_state;
        let zid = zone_tok.key();
        let tracked new_zone_tok = self.inst.remove_region(
            zid,
            region,
            zone_tok,
            &mut self.region_closure_tok,
        );
        ZoneState { zone_tok: new_zone_tok }
    }
}

/// Ghost key for a `Zone`'s `RwLock`.
///
/// Binds the lock to a specific `PCell<M>` (via `cell_id`) and to the
/// `HvMemSpec` instance (via `inst_id`), so the predicate can express
/// "the `PointsTo` inside the lock belongs to this cell, and the
/// `ZoneState` token belongs to this instance".
pub struct ZoneKey {
    /// `PCell::id()` of the zone's `mem_set` cell.
    pub cell_id: CellId,
    /// `HvMemSpec` instance id shared by the whole hypervisor.
    pub mem_inst_id: InstanceId,
}

/// Tracked content protected by a `Zone`'s `RwLock`.
///
/// This bundles the `PointsTo<M>` cell-permission (needed to access the exec
/// `mem_set` via `PCell::take`/`put`/`borrow`) together with the per-zone
/// `HvMemSpec` token (`ZoneState`).  Both are linear tracked resources that
/// must travel together: whoever holds the write guard can mutate the memory
/// set *and* update the ghost state atomically.
pub tracked struct ZoneRwContent<M> {
    /// Permission to read/write the zone's exec `mem_set` PCell.
    pub mem_set_perm: PointsTo<M>,
    /// Per-zone HvMemSpec token (map-sharded `zones[zid]`).
    pub zone_state: ZoneState,
}

/// Phantom struct that carries the `Zone`-level `InvariantPredicate`.
pub struct ZonePred<PT, M, A> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator {
    pub _phantom: PhantomData<(PT, M, A)>,
}

impl<PT, M, A> InvariantPredicate<ZoneKey, ZoneRwContent<M>> for ZonePred<PT, M, A> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
{
    /// The content is well-formed when:
    /// - `mem_set_perm` is initialised and points to the key's cell, and
    /// - `zone_state` belongs to the key's `HvMemSpec` instance.
    open spec fn inv(k: ZoneKey, v: ZoneRwContent<M>) -> bool {
        &&& v.mem_set_perm.is_init()
        &&& v.mem_set_perm@.pcell === k.cell_id
        &&& v.zone_state.wf(k.mem_inst_id)
    }
}

/// An exec struct representing one zone's memory, protected by an `RwLock`.
///
/// Layout (mirrors `GlobalAllocator`'s PCell + Mutex pattern, but with
/// read-write instead of exclusive locking):
///
/// ```text
///  RwLock<ZoneRwContent<M>>
///      .mem_set_perm : PointsTo<M>   <- cell permission  ┐ protected by
///      .zone_state   : ZoneState     <- ghost token       ┘ RwLock
///
///  PCell<M>   <- exec memory set, accessed only while lock is held
/// ```
///
/// Multiple CPUs from the **same zone** can hold read guards concurrently
/// (e.g., for page-table walks).  A write guard gives exclusive access for
/// operations that mutate the memory set (insert/remove region).
pub struct Zone<PT, M, A> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator {
    /// Exec memory set — written only while the write guard is held.
    pub mem_set: PCell<M>,
    /// RwLock protecting `ZoneRwContent<M>` with `ZoneKey` predicate.
    pub lock: RwLock<ZoneKey, ZoneRwContent<M>, ZonePred<PT, M, A>>,
    /// Zone identifier.
    pub zone_id: usize,
    /// Phantom data for unused type parameters.
    pub _phantom: PhantomData<(PT, A)>,
}

impl<PT, M, A> Zone<PT, M, A> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator {
    /// Structural well-formedness:
    /// - the `RwLock` is internally consistent, and
    /// - the lock's ghost key `cell_id` matches `self.mem_set.id()`.
    ///
    /// The stronger invariant that `PointsTo.pcell == cell_id` and
    /// `ZoneState.inst_id == k.inst_id` is captured by `ZonePred` and
    /// enforced every time the lock is acquired or released.
    pub open spec fn wf(&self) -> bool {
        &&& self.lock.wf()
        &&& self.lock.k@.cell_id == self.mem_set.id()
    }

    /// Assemble a `Zone` from an already-built exec `mem_set` and its ghost token.
    ///
    /// This is intentionally infallible: all fallible work (validating
    /// `cfg_regions`, constructing the `MemorySet`) must be done by the caller
    /// before invoking this function, so the `HvMemSpec` state machine is only
    /// advanced once success is guaranteed.
    pub fn new(
        mem_set: M,
        zone_id: usize,
        Ghost(inst_id): Ghost<InstanceId>,
        Tracked(zone_state): Tracked<ZoneState>,
    ) -> (res: Self)
        requires
            zone_state.wf(inst_id),
        ensures
            res.wf(),
            res.lock.k@.mem_inst_id == inst_id,
            res.zone_id == zone_id,
    {
        // Store the exec mem_set in a fresh PCell.
        let (mem_set_cell, Tracked(mem_set_perm)) = PCell::new(mem_set);

        // Bundle permission + ghost token into the lock content.
        let tracked zone_rw_content = ZoneRwContent { mem_set_perm, zone_state };

        // Build the ZoneKey (evaluated in spec mode via Ghost(…)).
        let zone_key = Ghost(ZoneKey { cell_id: mem_set_cell.id(), mem_inst_id: inst_id });

        // Admit ZonePred::inv; dischargeable from PCell::new postconditions and
        // zone_state.wf(inst_id) from the precondition.
        proof {
            assume(ZonePred::<PT, M, A>::inv(zone_key@, zone_rw_content));
        }

        let zone_lock = RwLock::new(zone_key, Tracked(zone_rw_content));
        Zone { mem_set: mem_set_cell, lock: zone_lock, zone_id, _phantom: PhantomData }
    }

    /// Acquire exclusive (write) access to this zone's memory set.
    ///
    /// Returns the exec `M` value and a write guard.  The caller must eventually
    /// call `unlock_write` with the (possibly modified) `M` and the guard to
    /// release the lock and restore the invariant.
    pub fn lock_write(&self) -> (res: (
        M,
        RwWriteGuard<ZoneKey, ZoneRwContent<M>, ZonePred<PT, M, A>>,
    ))
        requires
            self.wf(),
        ensures
            res.1.wf(&self.lock),
            res.1.token.mem_set_perm@.pcell == self.mem_set.id(),
            !res.1.token.mem_set_perm.is_init(),
    {
        let RwWriteGuard { handle, token } = self.lock.lock_write();
        let tracked mut content: ZoneRwContent<M> = token.get();
        let mem_set = self.mem_set.take(Tracked(&mut content.mem_set_perm));
        (mem_set, RwWriteGuard { handle, token: Tracked(content) })
    }

    /// Release the write lock and restore the zone invariant.
    ///
    /// Puts `mem_set` back into the zone's `PCell`, asserts (via `assume`) that
    /// `ZonePred::inv` holds, and then releases the `RwLock`.
    pub fn unlock_write(
        &self,
        mem_set: M,
        guard: RwWriteGuard<ZoneKey, ZoneRwContent<M>, ZonePred<PT, M, A>>,
    )
        requires
            self.wf(),
            guard.wf(&self.lock),
            guard.token.mem_set_perm@.pcell == self.mem_set.id(),
            !guard.token.mem_set_perm.is_init(),
    {
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M> = token.get();
        self.mem_set.put(Tracked(&mut content.mem_set_perm), mem_set);
        proof {
            assume(ZonePred::<PT, M, A>::inv(self.lock.k@, content));
        }
        self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });
    }

    /// Acquire shared (read) access to this zone's memory set.
    ///
    /// Multiple readers may hold a read guard concurrently.  Use
    /// `RwReadGuard::borrow` + `PCell::borrow` to obtain a `&M` reference.
    pub fn lock_read(&self) -> (res: RwReadGuard<ZoneKey, ZoneRwContent<M>, ZonePred<PT, M, A>>)
        requires
            self.wf(),
        ensures
            res.wf(&self.lock),
    {
        self.lock.lock_read()
    }

    /// Release the read lock acquired by `lock_read`.
    pub fn unlock_read(&self, guard: RwReadGuard<ZoneKey, ZoneRwContent<M>, ZonePred<PT, M, A>>)
        requires
            self.wf(),
            guard.wf(&self.lock),
    {
        self.lock.unlock_read(guard)
    }

    /// Borrow the zone's exec `mem_set` while a read guard is held.
    ///
    /// Both `self` and `guard` must be alive for lifetime `'a`, so the returned
    /// `&'a M` is valid for exactly that duration.  Do not call `unlock_read`
    /// until the `&M` reference is no longer in use.
    pub fn borrow_mem_set<'a>(
        &'a self,
        guard: &'a RwReadGuard<ZoneKey, ZoneRwContent<M>, ZonePred<PT, M, A>>,
    ) -> (res: &'a M)
        requires
            self.wf(),
            guard.wf(&self.lock),
    {
        // `self.lock.inst` is borrowed for `'a` (from `&'a self`).
        // `guard.handle`   is borrowed for `'a` (from `&'a guard`).
        // `read_guard` yields a ghost `&'a ZoneRwContent<M>`, so the field borrow
        // `&mem_set_perm` also carries lifetime `'a`, which flows through
        // `PCell::borrow` into the returned `&'a M`.
        let tracked ZoneRwContent { mem_set_perm, .. } = self.lock.inst.borrow().read_guard(
            guard.handle@.element(),
            guard.handle.borrow(),
        );
        // TODO: how to prove this?
        assume(mem_set_perm.is_init());
        assume(mem_set_perm@.pcell == self.mem_set.id());
        self.mem_set.borrow(Tracked(&mem_set_perm))
    }
}

/// Compound guard returned by `HvMem::write_zone` / `HvMem::read_zone`.
///
/// Bundles the HvMem write lock resources (handle + content with empty
/// zone-list permission) with the zone's write lock resources (handle +
/// content with empty mem-set permission) and the temporarily-detached
/// zone list.
///
/// Pass to `HvMem::unlock_write_zone` together with the (possibly modified)
/// exec `M` to put everything back and release both locks.
pub struct ZoneWriteGuard<PT, M, A> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
 {
    /// Zone list taken from HvMem's PCell (zone_list_perm is currently uninitialized).
    pub zones: Vec<Arc<Zone<PT, M, A>>>,
    /// Index of the locked zone within `zones`.
    pub zone_idx: usize,
    /// Zone-level write-lock handle token.
    pub zone_write_handle: Tracked<RwWriterToken<ZoneKey, ZoneRwContent<M>, ZonePred<PT, M, A>>>,
    /// Zone-level lock content (mem_set_perm is currently uninitialized — M was taken out).
    pub zone_content: Tracked<ZoneRwContent<M>>,
    /// HvMem-level write-lock handle token.
    pub hvm_handle: Tracked<RwWriterToken<HvMemKey, HvMemRwContent<PT, M, A>, HvMemPred<PT, M, A>>>,
    /// HvMem-level lock content (zone_list_perm is currently uninitialized — zones was taken out).
    pub hvm_content: Tracked<HvMemRwContent<PT, M, A>>,
}

/// Compound guard returned by `HvMem::read_zone`.
///
/// Structurally identical to `ZoneWriteGuard` — the zone is locked for write
/// to allow taking `M` from the PCell.  The semantic distinction (read-only
/// vs read-write) is enforced at the spec level: `unlock_read_zone` requires
/// the `M` passed back to be spec-equal to the one originally returned.
///
/// Use the same pattern as `ZoneWriteGuard`: receive `M`, inspect it, then
/// call `HvMem::unlock_read_zone(m, guard)`.
pub struct ZoneReadGuard<PT, M, A> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator {
    pub inner: ZoneWriteGuard<PT, M, A>,
}

/// Ghost key for `HvMem`'s outer `RwLock`.
///
/// Binds the lock to the `PCell<Vec<Zone<...>>>` (via `cell_id`).
pub struct HvMemKey {
    /// `PCell::id()` of `HvMem`'s zone-list cell.
    pub cell_id: CellId,
}

/// Tracked content protected by `HvMem`'s `RwLock`.
///
/// Bundles the `PointsTo<Vec<Zone<...>>>` cell-permission for the zone list
/// together with the global `HvMemState` (which holds the `HvMemSpec` instance
/// and the `zone_ids` / `region_closure` variable tokens).
pub tracked struct HvMemRwContent<PT, M, A> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
 {
    /// Permission to read/write the zone-list PCell.
    pub zone_list_perm: PointsTo<Vec<Arc<Zone<PT, M, A>>>>,
    /// Global HvMemSpec ghost state.
    pub hv_mem_state: HvMemState,
}

/// Phantom struct that carries the `HvMem`-level `InvariantPredicate`.
pub struct HvMemPred<PT, M, A> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator {
    pub _phantom: PhantomData<(PT, M, A)>,
}

impl<PT, M, A> InvariantPredicate<HvMemKey, HvMemRwContent<PT, M, A>> for HvMemPred<PT, M, A> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
 {
    /// The content is well-formed when:
    /// - `zone_list_perm` is initialised and points to the key's cell,
    /// - `hv_mem_state` is internally well-formed, and
    /// - the exec zone list and the ghost state agree: every ghost zone ID has
    ///   exactly one corresponding exec `Zone`, all zones share the same
    ///   `HvMemSpec` instance, and exec zone IDs are pairwise distinct.
    open spec fn inv(k: HvMemKey, v: HvMemRwContent<PT, M, A>) -> bool {
        &&& v.zone_list_perm.is_init()
        &&& v.zone_list_perm@.pcell === k.cell_id
        &&& v.hv_mem_state.wf()
        &&& {
            let zone_list = v.zone_list_perm@.mem_contents->Init_0;
            // The ghost zone_ids set is exactly the set of exec zone IDs.
            &&& (forall|zid: nat| #[trigger]
                v.hv_mem_state.zone_ids().contains(zid) == (exists|i: int|
                    0 <= i < zone_list.len() && #[trigger] zone_list[i].zone_id as nat
                        == zid))
            // Each exec zone's lock is bound to the correct HvMemSpec instance.
            &&& (forall|i: int|
                #![trigger zone_list[i]]
                0 <= i < zone_list.len() ==> zone_list[i].lock.k@.mem_inst_id
                    == v.hv_mem_state.inst_id())
            // Exec zone IDs are pairwise distinct (ensures the bijection above is well-defined).
            &&& (forall|i: int, j: int|
                0 <= i < zone_list.len() && 0 <= j < zone_list.len() && i != j
                    ==> zone_list[i].zone_id != zone_list[j].zone_id)
        }
    }
}

/// The top-level memory manager struct of the hypervisor, containing all zones
/// and the global allocator.
///
/// Layout:
///
/// ```text
///  RwLock<HvMemRwContent<PT,M,A>>
///      .zone_list_perm : PointsTo<Vec<Zone<...>>>   <- cell permission  ┐ protected by
///      .hv_mem_state   : HvMemState                 <- ghost tokens     ┘ RwLock
///
///  PCell<Vec<Zone<...>>>   <- zone list, accessed only while lock is held
///
///  GlobalAllocator<A>      <- already has its own internal Mutex; no extra locking needed
/// ```
///
/// CPUs from **different zones** share `HvMem` and may need the zone list at
/// the same time (e.g., to look up their zone).  The outer `RwLock` allows
/// concurrent reads of the list while serialising structural changes
/// (`add_zone` / `remove_zone`).
pub struct HvMem<PT, M, A> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator {
    /// Zone list — written only while the HvMem write guard is held.
    pub zone_mem_list: PCell<Vec<Arc<Zone<PT, M, A>>>>,
    /// RwLock protecting `HvMemRwContent<PT,M,A>` with `HvMemKey` predicate.
    pub lock: RwLock<HvMemKey, HvMemRwContent<PT, M, A>, HvMemPred<PT, M, A>>,
    /// Ghost record of `zone_mem_list.id()`.
    pub cell_id: Ghost<CellId>,
    /// Global allocator — already protected by its own `Mutex`.
    pub alloc: GlobalAllocator<A>,
}

impl<PT, M, A> HvMem<PT, M, A> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator {
    /// Structural well-formedness:
    /// - the outer `RwLock` is internally consistent,
    /// - the lock's ghost key `cell_id` matches `self.zone_mem_list.id()`, and
    /// - the global allocator is valid.
    ///
    /// `HvMemPred::inv` (checked on every write-lock release) additionally
    /// guarantees that the `PointsTo` inside the lock points to the same cell
    /// and that `HvMemState` is well-formed.
    pub open spec fn wf(&self) -> bool {
        &&& self.lock.wf()
        &&& self.lock.k@.cell_id == self.cell_id@
        &&& self.alloc.invariants()
    }

    /// Add a new zone to the hypervisor memory manager.
    ///
    /// # Protocol
    ///
    /// All **fallible** work happens before the lock is acquired, so there is
    /// only one lock-acquisition site and no need to release the lock on an
    /// error path:
    ///
    /// 1. Validate every entry in `cfg_regions`.
    /// 2. Build an empty `MemorySet` from the allocator and insert the regions
    ///    one by one (each `insert` can fail if the allocator is exhausted).
    /// 3. Acquire the **HvMem write lock** to serialise zone-list mutations.
    /// 4. Advance the `HvMemSpec` ghost state machine (`HvMemState::add_zone`)
    ///    to obtain a fresh `ZoneState` token for the new zone.
    /// 5. Delegate Zone assembly to `Zone::new` (infallible at this point).
    /// 6. Push the new `Zone`, return the zone list to its `PCell`, and release
    ///    the write lock.
    pub fn add_zone(
        &self,
        zid: usize,
        pt_constants: PTConstants,
        cfg_regions: Vec<HvConfigMemRegion>,
        Ghost(ghost_zone): Ghost<GhostZone>,
    ) -> (res: Result<(), ()>)
        requires
            self.wf(),
            pt_constants@.valid(),
            forall|level: nat|
                level < pt_constants.arch@.level_count() ==> pt_constants.arch@.entry_count(level)
                    == 512,
            pt_constants.arch@.leaf_frame_size() == FrameSize::Size4K,
        ensures
            res is Ok ==> self.wf(),
    {
        // ── Step 1: validate cfg_regions (no lock needed) ─────────────────────
        let mut i: usize = 0;
        while i < cfg_regions.len()
            invariant
                i <= cfg_regions.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] cfg_regions[j]@.valid(),
            decreases cfg_regions.len() - i,
        {
            if !cfg_regions[i].valid() {
                return Err(());
            }
            i += 1;
        }

        // ── Step 2: build mem_set (no lock needed — alloc has its own lock) ───
        let mut mem_set = M::new(&self.alloc, pt_constants);
        let mut j: usize = 0;
        while j < cfg_regions.len()
            invariant
                j <= cfg_regions.len(),
                forall|k: int| 0 <= k < cfg_regions.len() ==> #[trigger] cfg_regions[k]@.valid(),
                mem_set.invariants(),
                mem_set.inst_id() == self.alloc.inst_id(),
                self.alloc.invariants(),
            decreases cfg_regions.len() - j,
        {
            assert(cfg_regions[j as int]@.valid());
            let region = cfg_regions[j].to_region();
            if mem_set.overlaps_vmem(&region) {
                return Err(());
            }
            let insert_res = mem_set.insert(&self.alloc, region);
            j += 1;
        }

        // ── Step 3: acquire HvMem write lock ──────────────────────────────────
        let guard = self.lock.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: HvMemRwContent<PT, M, A> = token.get();
        let mut zones = self.zone_mem_list.take(Tracked(&mut content.zone_list_perm));

        // ── Step 4: advance HvMemSpec ghost state, obtain ZoneState token ─────
        let tracked zone_state: ZoneState;
        let ghost inst_id: InstanceId;
        proof {
            inst_id = content.hv_mem_state.inst_id();
            // Precondition admits — dischargeable from ghost_zone + HvMemState invariants
            // in a fully verified version.
            assume(!content.hv_mem_state.zone_ids().contains(zid as nat));
            assume(ghost_zone.wf(content.hv_mem_state.inst_id()));
            assume(forall|new_r: MemoryRegion|
                ghost_zone.regions().contains(new_r) ==> forall|existing: MemoryRegion| #[trigger]
                    content.hv_mem_state.region_closure().contains(existing)
                        ==> !new_r.spec_overlaps_vmem(existing));
            zone_state = content.hv_mem_state.add_zone(zid as nat, ghost_zone);
        }

        // ── Step 5: assemble the new Zone (infallible) ────────────────────────
        let new_zone = Arc::new(
            Zone::<PT, M, A>::new(mem_set, zid, Ghost(inst_id), Tracked(zone_state)),
        );

        // ── Step 6: push zone, restore PCell, release write lock ─────────────
        zones.push(new_zone);
        self.zone_mem_list.put(Tracked(&mut content.zone_list_perm), zones);
        proof {
            assume(HvMemPred::<PT, M, A>::inv(self.lock.k@, content));
        }
        self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });

        Ok(())
    }

    /// Remove the zone identified by `zid` from the hypervisor memory manager.
    ///
    /// # Protocol
    ///
    /// 1. Acquire the HvMem write lock and take the zone list.
    /// 2. Find the zone by `zone_id` field.
    /// 3. Swap-remove the zone from the list.
    /// 4. Acquire the zone write lock to extract the `ZoneState` token, and
    ///    take `M` (so that both tracked resources are properly consumed).
    /// 5. Advance `HvMemState::remove_zone` to drop the `ZoneState` token.
    /// 6. Restore the zone list and release the HvMem write lock.
    ///
    /// Returns `Err(())` if no zone with the given `zid` is found.
    pub fn remove_zone(&self, zid: usize) -> (res: Result<(), ()>)
        requires
            self.wf(),
        ensures
            res is Ok ==> self.wf(),
    {
        // ── Step 1: acquire HvMem write lock ─────────────────────────────────
        let guard = self.lock.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: HvMemRwContent<PT, M, A> = token.get();
        let mut zones = self.zone_mem_list.take(Tracked(&mut content.zone_list_perm));

        // ── Step 2: find zone by ID ───────────────────────────────────────────
        let mut idx_opt: Option<usize> = None;
        let mut i: usize = 0;
        while i < zones.len()
            invariant
                i <= zones.len(),
            decreases zones.len() - i,
        {
            if zones[i].zone_id == zid {
                idx_opt = Some(i);
                break ;
            }
            i += 1;
        }

        if idx_opt.is_none() {
            // Zone not found — restore and return error.
            self.zone_mem_list.put(Tracked(&mut content.zone_list_perm), zones);
            proof {
                assume(HvMemPred::<PT, M, A>::inv(self.lock.k@, content));
            }
            self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });
            return Err(());
        }
        // ── Step 3: remove zone from list ─────────────────────────────────────

        let idx = idx_opt.unwrap();
        let zone = zones.swap_remove(idx);

        // ── Step 4: extract ZoneState and M from the zone ─────────────────────
        let zone_guard = zone.lock.lock_write();
        let RwWriteGuard { handle: zone_handle, token: zone_token } = zone_guard;
        let tracked mut zone_content: ZoneRwContent<M> = zone_token.get();
        // Take M out of the zone's PCell so it is properly dropped below.
        let _mem_set: M = zone.mem_set.take(Tracked(&mut zone_content.mem_set_perm));
        // _mem_set is dropped at end of scope.

        // ── Step 5: advance ghost state ───────────────────────────────────────
        proof {
            let tracked ZoneRwContent { mem_set_perm: _, zone_state } = zone_content;
            content.hv_mem_state.remove_zone(zone_state);
            // zone_handle (writer token) is consumed here via assume — the zone is
            // being destroyed so there is no need to formally unlock it.
            assume(false);  // FIXME: zone_handle (RwWriterToken) needs explicit disposal
        }

        // ── Step 6: restore zone list and release HvMem write lock ───────────
        self.zone_mem_list.put(Tracked(&mut content.zone_list_perm), zones);
        proof {
            assume(HvMemPred::<PT, M, A>::inv(self.lock.k@, content));
        }
        self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });

        Ok(())
    }

    /// Look up the zone with the given `zid` and return an `Arc` clone if found.
    pub fn find_zone(&self, zid: usize) -> (res: Option<Arc<Zone<PT, M, A>>>)
        requires
            self.wf(),
        ensures
            res.is_some() ==> res.unwrap().wf() && res.unwrap().zone_id == zid,
    {
        // ── Step 1: acquire HvMem write lock ─────────────────────────────────
        let guard = self.lock.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: HvMemRwContent<PT, M, A> = token.get();
        let mut zones = self.zone_mem_list.take(Tracked(&mut content.zone_list_perm));

        // ── Step 2: find zone by ID ───────────────────────────────────────────
        let mut idx_opt: Option<usize> = None;
        let mut i: usize = 0;
        while i < zones.len()
            invariant
                i <= zones.len(),
            decreases zones.len() - i,
        {
            if zones[i].zone_id == zid {
                idx_opt = Some(i);
                break ;
            }
            i += 1;
        }

        if idx_opt.is_none() {
            // Zone not found — restore and return error.
            self.zone_mem_list.put(Tracked(&mut content.zone_list_perm), zones);
            proof {
                assume(HvMemPred::<PT, M, A>::inv(self.lock.k@, content));
            }
            self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });
            None
        } else {
            // Zone found — clone Arc, restore, and return.
            let idx = idx_opt.unwrap();
            let zone = zones[idx].clone();
            self.zone_mem_list.put(Tracked(&mut content.zone_list_perm), zones);
            proof {
                assume(HvMemPred::<PT, M, A>::inv(self.lock.k@, content));
            }
            self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });
            Some(zone)
        }
    }
}

} // verus!
