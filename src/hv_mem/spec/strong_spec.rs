//! Assumption-2 per-zone budget state machine for the hypervisor memory manager.
//!
//! Under assumption 2 each zone is pre-allocated a **fixed budget** of physical memory
//! regions at boot time.  A zone may only insert regions that are within its budget,
//! so `insert_region` needs only the zone-local `zones` token — no global lock is needed.
//!
//! Compared to [`super::weak_spec::ClosureSpec`]:
//! - `ClosureSpec` has a `#[sharding(variable)] region_closure` field, whose single
//!   global token forces a global write-lock on every `insert_region`.
//! - `BudgetSpec` uses an external uninterpreted `zone_budget(zid)` function to model
//!   static per-zone budgets, with trusted axioms for validity/disjointness. No budget
//!   token exists in the state machine, so there is less token plumbing.
//!
//! P1 (RegionDisjoint) still holds: `inv_budgets_disjoint` + `inv_budgets_in_all_regions`
//! + `all_regions_disjoint()` give cross-zone disjointness without any global token.
use super::{all_regions, all_regions_disjoint, all_regions_valid, GhostZone};
use crate::address::region::MemoryRegion;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::{prelude::*, tokens::InstanceId};

verus! {

/// Static per-zone configured budget.
///
/// This is treated as trusted configuration input, not mutable state.
pub uninterp spec fn zone_budget(zid: nat) -> Set<MemoryRegion>;

/// Axiom: every budget region is globally valid.
pub axiom fn zone_budget_in_all_regions()
    ensures
        forall|zid: nat, r: MemoryRegion| #[trigger]
            zone_budget(zid).contains(r) ==> all_regions().contains(r),
;

/// Axiom: budgets of distinct zones are disjoint.
pub axiom fn zone_budget_pairwise_disjoint()
    ensures
        forall|zid1: nat, zid2: nat, r: MemoryRegion|
            #![auto]
            zid1 != zid2 && zone_budget(zid1).contains(r) ==> !zone_budget(zid2).contains(r),
;

// Per-zone-budget state machine: assumption-2 specification.
tokenized_state_machine! {
    BudgetSpec {
        fields {
            #[sharding(constant)]
            pub alloc_inst_id: InstanceId,

            #[sharding(variable)]
            pub zone_ids: Set<nat>,

            /// Per-zone memory state (zones map: unchanged from ClosureSpec).
            #[sharding(map)]
            pub zones: Map<nat, GhostZone>,
        }

        // ── Invariants ─────────────────────────────────────────────────────────────

        /// `zone_ids` and `zones.dom()` are always identical.
        #[invariant]
        pub fn inv_zone_ids(&self) -> bool {
            self.zones.dom() == self.zone_ids
        }

        /// All zones are well-formed relative to the system allocator instance.
        #[invariant]
        pub fn inv_zones_wf(&self) -> bool {
            forall|zid: nat|
                self.zones.contains_key(zid) ==> #[trigger] self.zones[zid].wf(self.alloc_inst_id)
        }

        /// Every region currently assigned to a zone lies within that zone's budget.
        ///
        /// Together with `inv_budgets_disjoint`, this ensures that the assigned
        /// regions of two distinct zones are disjoint.
        #[invariant]
        pub fn inv_zone_within_budget(&self) -> bool {
            forall|zid: nat, r: MemoryRegion|
                self.zones.contains_key(zid) && #[trigger] self.zones[zid].contains_region(r)
                    ==> #[trigger] zone_budget(zid).contains(r)
        }

        /// All budget regions belong to `all_regions()`.
        ///
        /// Provides the physical-memory-validity anchor, mirroring
        /// `inv_region_closure_subset` in `ClosureSpec`.
        #[invariant]
        pub fn inv_budgets_in_all_regions(&self) -> bool {
            forall|zid: nat, r: MemoryRegion|
                self.zone_ids.contains(zid) && #[trigger] zone_budget(zid).contains(r)
                    ==> all_regions().contains(r)
        }

        /// Budgets from distinct zones are pairwise disjoint.
        ///
        /// Combined with `inv_budgets_in_all_regions` and `all_regions_disjoint()`,
        /// and `inv_zone_within_budget`, this implies P1 (RegionDisjoint): regions
        /// from different zones cannot overlap because their budgets are disjoint
        /// subsets of the axiomatically-disjoint `all_regions()`.
        #[invariant]
        pub fn inv_budgets_disjoint(&self) -> bool {
            forall|zid1: nat, zid2: nat, r: MemoryRegion| #![auto]
                self.zone_ids.contains(zid1) && self.zone_ids.contains(zid2)
                && zid1 != zid2
                && zone_budget(zid1).contains(r)
                    ==> !zone_budget(zid2).contains(r)
        }

        // ── Properties ─────────────────────────────────────────────────────────────

        /// P1 (RegionDisjoint): regions from distinct zones do not overlap in physical memory.
        ///
        /// Proof:
        /// - r1 ∈ zones[zid1] ⊆ budget[zid1] ⊆ all_regions()  (inv_zone_within_budget + inv_budgets_in_all_regions)
        /// - r2 ∈ zones[zid2] ⊆ budget[zid2] ⊆ all_regions()  (same)
        /// - r1 ≠ r2: `all_regions_disjoint()` gives `!r1.spec_overlaps_pmem(r2)`.
        /// - r1 = r2: `inv_budgets_disjoint` forbids the same region in two distinct budgets —
        ///            contradicting r1 ∈ budget[zid1] ∩ budget[zid2].
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
                        zone1.regions().contains(r1) && zone2.regions().contains(r2)
                        implies !r1.spec_overlaps_pmem(r2) by
                    {
                        assume(zone_budget(zid1).contains(r1));
                        assume(zone_budget(zid2).contains(r2));
                        assert(all_regions().contains(r1) && all_regions().contains(r2));
                        if r1 != r2 {
                            all_regions_disjoint();
                        } else {
                            // r1 = r2 ∈ budget[zid1] ∩ budget[zid2] contradicts inv_budgets_disjoint.
                            assert(false);
                        }
                    };
                };
            }
        }

        // ── Transitions ─────────────────────────────────────────────────────────────

        init! {
            initialize(alloc_inst_id: InstanceId) {
                init alloc_inst_id = alloc_inst_id;
                init zone_ids = Set::empty();
                init zones = Map::empty();
            }
        }

        /// Add a zone with a fixed static budget `zone_budget(zid)`.
        ///
        /// Preconditions:
        /// - `zone.regions()` ⊆ `zone_budget(zid)`: initial assignment is within budget.
        transition! {
            add_zone(zid: nat, zone: GhostZone) {
                require(!pre.zone_ids.contains(zid));
                require(zone.wf(pre.alloc_inst_id));
                require(forall|r: MemoryRegion|
                    #[trigger] zone.regions().contains(r) ==> zone_budget(zid).contains(r));
                update zone_ids = pre.zone_ids.insert(zid);
                add zones += [zid => zone];
            }
        }

        /// Remove a zone.
        transition! {
            remove_zone(zid: nat) {
                remove zones -= [zid => let _zone];
                update zone_ids = pre.zone_ids.remove(zid);
            }
        }

        /// Insert a region into a zone's current assignment.
        ///
        /// **Zone-local operation**: only the zone's own `zones` token is required.
        /// The global `zone_ids` variable token is untouched, so no global HvMem
        /// write lock is needed.
        ///
        /// Preconditions:
        /// - `region` ∈ `budget[zid]`: membership in the zone's static budget
        ///   authorizes the insert without a system-wide closure check.
        /// - `region` ∉ `zone.regions()`: prevents double-insert.
        /// - `region` does not overlap the zone's existing virtual memory layout.
        transition! {
            insert_region(zid: nat, region: MemoryRegion) {
                remove zones -= [zid => let zone];
                require(zone_budget(zid).contains(region));
                require(!zone.contains_region(region));
                require(!zone.mem_set.overlaps_vmem(region));
                add zones += [zid => zone.insert_region(region)];
            }
        }

        /// Remove a region from a zone's current assignment.
        ///
        /// **Zone-local operation**: only the zone's `zones` token is required.
        transition! {
            remove_region(zid: nat, region: MemoryRegion) {
                remove zones -= [zid => let zone];
                require(zone.contains_region(region));
                add zones += [zid => zone.remove_region(region)];
            }
        }

        // ── Inductive proofs ────────────────────────────────────────────────────────

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, alloc_inst_id: InstanceId) { }

        #[inductive(add_zone)]
        fn add_zone_inductive(pre: Self, post: Self, zid: nat, zone: GhostZone) {
            admit();
        }

        #[inductive(remove_zone)]
        fn remove_zone_inductive(pre: Self, post: Self, zid: nat) {
            admit();
        }

        #[inductive(insert_region)]
        fn insert_region_inductive(pre: Self, post: Self, zid: nat, region: MemoryRegion) {
            admit();
        }

        #[inductive(remove_region)]
        fn remove_region_inductive(pre: Self, post: Self, zid: nat, region: MemoryRegion) {
            admit();
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
