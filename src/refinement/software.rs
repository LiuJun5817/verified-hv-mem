//! The refinement: `impl SoftwareRefinement for BudgetSpec::State`.
//!
//! Where the contract is met.  `invariants()` is the machine's real
//! `invariant()`, so `inv_implies_wf` proves every reachable state projects to a
//! `wf` (hence secure) `SoftwareView`.
//!
//! Each transition method fires the matching `BudgetSpec` macro transition via
//! `BudgetSpec::take_step::*` (which supplies `post.invariant()`) and then proves
//! the corresponding `SoftwareView` step.  `insert_region` / `remove_region` take a
//! machine-level [`Region`] argument: the trusted bridge
//! [`super::view::axiom_assignable_from_budget`] recovers the budget
//! `MemoryRegion` it abstracts, the projection-equality lemmas in [`super::view`]
//! identify their pages/entries, and the projection-delta lemmas below assemble
//! the step.  The transition guards (`!contains_region` / `!overlaps_vmem` for
//! insert, `contains_region` / pmem-exclusivity for remove) are *derived* from the
//! closed `SoftwareView::*_enabled` preconditions.
//!
//! Builds on [`super::view`]; the projection-delta lemmas follow the impl.
use super::view::*;
use crate::address::addr::SpecVAddr;
use crate::address::frame::SpecFrame;
use crate::address::region::MemoryRegion;
use crate::machine::convert::{frame_phys_page, vaddr_of_gpa};
use crate::hv_mem::spec::budget::{zone_budget, zone_budget_in_all_regions, BudgetSpec};
use crate::hv_mem::spec::{all_regions, all_regions_disjoint, all_regions_valid, GhostZone};
use crate::machine::software::{Region, SoftwareView};
use crate::machine::types::*;
use crate::memory_set::SpecMemorySet;
use vstd::prelude::*;

verus! {

/// Specification trait for hypervisor software state management — the refinement
/// contract whose methods fire the matching [`SoftwareView`] transitions.
///
/// A **ghost contract**: a concrete `T: View<V = SoftwareView>` represents the
/// hypervisor's abstract memory state, and each transition is a `proof fn` taking
/// `self` by value whose effect on the view is the matching `SoftwareView` step.
/// The implementing type is `BudgetSpec::State` itself (impl below), so
/// `invariants()` is the state machine's real, inductively-proven `invariant()`.
/// Each precondition is the closed `SoftwareView::*_enabled` predicate, owned by the
/// trusted model.
pub trait SoftwareRefinement: View<V = SoftwareView> + Sized {
    /// Internal consistency predicate, established at construction and preserved.
    spec fn invariants(&self) -> bool;

    /// Invariants imply the abstract state is well-formed.
    broadcast proof fn inv_implies_wf(&self)
        requires
            #[trigger] self.invariants(),
        ensures
            self@.wf(),
    ;

    /// Register a fresh, empty VM.
    proof fn add_vm(self, vm: VmId) -> (post: Self)
        requires
            self.invariants(),
            SoftwareView::add_vm_enabled(self@, vm),
        ensures
            post.invariants(),
            SoftwareView::add_vm_step(self@, post@, vm),
    ;

    /// Deregister a VM that owns no pages, has no mappings, and shares nothing.
    proof fn remove_vm(self, vm: VmId) -> (post: Self)
        requires
            self.invariants(),
            SoftwareView::remove_vm_enabled(self@, vm),
        ensures
            post.invariants(),
            SoftwareView::remove_vm_step(self@, post@, vm),
    ;

    /// Assign `region`'s pages to its VM and install its stage-2 entries.
    proof fn insert_region(self, region: Region) -> (post: Self)
        requires
            self.invariants(),
            SoftwareView::insert_region_enabled(self@, region),
        ensures
            post.invariants(),
            SoftwareView::insert_region_step(self@, post@, region),
    ;

    /// Unmap `region`'s entries and reclaim its pages back to the hypervisor pool.
    proof fn remove_region(self, region: Region) -> (post: Self)
        requires
            self.invariants(),
            SoftwareView::remove_region_enabled(self@, region),
        ensures
            post.invariants(),
            SoftwareView::remove_region_step(self@, post@, region),
    ;
}

impl SoftwareRefinement for BudgetSpec::State {
    /// The contract invariant is the state machine's real invariant.
    open spec fn invariants(&self) -> bool {
        self.invariant()
    }

    broadcast proof fn inv_implies_wf(&self)
        ensures
            #[trigger] self@.wf(),
    {
        let sw = self.view();
        // sharing_wf: vacuous (shared_pages ≡ ∅).
        assert(sw.shared_pages =~= Set::<SharedPage>::empty());
        assert(sw.sharing_wf());

        // ownership_wf: dom; cross-zone disjointness; vm-vs-hypervisor disjointness.
        assert(sw.vm_owned.dom() =~= sw.all_vms);
        lemma_state_owned_pages_disjoint(*self);
        assert forall|vm: VmId, page: PhysPage|
            sw.all_vms.contains(vm) && #[trigger] sw.vm_owned[vm].contains(
                page,
            ) implies !sw.hypervisor_owned.contains(page) by {
            // vm.0 ∈ zones.dom (inv_zone_ids) and page ∈ zone_owned ⇒ all_owned ⇒ not in pool.
            assert(self.zones.contains_key(vm.0));
            lemma_zone_owned_in_all_owned(self.zones, vm.0, page);
        }
        assert(sw.ownership_wf());

        // translation_wf.
        assert forall|key: VmPageKey| #[trigger] sw.s2_map.contains_key(key) implies (
        sw.all_vms.contains(key.vm) && sw.owned_or_shared(key.vm, sw.s2_map[key].page)) by {
            lemma_zone_s2_target_owned(key.vm.0, self.zones[key.vm.0]);
        }
        assert(sw.translation_wf());

        assert(sw.wf());
    }

    proof fn add_vm(self, vm: VmId) -> (post: Self) {
        // Fire the `add_zone` macro transition; `post.invariant()` comes from the macro.
        let empty_zone = GhostZone {
            mem_set: SpecMemorySet {
                regions: Set::<MemoryRegion>::empty(),
                mappings: Map::empty(),
            },
        };
        let post = BudgetSpec::take_step::add_zone(self, vm.0);
        assert(post.zones == self.zones.insert(vm.0, empty_zone));
        lemma_zone_owned_pages_empty(empty_zone);
        lemma_zone_s2_entries_empty(vm.0, empty_zone);
        // The new zone owns nothing, so all_owned is unchanged.
        assert(!self.zones.dom().contains(vm.0));
        assert(all_owned_pages(post.zones) =~= all_owned_pages(self.zones)) by {
            assert forall|pp: PhysPage|
                all_owned_pages(post.zones).contains(pp) implies all_owned_pages(
                self.zones,
            ).contains(pp) by {
                let zid = choose|zid: nat|
                    #![auto]
                    post.zones.contains_key(zid) && zone_owned_pages(post.zones[zid]).contains(pp);
                assert(zid != vm.0);
                lemma_zone_owned_in_all_owned(self.zones, zid, pp);
            }
            assert forall|pp: PhysPage|
                all_owned_pages(self.zones).contains(pp) implies all_owned_pages(
                post.zones,
            ).contains(pp) by {
                let zid = choose|zid: nat|
                    #![auto]
                    self.zones.contains_key(zid) && zone_owned_pages(self.zones[zid]).contains(pp);
                assert(zid != vm.0);
                lemma_zone_owned_in_all_owned(post.zones, zid, pp);
            }
        }
        assert(post@.hypervisor_owned =~= self@.hypervisor_owned);
        assert(post@.all_vms =~= self@.all_vms.insert(vm));
        assert(post@.vm_owned =~= self@.vm_owned.insert(vm, Set::empty()));
        assert(post@.s2_map =~= self@.s2_map);
        post
    }

    proof fn remove_vm(self, vm: VmId) -> (post: Self) {
        // Fire the `remove_zone` macro transition; `post.invariant()` comes from the macro.
        let post = BudgetSpec::take_step::remove_zone(self, vm.0);
        assert(post.zone_ids == self.zone_ids.remove(vm.0));
        assert(post.zones == self.zones.remove(vm.0));
        // The removed zone owned nothing (precondition), so all_owned is unchanged.
        assert(zone_owned_pages(self.zones[vm.0]) =~= Set::<PhysPage>::empty());
        assert(all_owned_pages(post.zones) =~= all_owned_pages(self.zones)) by {
            assert forall|pp: PhysPage|
                all_owned_pages(self.zones).contains(pp) implies all_owned_pages(
                post.zones,
            ).contains(pp) by {
                let zid = choose|zid: nat|
                    #![auto]
                    self.zones.contains_key(zid) && zone_owned_pages(self.zones[zid]).contains(pp);
                assert(zid != vm.0);
                lemma_zone_owned_in_all_owned(post.zones, zid, pp);
            }
            assert forall|pp: PhysPage|
                all_owned_pages(post.zones).contains(pp) implies all_owned_pages(
                self.zones,
            ).contains(pp) by {
                let zid = choose|zid: nat|
                    #![auto]
                    post.zones.contains_key(zid) && zone_owned_pages(post.zones[zid]).contains(pp);
                lemma_zone_owned_in_all_owned(self.zones, zid, pp);
            }
        }
        assert(post@.hypervisor_owned =~= self@.hypervisor_owned);
        assert(post@.all_vms =~= self@.all_vms.remove(vm));
        assert(post@.vm_owned =~= self@.vm_owned.remove(vm));
        assert(post@.s2_map =~= self@.s2_map);
        post
    }

    proof fn insert_region(self, region: Region) -> (post: Self) {
        let vm = region.vm;
        let zid = vm.0;
        assert(vm == VmId(zid));
        assert(self.zone_ids.contains(zid));  // view: all_vms ⟺ zone_ids
        assert(self.zones.contains_key(zid));  // invariant: zone_ids ⊆ zones.dom

        // (1) Recover the budget region via the trusted environment bridge.
        axiom_assignable_from_budget(self, region);
        let r = choose|r: MemoryRegion|
            zone_budget(zid).contains(r) && region_to_abstract(zid, r) == region;
        zone_budget_in_all_regions();
        all_regions_valid();
        assert(all_regions().contains(r) && r.spec_valid());

        // (2) Projection equalities: the abstract region projects to `r`'s pages/entries.
        lemma_region_to_abstract_pages(zid, r);
        lemma_region_to_abstract_entries(zid, r);
        assert(region.pages() == region_pages(r));
        assert(region.entries() == region_s2_entries(zid, r));

        // (3) The transition guards, derived from `insert_region_enabled`.
        let gz = self.zones[zid];
        assert(gz.wf());  // inv_zones_wf
        let p0 = region.phys_page(0);
        assert(region.wf());  // enabled ⇒ count > 0
        assert(region.pages().contains(p0));
        // !contains_region(r): r's pages are free, but a contained region's pages are owned.
        if gz.contains_region(r) {
            lemma_region_in_zone_owns_pages(gz, r);
            assert(zone_owned_pages(gz).contains(p0));
            lemma_zone_owned_in_all_owned(self.zones, zid, p0);  // p0 ∈ all_owned
            assert(self@.hypervisor_owned.contains(p0));  // enabled
            assert(self@.hypervisor_owned == hypervisor_pool(self.zones));  // pool = budget \ owned
            assert(false);
        }
        // !overlaps_vmem(r): an overlapping zone region shares a gpa, which is mapped.

        if gz.mem_set.overlaps_vmem(r) {
            let r2 = choose|r2: MemoryRegion|
                gz.mem_set.regions.contains(r2) && r2.spec_overlaps_vmem(r);
            assert(r2.spec_valid());  // mem_set.wf ⇒ regions valid
            lemma_vmem_overlap_implies_shared_gpa(r2, r);
            let g = choose|g: GuestPage| region_owns_gpa(r2, g) && region_owns_gpa(r, g);
            assert(gz.contains_region(r2));
            lemma_region_in_zone_maps_gpa(gz, r2, g);
            let k = VmPageKey { vm, gpa: g };
            assert(zone_s2_entries(zid, gz).contains_key(k));  // ⇒ k ∈ self@.s2_map
            assert(region.entries().contains_key(k));  // region_owns_gpa(r, g)
            assert(!self@.s2_map.contains_key(k));  // enabled freshness — contradiction
            assert(false);
        }
        // (4) Fire the `insert_region` macro transition; `post.invariant()` from the macro.

        let post = BudgetSpec::take_step::insert_region(self, zid, r);
        assert(post.zone_ids == self.zone_ids);
        assert(post.zones == self.zones.insert(zid, self.zones[zid].insert_region(r)));

        // (5) Projection deltas ⇒ the SoftwareView step.
        lemma_insert_region_owned_pages(self.zones[zid], r);
        lemma_insert_region_all_owned(self.zones, zid, r);
        lemma_insert_region_state_s2_map(self, post, zid, r);
        assert(post@.all_vms =~= self@.all_vms);
        assert(post@.vm_owned =~= self@.vm_owned.insert(
            vm,
            self@.vm_owned[vm].union(region.pages()),
        ));
        assert(post@.s2_map =~= self@.s2_map.union_prefer_right(region.entries()));
        assert(post@.hypervisor_owned =~= self@.hypervisor_owned.difference(region.pages()));
        assert(SoftwareView::insert_region_step(self@, post@, region));
        post
    }

    proof fn remove_region(self, region: Region) -> (post: Self) {
        let vm = region.vm;
        let zid = vm.0;
        assert(vm == VmId(zid));
        assert(self.zone_ids.contains(zid));
        assert(self.zones.contains_key(zid));

        // (1) Recover the budget region via the trusted environment bridge.
        axiom_assignable_from_budget(self, region);
        let r = choose|r: MemoryRegion|
            zone_budget(zid).contains(r) && region_to_abstract(zid, r) == region;
        zone_budget_in_all_regions();
        all_regions_valid();
        all_regions_disjoint();
        assert(all_regions().contains(r) && r.spec_valid());

        // (2) Projection equalities.
        lemma_region_to_abstract_pages(zid, r);
        lemma_region_to_abstract_entries(zid, r);
        assert(region.pages() == region_pages(r));
        assert(region.entries() == region_s2_entries(zid, r));

        // (3) `r` is present in the zone: one of its (owned) pages is backed by a zone
        // region, which must be `r` itself since distinct `all_regions` are pmem-disjoint.
        let gz = self.zones[zid];
        assert(gz.wf());
        let p0 = region.phys_page(0);
        assert(region.wf());
        assert(region.pages().contains(p0));
        assert(self@.vm_owned[vm].contains(p0));  // enabled ⇒ region.pages() ⊆ vm_owned
        assert(self@.vm_owned[vm] == zone_owned_pages(gz));  // view
        lemma_zone_owned_pages_region_witness(gz, p0);
        let r2 = choose|rr: MemoryRegion| gz.regions().contains(rr) && region_owns_page(rr, p0);
        assert(gz.contains_region(r2));
        assert(zone_budget(zid).contains(r2));  // inv: zone regions ⊆ budget
        assert(all_regions().contains(r2) && r2.spec_valid());
        if r2 != r {
            let i2 = choose|i: nat| 0 <= i < r2.pages && region_phys_page(r2, i) == p0;
            let ir = choose|i: nat| 0 <= i < r.pages && region_phys_page(r, i) == p0;
            lemma_same_phys_page_implies_pmem_overlap(r2, i2, r, ir);
            assert(!r2.spec_overlaps_pmem(r));  // all_regions_disjoint
            assert(false);
        }
        assert(gz.contains_region(r));

        // pmem-exclusivity holds for any budget region: distinct `all_regions` are disjoint.
        assert(region_pmem_exclusive(gz, r)) by {
            assert forall|rr: MemoryRegion|
                gz.regions().contains(rr) && rr != r implies !rr.spec_overlaps_pmem(r) by {
                assert(gz.contains_region(rr));  // fires the budget inv
                assert(zone_budget(zid).contains(rr));  // inv
                assert(all_regions().contains(rr));
            }
        }

        // (4) Fire the `remove_region` macro transition; `post.invariant()` from the macro.
        let post = BudgetSpec::take_step::remove_region(self, zid, r);
        assert(post.zone_ids == self.zone_ids);
        assert(post.zones == self.zones.insert(zid, self.zones[zid].remove_region(r)));

        // (5) Projection deltas ⇒ the SoftwareView step.
        lemma_region_pages_in_all_budget(zid, r);  // r's pages are budget pages (pool algebra)
        lemma_remove_region_owned_pages(self.zones[zid], r);
        lemma_remove_region_all_owned(self, zid, r);
        lemma_remove_region_state_s2_map(self, post, zid, r);
        assert(post@.all_vms =~= self@.all_vms);
        assert(post@.vm_owned =~= self@.vm_owned.insert(
            vm,
            self@.vm_owned[vm].difference(region.pages()),
        ));
        assert(post@.s2_map =~= self@.s2_map.remove_keys(region.entries().dom()));
        assert(post@.hypervisor_owned =~= self@.hypervisor_owned.union(region.pages()));
        assert(SoftwareView::remove_region_step(self@, post@, region));
        post
    }
}

// ═════════════════════════ projection transition lemmas ════════════════════════
// (how the `SoftwareView` projection moves under each `BudgetSpec` region transition)
// ───────────────────────── insert_region (gz ↦ gz.insert_region(r)) ──────────
/// Inserting `r` extends a zone's owned-page set by exactly `r`'s pages.
pub proof fn lemma_insert_region_owned_pages(gz: GhostZone, region: MemoryRegion)
    requires
        gz.wf(),
        region.spec_valid(),
        !gz.mem_set.overlaps_vmem(region),
    ensures
        zone_owned_pages(gz.insert_region(region)) =~= zone_owned_pages(gz).union(
            region_pages(region),
        ),
{
    let new_gz = gz.insert_region(region);
    let om = gz.mem_set.mappings;
    let rm = region.spec_mappings();
    assert(new_gz.mem_set.mappings == om.union_prefer_right(rm));

    // Key domains are disjoint.
    assert forall|v: SpecVAddr| om.contains_key(v) implies !rm.contains_key(v) by {
        if rm.contains_key(v) {
            region.lemma_mappings_sound(v);
            let j = choose|j: nat| 0 <= j < region.pages && v == region.spec_page_vaddr(j);
            let f = om[v];
            assert(om.contains_pair(v, f));
            let (r2, i2) = choose|r2: MemoryRegion, i2: nat|
                gz.regions().contains(r2) && 0 <= i2 < r2.pages && v == r2.spec_page_vaddr(i2) && f
                    == r2.spec_frame(i2);
            assert(gz.regions().contains(r2));
            assert(!r2.spec_overlaps_vmem(region));
            MemoryRegion::lemma_pages_disjoint(r2, region, i2, j);  // r2 page i2 != region page j == v
        }
    }

    assert forall|p: PhysPage|
        zone_owned_pages(new_gz).contains(p) <==> (zone_owned_pages(gz).contains(p) || region_pages(
            region,
        ).contains(p)) by {
        // (⟹)
        if zone_owned_pages(new_gz).contains(p) {
            let v = choose|v: SpecVAddr| #[trigger]
                new_gz.mem_set.mappings.contains_key(v) && frame_phys_page(
                    new_gz.mem_set.mappings[v],
                ) == p;
            if rm.contains_key(v) {
                region.lemma_mappings_sound(v);
                let i = choose|i: nat|
                    0 <= i < region.pages && v == region.spec_page_vaddr(i) && rm[v]
                        == region.spec_frame(i);
                assert(new_gz.mem_set.mappings[v] == rm[v]);
                assert(region_phys_page(region, i) == p);
                assert(region_owns_page(region, p));  // witness i
            } else {
                assert(om.contains_key(v) && new_gz.mem_set.mappings[v] == om[v]);
                assert(zone_owned_pages(gz).contains(p));  // witness v
            }
        }
        // (⟸ old)

        if zone_owned_pages(gz).contains(p) {
            let v = choose|v: SpecVAddr| #[trigger]
                om.contains_key(v) && frame_phys_page(om[v]) == p;
            assert(!rm.contains_key(v));
            assert(new_gz.mem_set.mappings.contains_key(v) && new_gz.mem_set.mappings[v] == om[v]);
            assert(zone_owned_pages(new_gz).contains(p));  // witness v
        }
        // (⟸ region)

        if region_pages(region).contains(p) {
            let i = choose|i: nat| 0 <= i < region.pages && region_phys_page(region, i) == p;
            region.lemma_mappings_contains_pair(i);
            let v = region.spec_page_vaddr(i);
            assert(rm.contains_pair(v, region.spec_frame(i)));
            assert(new_gz.mem_set.mappings.contains_key(v) && new_gz.mem_set.mappings[v]
                == region.spec_frame(i));
            assert(frame_phys_page(region.spec_frame(i)) == p);
            assert(zone_owned_pages(new_gz).contains(p));  // witness v
        }
    }
}

/// `all_owned_pages` grows by exactly the inserted region's pages (the
/// whole-state lift of [`lemma_insert_region_owned_pages`]).
pub proof fn lemma_insert_region_all_owned(zones: Map<nat, GhostZone>, zid: nat, r: MemoryRegion)
    requires
        zones.contains_key(zid),
        zones[zid].wf(),
        r.spec_valid(),
        !zones[zid].mem_set.overlaps_vmem(r),
    ensures
        all_owned_pages(zones.insert(zid, zones[zid].insert_region(r))) =~= all_owned_pages(
            zones,
        ).union(region_pages(r)),
{
    let zones2 = zones.insert(zid, zones[zid].insert_region(r));
    lemma_insert_region_owned_pages(zones[zid], r);

    assert forall|p: PhysPage|
        all_owned_pages(zones2).contains(p) <==> (all_owned_pages(zones).contains(p)
            || region_pages(r).contains(p)) by {
        // (⟹)
        if all_owned_pages(zones2).contains(p) {
            let z = choose|z: nat| #[trigger]
                zones2.contains_key(z) && zone_owned_pages(zones2[z]).contains(p);
            if z == zid {
                if zone_owned_pages(zones[zid]).contains(p) {
                    lemma_zone_owned_in_all_owned(zones, zid, p);
                }  // else p ∈ region_pages(r) directly

            } else {
                assert(zones2[z] == zones[z]);
                lemma_zone_owned_in_all_owned(zones, z, p);
            }
        }
        // (⟸ old)

        if all_owned_pages(zones).contains(p) {
            let z = choose|z: nat| #[trigger]
                zones.contains_key(z) && zone_owned_pages(zones[z]).contains(p);
            if z == zid {
                lemma_zone_owned_in_all_owned(zones2, zid, p);
            } else {
                assert(zones2[z] == zones[z]);
                lemma_zone_owned_in_all_owned(zones2, z, p);
            }
        }
        // (⟸ region)

        if region_pages(r).contains(p) {
            lemma_zone_owned_in_all_owned(zones2, zid, p);
        }
    }
}

/// A zone's stage-2 entries gain exactly the inserted region's entries.
pub proof fn lemma_insert_region_s2_entries(zid: nat, gz: GhostZone, r: MemoryRegion)
    requires
        gz.wf(),
        r.spec_valid(),
        !gz.mem_set.overlaps_vmem(r),
    ensures
        zone_s2_entries(zid, gz.insert_region(r)) =~= zone_s2_entries(zid, gz).union_prefer_right(
            region_s2_entries(zid, r),
        ),
{
    let new_gz = gz.insert_region(r);
    let om = gz.mem_set.mappings;
    let rm = r.spec_mappings();
    let nm = new_gz.mem_set.mappings;
    assert(nm == om.union_prefer_right(rm));
    let zg = zone_s2_entries(zid, gz);
    let re = region_s2_entries(zid, r);
    let lhs = zone_s2_entries(zid, new_gz);
    let rhs = zg.union_prefer_right(re);

    assert forall|k: VmPageKey| #[trigger] lhs.contains_key(k) <==> rhs.contains_key(k) by {
        lemma_region_gpa_mapped_iff(r, k.gpa);  // rm.contains_key(v) <==> region_owns_gpa(r, k.gpa)
    }
    assert forall|k: VmPageKey|
        #![trigger lhs[k]]
        #![trigger rhs[k]]
        lhs.contains_key(k) implies lhs[k] == rhs[k] by {
        let v = vaddr_of_gpa(k.gpa);
        lemma_region_gpa_mapped_iff(r, k.gpa);
        if rm.contains_key(v) {
            lemma_region_s2_value(zid, r, k);  // re.contains_key(k), re[k] == frame_to_s2(rm[v])
            assert(nm[v] == rm[v]);  // union prefers right
        } else {
            assert(om.contains_key(v) && nm[v] == om[v]);
            assert(!re.contains_key(k));
            assert(zg.contains_key(k));
        }
    }
}

/// The state's `s2_map` gains exactly the inserted region's entries.
pub proof fn lemma_insert_region_state_s2_map(
    pre: BudgetSpec::State,
    post: BudgetSpec::State,
    zid: nat,
    r: MemoryRegion,
)
    requires
        pre.invariant(),
        pre.zones.contains_key(zid),
        r.spec_valid(),
        !pre.zones[zid].mem_set.overlaps_vmem(r),
        post.zone_ids == pre.zone_ids,
        post.zones == pre.zones.insert(zid, pre.zones[zid].insert_region(r)),
    ensures
        state_s2_map(post) =~= state_s2_map(pre).union_prefer_right(region_s2_entries(zid, r)),
{
    let pre_z = pre.zones[zid];
    assert(pre_z.wf());  // inv_zones_wf
    assert(pre.zone_ids.contains(zid));  // inv_zone_ids
    lemma_insert_region_s2_entries(zid, pre_z, r);
    // zone_s2_entries(zid, post.zones[zid]) == zone_s2_entries(zid, pre_z) ∪ region_s2_entries(zid, r)
    let re = region_s2_entries(zid, r);
    let lhs = state_s2_map(post);
    let rhs = state_s2_map(pre).union_prefer_right(re);

    assert forall|k: VmPageKey| #[trigger] lhs.contains_key(k) <==> rhs.contains_key(k) by {
        let z = k.vm.0;
        if z != zid {
            assert(post.zones[z] == pre.zones[z]);
        }
    }
    assert forall|k: VmPageKey|
        #![trigger lhs[k]]
        #![trigger rhs[k]]
        lhs.contains_key(k) implies lhs[k] == rhs[k] by {
        let z = k.vm.0;
        if z != zid {
            assert(post.zones[z] == pre.zones[z]);
            assert(!re.contains_key(k));  // re keys have vm == VmId(zid)
        }
    }
}

// ───────────────────────── remove_region (gz ↦ gz.remove_region(r)) ──────────
/// Owned pages shrink by exactly the removed region's pages (needs
/// `region_pmem_exclusive`).
pub proof fn lemma_remove_region_owned_pages(gz: GhostZone, r: MemoryRegion)
    requires
        gz.wf(),
        gz.contains_region(r),
        region_pmem_exclusive(gz, r),
    ensures
        zone_owned_pages(gz.remove_region(r)) =~= zone_owned_pages(gz).difference(region_pages(r)),
{
    let new_gz = gz.remove_region(r);
    let om = gz.mem_set.mappings;
    let rm = r.spec_mappings();
    let nm = new_gz.mem_set.mappings;
    assert(nm == om.remove_keys(rm.dom()));
    assert(r.spec_valid());  // r ∈ regions, gz.wf() ⇒ valid

    assert forall|p: PhysPage|
        zone_owned_pages(new_gz).contains(p) <==> (zone_owned_pages(gz).contains(p)
            && !region_pages(r).contains(p)) by {
        // (⟹)
        if zone_owned_pages(new_gz).contains(p) {
            let v = choose|v: SpecVAddr| #[trigger]
                nm.contains_key(v) && frame_phys_page(nm[v]) == p;
            assert(om.contains_key(v) && !rm.contains_key(v) && nm[v] == om[v]);
            assert(zone_owned_pages(gz).contains(p));  // witness v
            if region_pages(r).contains(p) {
                let i = choose|i: nat| 0 <= i < r.pages && region_phys_page(r, i) == p;
                let f = om[v];
                assert(om.contains_pair(v, f));
                let (r2, i2) = choose|r2: MemoryRegion, i2: nat|
                    gz.regions().contains(r2) && 0 <= i2 < r2.pages && v == r2.spec_page_vaddr(i2)
                        && f == r2.spec_frame(i2);
                assert(gz.regions().contains(r2));
                assert(region_phys_page(r2, i2) == p);
                if r2 == r {
                    r.lemma_mappings_contains_pair(i2);  // ⇒ v ∈ rm.dom(): contradiction
                }
                assert(r2 != r);
                assert(r2.spec_valid());
                assert(!r2.spec_overlaps_pmem(r));  // region_pmem_exclusive
                assert(gz.regions().contains(r));  // from contains_region(r)
                lemma_same_phys_page_implies_pmem_overlap(r2, i2, r, i);
                assert(false);
            }
        }
        // (⟸)

        if zone_owned_pages(gz).contains(p) && !region_pages(r).contains(p) {
            let v = choose|v: SpecVAddr| #[trigger]
                om.contains_key(v) && frame_phys_page(om[v]) == p;
            if rm.contains_key(v) {
                r.lemma_mappings_sound(v);
                let i = choose|i: nat|
                    0 <= i < r.pages && v == r.spec_page_vaddr(i) && rm[v] == r.spec_frame(i);
                // gz.wf() completeness pins om[v] to r's frame, so p is one of r's pages.
                assert(gz.regions().contains(r));
                assert(om.contains_pair(r.spec_page_vaddr(i), r.spec_frame(i)));
                assert(om[v] == r.spec_frame(i));
                assert(region_phys_page(r, i) == p);
                assert(region_pages(r).contains(p));  // witness i: contradiction
                assert(false);
            }
            assert(nm.contains_key(v) && nm[v] == om[v]);
            assert(zone_owned_pages(new_gz).contains(p));  // witness v
        }
    }
}

/// `all_owned_pages` shrinks by exactly the removed region's pages (the
/// whole-state lift of [`lemma_remove_region_owned_pages`]).
pub proof fn lemma_remove_region_all_owned(pre: BudgetSpec::State, zid: nat, r: MemoryRegion)
    requires
        pre.invariant(),
        pre.zones.contains_key(zid),
        pre.zones[zid].contains_region(r),
        region_pmem_exclusive(pre.zones[zid], r),
    ensures
        all_owned_pages(pre.zones.insert(zid, pre.zones[zid].remove_region(r))) =~= all_owned_pages(
            pre.zones,
        ).difference(region_pages(r)),
{
    let zones = pre.zones;
    let zones2 = zones.insert(zid, zones[zid].remove_region(r));
    assert(zones[zid].wf());  // inv_zones_wf
    lemma_remove_region_owned_pages(zones[zid], r);
    lemma_state_owned_pages_disjoint(pre);

    // Every page of `r` is owned by `zid`.
    assert forall|p: PhysPage|
        #![trigger region_pages(r).contains(p)]
        region_pages(r).contains(p) implies zone_owned_pages(zones[zid]).contains(p) by {
        let i = choose|i: nat| 0 <= i < r.pages && region_phys_page(r, i) == p;
        let v = r.spec_page_vaddr(i);
        assert(zones[zid].regions().contains(r));
        // completeness clause of `zones[zid].wf()` fires on (r, i):
        assert(zones[zid].mem_set.mappings.contains_pair(v, r.spec_frame(i)));
        assert(frame_phys_page(zones[zid].mem_set.mappings[v]) == p);
        assert(zone_owned_pages(zones[zid]).contains(p));  // witness v
    }

    assert forall|p: PhysPage|
        all_owned_pages(zones2).contains(p) <==> (all_owned_pages(zones).contains(p)
            && !region_pages(r).contains(p)) by {
        // (⟹)
        if all_owned_pages(zones2).contains(p) {
            let z = choose|z: nat| #[trigger]
                zones2.contains_key(z) && zone_owned_pages(zones2[z]).contains(p);
            if z == zid {
                // p ∈ zone_owned(zones[zid]) \ region_pages(r): owned & not r's.
                lemma_zone_owned_in_all_owned(zones, zid, p);
            } else {
                assert(zones2[z] == zones[z]);
                lemma_zone_owned_in_all_owned(zones, z, p);
                // p ∉ region_pages(r): else `zid` and `z` would both own p.
                if region_pages(r).contains(p) {
                    assert(zone_owned_pages(zones[zid]).contains(p));
                    assert(zone_owned_pages(zones[z]).contains(p));
                    assert(false);  // cross-zone disjointness
                }
            }
        }
        // (⟸)

        if all_owned_pages(zones).contains(p) && !region_pages(r).contains(p) {
            let z = choose|z: nat| #[trigger]
                zones.contains_key(z) && zone_owned_pages(zones[z]).contains(p);
            if z == zid {
                lemma_zone_owned_in_all_owned(zones2, zid, p);
            } else {
                assert(zones2[z] == zones[z]);
                lemma_zone_owned_in_all_owned(zones2, z, p);
            }
        }
    }
}

/// A zone's stage-2 entries lose exactly the removed region's keys.
pub proof fn lemma_remove_region_s2_entries(zid: nat, gz: GhostZone, r: MemoryRegion)
    requires
        gz.wf(),
        gz.contains_region(r),
    ensures
        zone_s2_entries(zid, gz.remove_region(r)) =~= zone_s2_entries(zid, gz).remove_keys(
            region_s2_entries(zid, r).dom(),
        ),
{
    let new_gz = gz.remove_region(r);
    let om = gz.mem_set.mappings;
    let rm = r.spec_mappings();
    let nm = new_gz.mem_set.mappings;
    assert(nm == om.remove_keys(rm.dom()));
    assert(r.spec_valid());  // r ∈ regions, gz.wf() ⇒ valid
    let zg = zone_s2_entries(zid, gz);
    let re = region_s2_entries(zid, r);
    let lhs = zone_s2_entries(zid, new_gz);
    let rhs = zg.remove_keys(re.dom());

    assert forall|k: VmPageKey| #[trigger] lhs.contains_key(k) <==> rhs.contains_key(k) by {
        lemma_region_gpa_mapped_iff(r, k.gpa);  // rm.contains_key(v) <==> region_owns_gpa(r, k.gpa)
    }
    assert forall|k: VmPageKey|
        #![trigger lhs[k]]
        #![trigger rhs[k]]
        lhs.contains_key(k) implies lhs[k] == rhs[k] by {
        let v = vaddr_of_gpa(k.gpa);
        assert(nm[v] == om[v]);  // surviving key keeps its value
    }
}

/// The state's `s2_map` loses exactly the removed region's keys.
pub proof fn lemma_remove_region_state_s2_map(
    pre: BudgetSpec::State,
    post: BudgetSpec::State,
    zid: nat,
    r: MemoryRegion,
)
    requires
        pre.invariant(),
        pre.zones.contains_key(zid),
        pre.zones[zid].contains_region(r),
        post.zone_ids == pre.zone_ids,
        post.zones == pre.zones.insert(zid, pre.zones[zid].remove_region(r)),
    ensures
        state_s2_map(post) =~= state_s2_map(pre).remove_keys(region_s2_entries(zid, r).dom()),
{
    let pre_z = pre.zones[zid];
    assert(pre_z.wf());  // inv_zones_wf
    lemma_remove_region_s2_entries(zid, pre_z, r);
    // zone_s2_entries(zid, post.zones[zid]) == zone_s2_entries(zid, pre_z).remove_keys(re.dom())
    let re = region_s2_entries(zid, r);
    let lhs = state_s2_map(post);
    let rhs = state_s2_map(pre).remove_keys(re.dom());

    assert forall|k: VmPageKey| #[trigger] lhs.contains_key(k) <==> rhs.contains_key(k) by {
        let z = k.vm.0;
        if z != zid {
            assert(post.zones[z] == pre.zones[z]);
            assert(!re.contains_key(k));  // re keys have vm == VmId(zid)
        }
    }
    assert forall|k: VmPageKey|
        #![trigger lhs[k]]
        #![trigger rhs[k]]
        lhs.contains_key(k) implies lhs[k] == rhs[k] by {
        let z = k.vm.0;
        if z != zid {
            assert(post.zones[z] == pre.zones[z]);
        }
    }
}

} // verus!
