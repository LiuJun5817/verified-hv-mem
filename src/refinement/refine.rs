//! The refinement: `impl SoftwareOps for BudgetSpec::State`.
//!
//! Where the contract is met.  `invariants()` is the machine's real
//! `invariant()`, so `inv_implies_wf` proves every reachable state projects to a
//! `wf` (hence secure) `SwView`.
//!
//! Each transition method fires the matching `BudgetSpec` macro transition via
//! `BudgetSpec::take_step::*` (which supplies `post.invariant()`) and then proves
//! the corresponding `SwView` step.  `insert_region` / `remove_region` take a
//! machine-level [`Region`] argument: the trusted bridge
//! [`super::view::axiom_assignable_from_budget`] recovers the budget
//! `MemoryRegion` it abstracts, the projection-equality lemmas in [`super::view`]
//! identify their pages/entries, and the deltas in [`super::transition`] assemble
//! the step.  The transition guards (`!contains_region` / `!overlaps_vmem` for
//! insert, `contains_region` / pmem-exclusivity for remove) are *derived* from the
//! closed `SwView::*_enabled` preconditions.
//!
//! Builds on [`super::view`] and [`super::transition`].
use super::transition::*;
use super::view::*;
use crate::address::region::MemoryRegion;
use crate::hv_mem::spec::budget::{zone_budget, zone_budget_in_all_regions, BudgetSpec};
use crate::hv_mem::spec::{all_regions, all_regions_disjoint, all_regions_valid, GhostZone};
use crate::machine::software::{Region, SoftwareOps, SwView};
use crate::machine::types::*;
use crate::memory_set::SpecMemorySet;
use vstd::prelude::*;

verus! {

impl SoftwareOps for BudgetSpec::State {
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

        // (5) Projection deltas ⇒ the SwView step.
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
        assert(SwView::insert_region_step(self@, post@, region));
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

        // (5) Projection deltas ⇒ the SwView step.
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
        assert(SwView::remove_region_step(self@, post@, region));
        post
    }
}

} // verus!
