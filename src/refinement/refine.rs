//! The refinement: `impl SoftwareOps for BudgetSpec::State`.
//!
//! Where the contract is met.  `invariants()` is the machine's real
//! `invariant()`, so `inv_implies_wf` proves every reachable state projects to a
//! `wf` (hence secure) `SwView`.
//!
//! Each transition method fires the matching `BudgetSpec` macro transition via
//! `BudgetSpec::take_step::*` (which supplies `post.invariant()`) and then proves
//! the corresponding `SwView` step.  `insert_region` / `remove_region` use the
//! precondition hooks `insert_region_pre` / `remove_region_pre` to pin
//! `pages`/`entries` to a single budget region, then assemble the step from the
//! projection deltas in [`super::transition`].
//!
//! Builds on [`super::view`] and [`super::transition`].
use super::transition::*;
use super::view::*;
use crate::address::region::MemoryRegion;
use crate::hv_mem::spec::budget::{zone_budget, zone_budget_in_all_regions, BudgetSpec};
use crate::hv_mem::spec::{all_regions, all_regions_valid, GhostZone};
use crate::machine::software::{SoftwareOps, SwView};
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

    /// `pages`/`entries` are exactly some not-yet-present budget region of `vm`.
    open spec fn insert_region_pre(
        self,
        vm: VmId,
        pages: Set<PhysPage>,
        entries: Map<VmPageKey, S2Entry>,
    ) -> bool {
        exists|r: MemoryRegion|
            #![trigger zone_budget(vm.0).contains(r)]
            zone_budget(vm.0).contains(r) && pages == region_pages(r) && entries
                == region_s2_entries(vm.0, r) && !self.zones[vm.0].contains_region(r)
                && !self.zones[vm.0].mem_set.overlaps_vmem(r)
    }

    proof fn insert_region(
        self,
        vm: VmId,
        pages: Set<PhysPage>,
        entries: Map<VmPageKey, S2Entry>,
    ) -> (post: Self) {
        let zid = vm.0;
        // The witnessing budget region from the precondition hook.
        let r = choose|r: MemoryRegion|
            #![auto]
            zone_budget(zid).contains(r) && pages == region_pages(r) && entries
                == region_s2_entries(zid, r) && !self.zones[zid].contains_region(r)
                && !self.zones[zid].mem_set.overlaps_vmem(r);
        // r is valid (budget ⊆ all_regions, all_regions valid).
        zone_budget_in_all_regions();
        all_regions_valid();
        assert(all_regions().contains(r) && r.spec_valid());

        assert(self.zones.contains_key(zid));
        // Fire the `insert_region` macro transition; `post.invariant()` comes from the macro.
        let post = BudgetSpec::take_step::insert_region(self, zid, r);
        assert(post.zone_ids == self.zone_ids);
        assert(post.zones == self.zones.insert(zid, self.zones[zid].insert_region(r)));

        // ── insert_region_step ─────────────────────────────────────────────
        lemma_insert_region_owned_pages(self.zones[zid], r);
        lemma_insert_region_all_owned(self.zones, zid, r);
        lemma_insert_region_state_s2_map(self, post, zid, r);
        assert(post@.all_vms =~= self@.all_vms);
        assert(post@.vm_owned =~= self@.vm_owned.insert(vm, self@.vm_owned[vm].union(pages)));
        assert(post@.s2_map =~= self@.s2_map.union_prefer_right(entries));
        assert(post@.hypervisor_owned =~= self@.hypervisor_owned.difference(pages));
        assert(SwView::insert_region_step(self@, post@, vm, pages, entries));
        post
    }

    /// `pages`/`keys` are exactly some region currently present in `vm`'s zone.
    open spec fn remove_region_pre(
        self,
        vm: VmId,
        pages: Set<PhysPage>,
        keys: Set<VmPageKey>,
    ) -> bool {
        exists|r: MemoryRegion|
            #![trigger self.zones[vm.0].contains_region(r)]
            self.zones[vm.0].contains_region(r) && pages == region_pages(r) && keys
                == region_s2_entries(vm.0, r).dom() && region_pmem_exclusive(self.zones[vm.0], r)
    }

    proof fn remove_region(self, vm: VmId, pages: Set<PhysPage>, keys: Set<VmPageKey>) -> (post:
        Self) {
        let zid = vm.0;
        let r = choose|r: MemoryRegion|
            #![auto]
            self.zones[zid].contains_region(r) && pages == region_pages(r) && keys
                == region_s2_entries(zid, r).dom() && region_pmem_exclusive(self.zones[zid], r);

        assert(self.zones.contains_key(zid));
        // Fire the `remove_region` macro transition; `post.invariant()` comes from the
        // macro.  (`region_pmem_exclusive` is not part of the transition — it is a
        // refinement-side hypothesis for the page delta, supplied via `remove_region_pre`.)
        let post = BudgetSpec::take_step::remove_region(self, zid, r);
        assert(post.zone_ids == self.zone_ids);
        assert(post.zones == self.zones.insert(zid, self.zones[zid].remove_region(r)));

        // ── remove_region_step ─────────────────────────────────────────────
        // `pages` are budget pages — needed for the hypervisor-pool union algebra.
        assert(zone_budget(zid).contains(r));
        lemma_region_pages_in_all_budget(zid, r);
        assert(forall|pp: PhysPage| #[trigger]
            pages.contains(pp) ==> all_budget_pages().contains(pp));

        assert(self.zones[zid].wf());
        lemma_remove_region_owned_pages(self.zones[zid], r);
        lemma_remove_region_all_owned(self, zid, r);
        lemma_remove_region_state_s2_map(self, post, zid, r);
        assert(post@.all_vms =~= self@.all_vms);
        assert(post@.vm_owned =~= self@.vm_owned.insert(vm, self@.vm_owned[vm].difference(pages)));
        assert(post@.s2_map =~= self@.s2_map.remove_keys(keys));
        assert(post@.hypervisor_owned =~= self@.hypervisor_owned.union(pages));
        assert(SwView::remove_region_step(self@, post@, vm, pages, keys));
        post
    }
}

} // verus!
