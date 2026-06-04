//! The refinement: `impl SoftwareOps for BudgetSpec::State`.
//!
//! This is where the contract is met.  The decisive point: `invariants()` *is*
//! `BudgetSpec::State::invariant()` (the machine's real, inductively-proven
//! invariant), so `inv_implies_wf` + the macro's reachability guarantee ⇒ every
//! reachable state `HvMem` drives projects to a `wf` (hence secure) `SwView`.
//!
//! Each transition method:
//! - `add_vm` / `remove_vm` are proven outright (construct the post-state,
//!   discharge `invariant()` from the budget axioms, prove the `SwView` step);
//! - `insert_region` / `remove_region` use the implementor-defined precondition
//!   hooks `insert_region_pre` / `remove_region_pre` to pin `pages`/`entries` to a
//!   single budget region, then assemble the `SwView` step from the projection
//!   deltas in [`super::transition`].
//!
//! `lemma_state_owned_pages_disjoint` (the cross-zone half of `ownership_wf`) is
//! proven here from the real `invariant()` + the budget axioms.
//!
//! Depends on the helper modules [`super::view`] and [`super::transition`].
use super::transition::*;
use super::view::*;
use crate::address::region::MemoryRegion;
use crate::hv_mem::spec::budget::{
    zone_budget, zone_budget_in_all_regions, zone_budget_pairwise_disjoint, BudgetSpec,
};
use crate::hv_mem::spec::{all_regions, all_regions_disjoint, all_regions_valid, GhostZone};
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
        let s = *self;
        let sw = self.view();

        // sharing_wf: vacuous (shared_pages ≡ ∅).
        assert(sw.shared_pages =~= Set::<SharedPage>::empty());
        assert(sw.sharing_wf());

        // ownership_wf: dom; cross-zone disjointness; vm-vs-hypervisor disjointness.
        assert(sw.vm_owned.dom() =~= sw.all_vms);
        lemma_state_owned_pages_disjoint(s);
        assert forall|vm: VmId, page: PhysPage|
            sw.all_vms.contains(vm) && #[trigger] sw.vm_owned[vm].contains(
                page,
            ) implies !sw.hypervisor_owned.contains(page) by {
            // vm.0 ∈ zones.dom (inv_zone_ids) and page ∈ zone_owned ⇒ all_owned ⇒ not in pool.
            assert(s.zones.contains_key(vm.0));
            lemma_zone_owned_in_all_owned(s.zones, vm.0, page);
        }
        assert(sw.ownership_wf());

        // translation_wf.
        assert forall|key: VmPageKey| #[trigger] sw.s2_map.contains_key(key) implies (
        sw.all_vms.contains(key.vm) && sw.owned_or_shared(key.vm, sw.s2_map[key].page)) by {
            lemma_zone_s2_target_owned(key.vm.0, s.zones[key.vm.0]);
        }
        assert(sw.translation_wf());

        assert(sw.wf());
    }

    proof fn add_vm(self, vm: VmId) -> (post: Self) {
        let empty_zone = GhostZone {
            mem_set: SpecMemorySet {
                regions: Set::<MemoryRegion>::empty(),
                mappings: Map::empty(),
            },
        };
        let post = BudgetSpec::State {
            zone_ids: self.zone_ids.insert(vm.0),
            zones: self.zones.insert(vm.0, empty_zone),
        };
        assert(empty_zone.regions() =~= Set::<MemoryRegion>::empty());
        assert(empty_zone.mem_set.mappings =~= Map::empty());
        assert(empty_zone.wf());
        lemma_zone_owned_pages_empty(empty_zone);
        lemma_zone_s2_entries_empty(vm.0, empty_zone);
        // post.invariant(): only the (vacuous) new zone is added.
        assert(post.zones.dom() =~= post.zone_ids);
        assert forall|zid: nat|
            #![auto]
            post.zones.contains_key(zid) implies post.zones[zid].wf() by {
            if zid != vm.0 {
                assert(self.zones.contains_key(zid) && self.zones[zid].wf());
            }
        }
        assert forall|zid: nat, r: MemoryRegion|
            #![auto]
            post.zones.contains_key(zid) && post.zones[zid].contains_region(r) implies zone_budget(
            zid,
        ).contains(r) by {
            if zid == vm.0 {
                assert(post.zones[zid].regions() =~= Set::<MemoryRegion>::empty());
            } else {
                assert(self.zones.contains_key(zid) && self.zones[zid].contains_region(r));
            }
        }
        zone_budget_in_all_regions();
        zone_budget_pairwise_disjoint();
        assert(post.invariant());
        // add_vm_step: the new zone contributes nothing, so all_owned is unchanged.
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
        let post = BudgetSpec::State {
            zone_ids: self.zone_ids.remove(vm.0),
            zones: self.zones.remove(vm.0),
        };
        // post.invariant(): removing a zone only shrinks the maps.
        assert(post.zones.dom() =~= post.zone_ids);
        assert forall|zid: nat|
            #![auto]
            post.zones.contains_key(zid) implies post.zones[zid].wf() by {
            assert(self.zones.contains_key(zid) && self.zones[zid].wf());
        }
        assert forall|zid: nat, r: MemoryRegion|
            #![auto]
            post.zones.contains_key(zid) && post.zones[zid].contains_region(r) implies zone_budget(
            zid,
        ).contains(r) by {
            assert(self.zones.contains_key(zid) && self.zones[zid].contains_region(r));
        }
        zone_budget_in_all_regions();
        zone_budget_pairwise_disjoint();
        assert(post.invariant());
        // remove_vm_step: the removed zone owned nothing, so all_owned is unchanged.
        assert(self@.vm_owned[vm] == Set::<PhysPage>::empty());  // precondition
        assert(zone_owned_pages(self.zones[vm.0]) =~= Set::<PhysPage>::empty());
        assert(all_owned_pages(post.zones) =~= all_owned_pages(self.zones)) by {
            assert forall|pp: PhysPage|
                all_owned_pages(self.zones).contains(pp) implies all_owned_pages(
                post.zones,
            ).contains(pp) by {
                let zid = choose|zid: nat|
                    #![auto]
                    self.zones.contains_key(zid) && zone_owned_pages(self.zones[zid]).contains(pp);
                // the removed zone vm.0 owns nothing, so the witness zid ≠ vm.0.
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
        // Recover the witnessing budget region from the precondition hook.
        let r = choose|r: MemoryRegion|
            #![auto]
            zone_budget(zid).contains(r) && pages == region_pages(r) && entries
                == region_s2_entries(zid, r) && !self.zones[zid].contains_region(r)
                && !self.zones[zid].mem_set.overlaps_vmem(r);
        assert(zone_budget(zid).contains(r) && pages == region_pages(r) && entries
            == region_s2_entries(zid, r) && !self.zones[zid].contains_region(r)
            && !self.zones[zid].mem_set.overlaps_vmem(r));
        // r is valid (budget ⊆ all_regions, all_regions valid).
        zone_budget_in_all_regions();
        all_regions_valid();
        assert(all_regions().contains(r) && r.spec_valid());

        assert(self.zones.contains_key(zid));
        assert(self.zones[zid].wf());
        let new_zone = self.zones[zid].insert_region(r);
        let post = BudgetSpec::State {
            zone_ids: self.zone_ids,
            zones: self.zones.insert(zid, new_zone),
        };

        // ── post.invariant() ───────────────────────────────────────────────
        lemma_ghost_zone_insert_region_wf(self.zones[zid], r);
        assert(new_zone.wf());
        assert(new_zone.regions() =~= self.zones[zid].regions().insert(r));
        assert(post.zones.dom() =~= post.zone_ids);
        assert forall|z: nat| #![auto] post.zones.contains_key(z) implies post.zones[z].wf() by {
            if z != zid {
                assert(self.zones.contains_key(z) && self.zones[z].wf());
            }
        }
        assert forall|z: nat, rr: MemoryRegion|
            #![auto]
            post.zones.contains_key(z) && post.zones[z].contains_region(rr) implies zone_budget(
            z,
        ).contains(rr) by {
            if z == zid {
                if rr != r {
                    assert(self.zones[zid].contains_region(rr));
                }
            } else {
                assert(self.zones.contains_key(z) && self.zones[z].contains_region(rr));
            }
        }
        zone_budget_pairwise_disjoint();
        assert(post.invariant());

        // ── insert_region_step ─────────────────────────────────────────────
        lemma_insert_region_owned_pages(self.zones[zid], r);
        lemma_all_owned_insert_region(self.zones, zid, r);
        lemma_state_s2_map_insert_region(self, post, zid, r);
        assert(post@.all_vms =~= self@.all_vms);
        assert(post@.vm_owned =~= self@.vm_owned.insert(vm, self@.vm_owned[vm].union(pages)));
        assert(post@.s2_map =~= self@.s2_map.union_prefer_right(entries));
        // hypervisor_owned loses exactly `pages` (set algebra A\(B∪P) = (A\B)\P).
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
        assert(self.zones[zid].contains_region(r) && pages == region_pages(r) && keys
            == region_s2_entries(zid, r).dom() && region_pmem_exclusive(self.zones[zid], r));

        assert(self.zones.contains_key(zid));
        assert(self.zones[zid].wf());
        let new_zone = self.zones[zid].remove_region(r);
        let post = BudgetSpec::State {
            zone_ids: self.zone_ids,
            zones: self.zones.insert(zid, new_zone),
        };

        // ── post.invariant(): removing a present region keeps the zone wf ──
        assert(new_zone.regions() =~= self.zones[zid].regions().remove(r));
        assert(self.zones[zid].contains_region(r));
        self.zones[zid].lemma_remove_region_wf(r);
        assert(new_zone.wf());
        assert(post.zones.dom() =~= post.zone_ids);
        assert forall|z: nat| #![auto] post.zones.contains_key(z) implies post.zones[z].wf() by {
            if z != zid {
                assert(self.zones.contains_key(z) && self.zones[z].wf());
            }
        }
        assert forall|z: nat, rr: MemoryRegion|
            #![auto]
            post.zones.contains_key(z) && post.zones[z].contains_region(rr) implies zone_budget(
            z,
        ).contains(rr) by {
            if z == zid {
                assert(self.zones[zid].contains_region(rr));
            } else {
                assert(self.zones.contains_key(z) && self.zones[z].contains_region(rr));
            }
        }
        zone_budget_in_all_regions();
        zone_budget_pairwise_disjoint();
        assert(post.invariant());

        // ── remove_region_step ─────────────────────────────────────────────
        // `pages` lie in some budget (so they are budget pages) — needed for the
        // hypervisor-pool union algebra.
        assert(zone_budget(zid).contains(r));
        lemma_region_pages_in_all_budget(zid, r);
        assert(forall|pp: PhysPage| #[trigger]
            pages.contains(pp) ==> all_budget_pages().contains(pp));

        lemma_remove_region_owned_pages(self.zones[zid], r);
        lemma_all_owned_remove_region(self, zid, r);
        lemma_state_s2_map_remove_region(self, post, zid, r);
        assert(post@.all_vms =~= self@.all_vms);
        assert(post@.vm_owned =~= self@.vm_owned.insert(vm, self@.vm_owned[vm].difference(pages)));
        assert(post@.s2_map =~= self@.s2_map.remove_keys(keys));
        assert(post@.hypervisor_owned =~= self@.hypervisor_owned.union(pages));
        assert(SwView::remove_region_step(self@, post@, vm, pages, keys));
        post
    }
}

/// Cross-zone physical-page disjointness, proven from the **real** `invariant()`
/// (`inv_zone_within_budget` + `inv_zones_wf`) plus the budget axioms.
pub proof fn lemma_state_owned_pages_disjoint(s: BudgetSpec::State)
    requires
        s.invariant(),
    ensures
        forall|zid1: nat, zid2: nat, p: PhysPage|
            #![trigger zone_owned_pages(s.zones[zid1]).contains(p), s.zones[zid2]]
            s.zones.contains_key(zid1) && s.zones.contains_key(zid2) && zid1 != zid2
                && zone_owned_pages(s.zones[zid1]).contains(p) ==> !zone_owned_pages(
                s.zones[zid2],
            ).contains(p),
{
    assert forall|zid1: nat, zid2: nat, p: PhysPage|
        #![trigger zone_owned_pages(s.zones[zid1]).contains(p), s.zones[zid2]]
        s.zones.contains_key(zid1) && s.zones.contains_key(zid2) && zid1 != zid2
            && zone_owned_pages(s.zones[zid1]).contains(p) implies !zone_owned_pages(
        s.zones[zid2],
    ).contains(p) by {
        if zone_owned_pages(s.zones[zid2]).contains(p) {
            let gz1 = s.zones[zid1];
            let gz2 = s.zones[zid2];
            assert(gz1.wf());
            assert(gz2.wf());

            // Recover backing regions from the exposed mappings (exact-dense soundness).
            lemma_zone_owned_pages_region_witness(gz1, p);
            lemma_zone_owned_pages_region_witness(gz2, p);

            let r1 = choose|r: MemoryRegion|
                #![trigger gz1.regions().contains(r)]
                gz1.regions().contains(r) && region_owns_page(r, p);
            assert(gz1.regions().contains(r1) && region_owns_page(r1, p));
            let i1 = choose|i: nat| 0 <= i < r1.pages && region_phys_page(r1, i) == p;
            assert(0 <= i1 < r1.pages && region_phys_page(r1, i1) == p);

            let r2 = choose|r: MemoryRegion|
                #![trigger gz2.regions().contains(r)]
                gz2.regions().contains(r) && region_owns_page(r, p);
            assert(gz2.regions().contains(r2) && region_owns_page(r2, p));
            let i2 = choose|i: nat| 0 <= i < r2.pages && region_phys_page(r2, i) == p;
            assert(0 <= i2 < r2.pages && region_phys_page(r2, i2) == p);

            assert(r1.spec_valid());
            assert(r2.spec_valid());

            assert(gz1.contains_region(r1));
            assert(gz2.contains_region(r2));
            assert(zone_budget(zid1).contains(r1));
            assert(zone_budget(zid2).contains(r2));

            zone_budget_pairwise_disjoint();
            assert(!zone_budget(zid2).contains(r1));
            assert(r1 != r2);
            zone_budget_in_all_regions();
            assert(all_regions().contains(r1) && all_regions().contains(r2));
            all_regions_disjoint();
            assert(!r1.spec_overlaps_pmem(r2));

            lemma_same_phys_page_implies_pmem_overlap(r1, i1, r2, i2);
            assert(r1.spec_overlaps_pmem(r2));
            assert(false);
        }
    }
}

} // verus!
