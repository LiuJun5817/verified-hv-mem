//! Transition lemmas: how the `SwView` projection moves under each `BudgetSpec`
//! transition.
//!
//! `refine`'s `insert_region` / `remove_region` proofs need to know exactly how
//! the projection ([`super::view`]) changes when a region is added to / removed
//! from a zone.  Each lemma here states one such delta.
//!
//! Well-formedness preservation is **not** restated here: `refine` fires the real
//! `BudgetSpec` transition via `BudgetSpec::take_step::*`, which yields
//! `post.invariant()` (hence each zone's `wf()`) from the macro's own inductiveness.
//!
//! All deltas in this module are **proven**.  Each owned-page / `s2_map` delta is
//! established per zone on the exposed mapping (the insert side unions `r`'s dense
//! keys, the remove side deletes them) and then lifted over the `zones` map.  The
//! remove side relies on `region_pmem_exclusive` for *physical* pages (a page is
//! freed only if no other region backs it) and on cross-zone disjointness to lift
//! that to the whole state; the `s2_map` (vaddr-keyed) deltas need neither, since
//! distinct regions are vmem-disjoint.  All deltas are fully proven — the physical
//! reasoning ([`lemma_same_phys_page_implies_pmem_overlap`] in [`super::view`])
//! rests on the trusted `all_regions_pmem_linear` axiom, no `admit()`.
use super::view::*;
use crate::address::addr::SpecVAddr;
use crate::address::frame::SpecFrame;
use crate::address::region::MemoryRegion;
use crate::hv_mem::spec::budget::{zone_budget, zone_budget_in_all_regions, BudgetSpec};
use crate::hv_mem::spec::{all_regions, all_regions_pmem_linear, GhostZone};
use crate::machine::types::*;
use vstd::prelude::*;

verus! {

// ───────────────────────── insert_region (gz ↦ gz.insert_region(r)) ──────────
/// Inserting `r` extends a zone's owned-page set by exactly `r`'s pages.
///
/// Reasoning is on the exposed mapping: the new page table is the old one
/// unioned with `r`'s dense mappings, whose key domains are disjoint (the new
/// region is vmem-disjoint from every existing one), so the backed-page set is
/// the union of the two.
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

    // Key domains are disjoint: an existing mapping key is some existing region's
    // page vaddr, which is vmem-disjoint from every page of `region`.
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
        // (⟹) the backing key is either `region`'s (a region page) or the old map's.
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
        // (⟸ old) an old backing key survives the (domain-disjoint) union unchanged.

        if zone_owned_pages(gz).contains(p) {
            let v = choose|v: SpecVAddr| #[trigger]
                om.contains_key(v) && frame_phys_page(om[v]) == p;
            assert(!rm.contains_key(v));
            assert(new_gz.mem_set.mappings.contains_key(v) && new_gz.mem_set.mappings[v] == om[v]);
            assert(zone_owned_pages(new_gz).contains(p));  // witness v
        }
        // (⟸ region) a page of `region` is mapped in the union to `region`'s frame.

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

/// `all_owned_pages` grows by exactly the inserted region's pages.
///
/// Only zone `zid` changes; its owned-page delta is [`lemma_insert_region_owned_pages`],
/// and the union over zones lifts that delta to the whole state.
pub proof fn lemma_all_owned_insert_region(zones: Map<nat, GhostZone>, zid: nat, r: MemoryRegion)
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
    // zone_owned_pages(zones2[zid]) == zone_owned_pages(zones[zid]) ∪ region_pages(r)

    assert forall|p: PhysPage|
        all_owned_pages(zones2).contains(p) <==> (all_owned_pages(zones).contains(p)
            || region_pages(r).contains(p)) by {
        // (⟹) the witnessing zone is either `zid` (old owned ∪ region) or unchanged.
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
        // (⟸ old) an old owner survives; zone `zid` only grows.

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
        // (⟸ region) a region page is owned by the (grown) zone `zid`.

        if region_pages(r).contains(p) {
            lemma_zone_owned_in_all_owned(zones2, zid, p);
        }
    }
}

/// A zone's stage-2 entries gain exactly the inserted region's entries (the
/// per-zone dual of [`lemma_insert_region_owned_pages`], on guest-page keys).
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
        let v = gpa_to_vaddr(k.gpa);
        lemma_region_gpa_mapped_iff(r, k.gpa);
        if rm.contains_key(v) {
            lemma_region_s2_value(zid, r, k);  // re.contains_key(k), re[k] == frame_s2_entry(rm[v])
            assert(nm[v] == rm[v]);  // union prefers right
        } else {
            assert(om.contains_key(v) && nm[v] == om[v]);
            assert(!re.contains_key(k));
            assert(zg.contains_key(k));
        }
    }
}

/// The state's `s2_map` gains exactly the inserted region's entries.
pub proof fn lemma_state_s2_map_insert_region(
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
// NOTE: the page/owned deltas below require `region_pmem_exclusive` — removing
// `r` only frees a page if no *other* region in the zone also backs it.  Without
// that hypothesis these are false; it is established by `remove_region_pre`.
/// Owned pages shrink by exactly the removed region's pages.
///
/// Dual to [`lemma_insert_region_owned_pages`], reasoning on the exposed mapping:
/// removal deletes exactly `r`'s dense keys.  A surviving key still backs its old
/// physical page (so nothing else is lost), and a deleted key's page is not backed
/// by any *other* region — that is precisely `region_pmem_exclusive`, via
/// [`lemma_same_phys_page_implies_pmem_overlap`].
pub proof fn lemma_remove_region_owned_pages(gz: GhostZone, r: MemoryRegion)
    requires
        gz.wf(),
        gz.contains_region(r),
        region_pmem_exclusive(gz, r),
        forall|rr: MemoryRegion| #[trigger] gz.regions().contains(rr) ==> rr.pmem_linear(),
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
        // (⟹) a surviving key keeps its old page and that page is not `r`'s.
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
                assert(r2.pmem_linear() && r.pmem_linear());  // forall precondition
                lemma_same_phys_page_implies_pmem_overlap(r2, i2, r, i);
                assert(false);
            }
        }
        // (⟸) an old key whose page is not `r`'s survives the key removal.

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

/// `all_owned_pages` shrinks by exactly the removed region's pages.
///
/// Zone `zid`'s delta is [`lemma_remove_region_owned_pages`].  Lifting it needs
/// that no *other* zone owns `r`'s pages: `r`'s pages are owned by `zid` (dense
/// completeness), so cross-zone disjointness ([`lemma_state_owned_pages_disjoint`])
/// keeps every other zone clear of them.
pub proof fn lemma_all_owned_remove_region(pre: BudgetSpec::State, zid: nat, r: MemoryRegion)
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
    // zone's regions ⊆ budget ⊆ all_regions ⇒ pmem_linear.
    all_regions_pmem_linear();
    zone_budget_in_all_regions();
    assert forall|rr: MemoryRegion| #[trigger]
        zones[zid].regions().contains(rr) implies rr.pmem_linear() by {
        assert(zones[zid].contains_region(rr));  // inv_zone_within_budget ⇒ in budget
        assert(zone_budget(zid).contains(rr));
        assert(all_regions().contains(rr));
    }
    lemma_remove_region_owned_pages(zones[zid], r);
    // zone_owned_pages(zones2[zid]) == zone_owned_pages(zones[zid]) \ region_pages(r)
    lemma_state_owned_pages_disjoint(pre);

    // Every page of `r` is owned by `zid` (dense completeness of the mapping).
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

/// A zone's stage-2 entries lose exactly the removed region's keys (the per-zone
/// dual of [`lemma_remove_region_owned_pages`], on guest-page keys).
///
/// No `region_pmem_exclusive` is needed here: keys are vaddrs, and distinct
/// regions are vmem-disjoint (`gz.wf()`), so `r`'s keys are uniquely `r`'s.
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
        let v = gpa_to_vaddr(k.gpa);
        assert(nm[v] == om[v]);  // surviving key keeps its value
    }
}

/// The state's `s2_map` loses exactly the removed region's keys.
pub proof fn lemma_state_s2_map_remove_region(
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
