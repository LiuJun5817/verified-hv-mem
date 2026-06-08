//! Transition lemmas: how the `SwView` projection ([`super::view`]) moves under
//! each `BudgetSpec` region transition.
//!
//! Each lemma states one delta — how a zone's `owned_pages` / `s2_entries` (and
//! their whole-state lifts `all_owned` / `state_s2_map`) change when a region is
//! inserted into or removed from a zone.  These are the deltas `refine` assembles
//! into the `SwView` `insert_region_step` / `remove_region_step`.
use super::view::*;
use crate::address::addr::SpecVAddr;
use crate::address::frame::SpecFrame;
use crate::address::region::MemoryRegion;
use crate::hv_mem::spec::budget::BudgetSpec;
use crate::hv_mem::spec::GhostZone;
use crate::machine::types::*;
use vstd::prelude::*;

verus! {

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
        let v = gpa_to_vaddr(k.gpa);
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
