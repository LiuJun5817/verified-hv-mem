//! Transition lemmas: how the `SwView` projection moves under each `BudgetSpec`
//! transition.
//!
//! `refine`'s `insert_region` / `remove_region` proofs need to know exactly how
//! the projection ([`super::view`]) changes when a region is added to / removed
//! from a zone.  Each lemma here states one such delta.
//!
//! Status:
//! - `lemma_insert_region_owned_pages` is **proven** (set extensionality).
//! - the rest are the remaining **analytic** obligations — well-formedness
//!   (mirrors `BudgetSpec`'s own `insert_region_inductive`), the `all_owned`
//!   deltas (set algebra), and the `choose`-heavy `s2_map` `Map` equalities.
//!   Each is a *true* statement (the remove ones require `region_pmem_exclusive`,
//!   without which they are false); their bodies are `admit()` pending proof.
use super::view::*;
use crate::address::addr::SpecVAddr;
use crate::address::region::MemoryRegion;
use crate::hv_mem::spec::budget::BudgetSpec;
use crate::hv_mem::spec::GhostZone;
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
            let v = choose|v: SpecVAddr|
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
            let v = choose|v: SpecVAddr| om.contains_key(v) && frame_phys_page(om[v]) == p;
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

/// Inserting a non-overlapping valid region preserves zone well-formedness
/// (mirrors `BudgetSpec`'s `insert_region_inductive`).
pub proof fn lemma_ghost_zone_insert_region_wf(gz: GhostZone, r: MemoryRegion)
    requires
        gz.wf(),
        r.spec_valid(),
        !gz.mem_set.overlaps_vmem(r),
    ensures
        gz.insert_region(r).wf(),
{
    admit();
}

/// `all_owned_pages` grows by exactly the inserted region's pages.
pub proof fn lemma_all_owned_insert_region(zones: Map<nat, GhostZone>, zid: nat, r: MemoryRegion)
    requires
        zones.contains_key(zid),
    ensures
        all_owned_pages(zones.insert(zid, zones[zid].insert_region(r))) =~= all_owned_pages(
            zones,
        ).union(region_pages(r)),
{
    admit();
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
        !pre.zones[zid].mem_set.overlaps_vmem(r),
        post.zone_ids == pre.zone_ids,
        post.zones == pre.zones.insert(zid, pre.zones[zid].insert_region(r)),
    ensures
        state_s2_map(post) =~= state_s2_map(pre).union_prefer_right(region_s2_entries(zid, r)),
{
    admit();
}

// ───────────────────────── remove_region (gz ↦ gz.remove_region(r)) ──────────
// NOTE: the page/owned deltas below require `region_pmem_exclusive` — removing
// `r` only frees a page if no *other* region in the zone also backs it.  Without
// that hypothesis these are false; it is established by `remove_region_pre`.
/// Owned pages shrink by exactly the removed region's pages.
pub proof fn lemma_remove_region_owned_pages(gz: GhostZone, r: MemoryRegion)
    requires
        gz.contains_region(r),
        region_pmem_exclusive(gz, r),
    ensures
        zone_owned_pages(gz.remove_region(r)) =~= zone_owned_pages(gz).difference(region_pages(r)),
{
    admit();
}

/// `all_owned_pages` shrinks by exactly the removed region's pages.
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
    admit();
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
        post.zone_ids == pre.zone_ids,
        post.zones == pre.zones.insert(zid, pre.zones[zid].remove_region(r)),
    ensures
        state_s2_map(post) =~= state_s2_map(pre).remove_keys(region_s2_entries(zid, r).dom()),
{
    admit();
}

} // verus!
