//! Layer 3 — transition lemmas: how the `SwView` projection moves under each
//! `BudgetSpec` transition.
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
use super::geometry::*;
use super::view::*;
use crate::address::region::MemoryRegion;
use crate::hv_mem::spec::budget::BudgetSpec;
use crate::hv_mem::spec::GhostZone;
use crate::machine::types::*;
use vstd::prelude::*;

verus! {

// ───────────────────────── insert_region (gz ↦ gz.insert_region(r)) ──────────
/// Inserting `r` extends a zone's owned-page set by exactly `r`'s pages.
pub proof fn lemma_insert_region_owned_pages(gz: GhostZone, region: MemoryRegion)
    ensures
        zone_owned_pages(gz.insert_region(region)) =~= zone_owned_pages(gz).union(
            region_pages(region),
        ),
{
    let new_gz = gz.insert_region(region);
    assert(new_gz.regions() =~= gz.regions().insert(region));
    assert(new_gz.regions().contains(region));
    assert forall|p: PhysPage|
        zone_owned_pages(new_gz).contains(p) <==> (zone_owned_pages(gz).contains(p) || region_pages(
            region,
        ).contains(p)) by {
        // (⟹) a backing region in `new` is either an old region or `region`.
        if zone_owned_pages(new_gz).contains(p) {
            let r = choose|r: MemoryRegion|
                #![trigger new_gz.regions().contains(r)]
                new_gz.regions().contains(r) && region_owns_page(r, p);
            assert(new_gz.regions().contains(r) && region_owns_page(r, p));
            if r == region {
                assert(region_pages(region).contains(p));
            } else {
                assert(gz.regions().contains(r));
                assert(zone_owned_pages(gz).contains(p));  // witness r
            }
        }
        // (⟸ old) an old backing region is still in `new`.
        if zone_owned_pages(gz).contains(p) {
            let r = choose|r: MemoryRegion|
                #![trigger gz.regions().contains(r)]
                gz.regions().contains(r) && region_owns_page(r, p);
            assert(new_gz.regions().contains(r) && region_owns_page(r, p));
            assert(zone_owned_pages(new_gz).contains(p));  // witness r
        }
        // (⟸ region) `region` itself backs p and is in `new`.
        if region_pages(region).contains(p) {
            assert(region_owns_page(region, p));
            assert(zone_owned_pages(new_gz).contains(p));  // witness region
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
