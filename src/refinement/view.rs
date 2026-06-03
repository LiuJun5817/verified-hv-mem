//! Layer 2 — the abstraction relation R: project `BudgetSpec::State` → `SwView`.
//!
//! The abstract state is the state machine's own `BudgetSpec::State` (its
//! `zone_ids` and per-zone `GhostZone` region sets) — **not** a hand-written
//! twin.  `<BudgetSpec::State as View>::view` (= `sw_view_of`) maps it to the
//! security model's `SwView`.  Because the projection runs on the machine's real
//! state, the contract invariant in [`super::refine`] can be the machine's real
//! `invariant()`, and the global `SwView` step shape is available without
//! serializing anything (the runtime authority stays in the sharded tokens).
//!
//! This layer builds the projection out of the per-region geometry in
//! [`super::geometry`]: per-zone sets (`zone_owned_pages`, `zone_s2_entries`),
//! the global views (`all_budget_pages`, `all_owned_pages`, `hypervisor_pool`,
//! `state_s2_map`), and the small "facts about the projection" lemmas the
//! refinement needs.
use super::geometry::*;
use crate::address::region::MemoryRegion;
use crate::hv_mem::spec::budget::{zone_budget, BudgetSpec};
use crate::hv_mem::spec::GhostZone;
use crate::machine::software::SwView;
use crate::machine::types::*;
use vstd::prelude::*;

verus! {

// ─────────────────────────── per-zone projections ───────────────────────────
/// Physical pages owned by a zone: the union over its regions of backed pages.
pub open spec fn zone_owned_pages(gz: GhostZone) -> Set<PhysPage> {
    Set::new(
        |p: PhysPage|
            exists|r: MemoryRegion| #[trigger] gz.regions().contains(r) && region_owns_page(r, p),
    )
}

/// Stage-2 entries installed by a zone: the union over its regions' entries.
pub open spec fn zone_s2_entries(zid: nat, gz: GhostZone) -> Map<VmPageKey, S2Entry> {
    Map::new(
        |k: VmPageKey|
            k.vm == VmId(zid) && exists|r: MemoryRegion| #[trigger]
                gz.regions().contains(r) && region_owns_gpa(r, k.gpa),
        |k: VmPageKey|
            {
                let r = choose|r: MemoryRegion|
                    gz.regions().contains(r) && region_owns_gpa(r, k.gpa);
                let i = choose|i: nat| 0 <= i < r.pages && region_guest_page(r, i) == k.gpa;
                S2Entry {
                    page: region_phys_page(r, i),
                    access: attr_to_perms(r.attr),
                    generation: 0,
                }
            },
    )
}

// ───────────────────────────── global views ─────────────────────────────────
/// All physical pages that lie within *some* zone's static budget.
pub open spec fn all_budget_pages() -> Set<PhysPage> {
    Set::new(
        |pp: PhysPage|
            exists|zid: nat, r: MemoryRegion|
                #![trigger zone_budget(zid).contains(r), region_owns_page(r, pp)]
                zone_budget(zid).contains(r) && region_owns_page(r, pp),
    )
}

/// Physical pages currently owned by some active zone.
pub open spec fn all_owned_pages(zones: Map<nat, GhostZone>) -> Set<PhysPage> {
    Set::new(
        |pp: PhysPage|
            exists|zid: nat|
                #![trigger zones.contains_key(zid)]
                zones.contains_key(zid) && zone_owned_pages(zones[zid]).contains(pp),
    )
}

/// Physical pages that belong to no zone (the hypervisor pool): budget pages not
/// currently owned by any active zone.
pub open spec fn hypervisor_pool(zones: Map<nat, GhostZone>) -> Set<PhysPage> {
    all_budget_pages().difference(all_owned_pages(zones))
}

/// Stage-2 map of the whole state: the union of each zone's `zone_s2_entries`.
pub open spec fn state_s2_map(s: BudgetSpec::State) -> Map<VmPageKey, S2Entry> {
    Map::new(
        |k: VmPageKey|
            s.zone_ids.contains(k.vm.0) && zone_s2_entries(k.vm.0, s.zones[k.vm.0]).contains_key(k),
        |k: VmPageKey| zone_s2_entries(k.vm.0, s.zones[k.vm.0])[k],
    )
}

// ───────────────────────── the abstraction relation R ───────────────────────
impl View for BudgetSpec::State {
    type V = SwView;

    /// R: project the machine state to the abstract `SwView`.  `vm_owned` and
    /// `s2_map` come from the zones; `hypervisor_owned` is the unowned budget;
    /// `shared_pages` is empty (cross-VM sharing is out of scope).
    open spec fn view(&self) -> SwView {
        SwView {
            all_vms: Set::new(|vm: VmId| self.zone_ids.contains(vm.0)),
            hypervisor_owned: hypervisor_pool(self.zones),
            vm_owned: Map::new(
                |vm: VmId| self.zone_ids.contains(vm.0),
                |vm: VmId| zone_owned_pages(self.zones[vm.0]),
            ),
            shared_pages: Set::empty(),
            s2_map: state_s2_map(*self),
        }
    }
}

// ───────────────────────── facts about the projection ───────────────────────
/// A page owned by an active zone is in `all_owned_pages` (membership helper).
pub proof fn lemma_zone_owned_in_all_owned(zones: Map<nat, GhostZone>, zid: nat, p: PhysPage)
    requires
        zones.contains_key(zid),
        zone_owned_pages(zones[zid]).contains(p),
    ensures
        all_owned_pages(zones).contains(p),
{
}

/// A budget region's pages are all budget pages.
pub proof fn lemma_region_pages_in_all_budget(zid: nat, r: MemoryRegion)
    requires
        zone_budget(zid).contains(r),
    ensures
        forall|pp: PhysPage| #[trigger]
            region_pages(r).contains(pp) ==> all_budget_pages().contains(pp),
{
    assert forall|pp: PhysPage| region_pages(r).contains(pp) implies all_budget_pages().contains(
        pp,
    ) by {
        assert(region_owns_page(r, pp));  // witness (zid, r)
    }
}

/// Every stage-2 entry a zone installs targets a page that zone owns
/// (the per-zone half of `SwView::translation_wf`).
pub proof fn lemma_zone_s2_target_owned(zid: nat, gz: GhostZone)
    ensures
        forall|k: VmPageKey| #[trigger]
            zone_s2_entries(zid, gz).contains_key(k) ==> zone_owned_pages(gz).contains(
                zone_s2_entries(zid, gz)[k].page,
            ),
{
    assert forall|k: VmPageKey| #[trigger]
        zone_s2_entries(zid, gz).contains_key(k) implies zone_owned_pages(gz).contains(
        zone_s2_entries(zid, gz)[k].page,
    ) by {
        // The key predicate gives a region owning k.gpa; the value's chosen (r, i)
        // is exactly that witness, and region_phys_page(r, i) is owned via index i.
        let r = choose|r: MemoryRegion| gz.regions().contains(r) && region_owns_gpa(r, k.gpa);
        assert(gz.regions().contains(r) && region_owns_gpa(r, k.gpa));
        let i = choose|i: nat| 0 <= i < r.pages && region_guest_page(r, i) == k.gpa;
        assert(0 <= i < r.pages && region_guest_page(r, i) == k.gpa);
        assert(region_owns_page(r, region_phys_page(r, i)));  // witness i
        assert(zone_owned_pages(gz).contains(region_phys_page(r, i)));  // witness r
    }
}

/// An empty zone owns no pages.
pub proof fn lemma_zone_owned_pages_empty(gz: GhostZone)
    requires
        gz.regions() =~= Set::<MemoryRegion>::empty(),
    ensures
        zone_owned_pages(gz) =~= Set::<PhysPage>::empty(),
{
    assert forall|p: PhysPage| !zone_owned_pages(gz).contains(p) by {
        // membership needs a region in the (empty) region set.
    }
}

/// An empty zone installs no stage-2 entries.
pub proof fn lemma_zone_s2_entries_empty(zid: nat, gz: GhostZone)
    requires
        gz.regions() =~= Set::<MemoryRegion>::empty(),
    ensures
        zone_s2_entries(zid, gz) =~= Map::<VmPageKey, S2Entry>::empty(),
{
    assert forall|k: VmPageKey| !zone_s2_entries(zid, gz).contains_key(k) by {
        // key predicate needs a region in the (empty) region set.
    }
}

} // verus!
