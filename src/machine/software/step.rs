use vstd::prelude::*;

use super::SwView;
use crate::machine::types::*;

verus! {

// ---------------------------------------------------------------------------
// Software-only state transitions
//
// Each `*_step` predicate relates two `SwView` snapshots.  `s1` is the
// pre-state; `s2` is the post-state.  Hardware state (`HwView`) is
// intentionally absent; cross-cutting effects (e.g., updating
// `pending_invalidations` after a map/unmap) are handled separately in
// `hardware::step` and composed in `machine::machine::refine`.
// ---------------------------------------------------------------------------
impl SwView {
    /// Install (or replace) the stage-2 mapping for `(vm, gpa)`.
    ///
    /// Preconditions are embedded: `vm` must be in `all_vms`, and `entry.page`
    /// must be owned or shared by `vm` in `s1`.
    pub open spec fn map_step(
        s1: SwView,
        s2: SwView,
        vm: VmId,
        gpa: GuestPage,
        entry: S2Entry,
    ) -> bool {
        let key = VmPageKey::new(vm, gpa);
        &&& s1.all_vms.contains(vm)
        &&& s1.owned_or_shared(vm, entry.page)
        &&& s2.all_vms == s1.all_vms
        &&& s2.hypervisor_owned == s1.hypervisor_owned
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.shared_pages == s1.shared_pages
        &&& s2.s2_map == s1.s2_map.insert(key, entry)
    }

    /// Remove the stage-2 mapping for `(vm, gpa)`.
    pub open spec fn unmap_step(s1: SwView, s2: SwView, vm: VmId, gpa: GuestPage) -> bool {
        let key = VmPageKey::new(vm, gpa);
        &&& s1.s2_map.contains_key(key)
        &&& s2.all_vms == s1.all_vms
        &&& s2.hypervisor_owned == s1.hypervisor_owned
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.shared_pages == s1.shared_pages
        &&& s2.s2_map == s1.s2_map.remove(key)
    }

    /// Transfer `page` from the hypervisor pool to `vm`.
    pub open spec fn assign_page_step(s1: SwView, s2: SwView, vm: VmId, page: PhysPage) -> bool {
        &&& s1.all_vms.contains(vm)
        &&& s1.hypervisor_owned.contains(page)
        &&& s2.all_vms == s1.all_vms
        &&& s2.hypervisor_owned == s1.hypervisor_owned.remove(page)
        &&& s2.vm_owned == s1.vm_owned.insert(vm, s1.vm_owned[vm].insert(page))
        &&& s2.shared_pages == s1.shared_pages
        &&& s2.s2_map == s1.s2_map
    }

    /// Reclaim `page` from `vm` back to the hypervisor pool.
    ///
    /// `page` must be quiescent (no mappings, no sharing) — enforced at the
    /// machine level before calling this step.
    pub open spec fn reclaim_page_step(s1: SwView, s2: SwView, vm: VmId, page: PhysPage) -> bool {
        &&& s1.all_vms.contains(vm)
        &&& s1.vm_owned.contains_key(vm) && s1.vm_owned[vm].contains(page)
        &&& s2.all_vms == s1.all_vms
        &&& s2.hypervisor_owned == s1.hypervisor_owned.insert(page)
        &&& s2.vm_owned == s1.vm_owned.insert(vm, s1.vm_owned[vm].remove(page))
        &&& s2.shared_pages == s1.shared_pages
        &&& s2.s2_map == s1.s2_map
    }

    /// Establish a symmetric sharing edge for `page` between `left` and `right`.
    pub open spec fn share_page_step(
        s1: SwView,
        s2: SwView,
        left: VmId,
        right: VmId,
        page: PhysPage,
    ) -> bool {
        let edge = SharedPage { left, right, page };
        &&& left != right
        &&& s1.all_vms.contains(left) && s1.all_vms.contains(right)
        &&& s1.vm_owned.contains_key(left) && s1.vm_owned[left].contains(page)
        &&& s2.all_vms == s1.all_vms
        &&& s2.hypervisor_owned == s1.hypervisor_owned
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.s2_map == s1.s2_map
        &&& s2.shared_pages == s1.shared_pages.insert(edge).insert(edge.reverse())
    }

    /// Remove the symmetric sharing edge for `page` between `left` and `right`.
    pub open spec fn unshare_page_step(
        s1: SwView,
        s2: SwView,
        left: VmId,
        right: VmId,
        page: PhysPage,
    ) -> bool {
        let edge = SharedPage { left, right, page };
        &&& s1.shared_pages.contains(edge) && s1.shared_pages.contains(edge.reverse())
        &&& s2.all_vms == s1.all_vms
        &&& s2.hypervisor_owned == s1.hypervisor_owned
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.s2_map == s1.s2_map
        &&& s2.shared_pages == s1.shared_pages.remove(edge).remove(edge.reverse())
    }

    // -----------------------------------------------------------------------
    // Region-bulk and VM-lifecycle steps
    //
    // These are the operations the hypervisor actually realizes (region-bulk,
    // ownership = inserted regions; cf. `crate::refinement`).  Each region step
    // is the finite composition of the per-page steps above.
    // -----------------------------------------------------------------------
    /// Register a fresh, empty VM (counterpart of `HvMem::add_zone`).
    pub open spec fn add_vm_step(s1: SwView, s2: SwView, vm: VmId) -> bool {
        &&& !s1.all_vms.contains(vm)
        &&& s2.all_vms == s1.all_vms.insert(vm)
        &&& s2.hypervisor_owned == s1.hypervisor_owned
        &&& s2.vm_owned == s1.vm_owned.insert(vm, Set::empty())
        &&& s2.shared_pages == s1.shared_pages
        &&& s2.s2_map == s1.s2_map
    }

    /// Deregister an empty VM (counterpart of `HvMem::remove_zone`).
    pub open spec fn remove_vm_step(s1: SwView, s2: SwView, vm: VmId) -> bool {
        &&& s1.all_vms.contains(vm)
        &&& s1.vm_owned[vm] == Set::<PhysPage>::empty()
        &&& (forall|k: VmPageKey| #[trigger] s1.s2_map.contains_key(k) ==> k.vm != vm)
        &&& s2.all_vms == s1.all_vms.remove(vm)
        &&& s2.hypervisor_owned == s1.hypervisor_owned
        &&& s2.vm_owned == s1.vm_owned.remove(vm)
        &&& s2.shared_pages == s1.shared_pages
        &&& s2.s2_map == s1.s2_map
    }

    /// Bulk assign + map a region's pages to `vm` (counterpart of
    /// `HvMem::insert_region`).  `pages` are the physical pages moved from the
    /// hypervisor pool; `entries` are the installed stage-2 entries.
    pub open spec fn insert_region_step(
        s1: SwView,
        s2: SwView,
        vm: VmId,
        pages: Set<PhysPage>,
        entries: Map<VmPageKey, S2Entry>,
    ) -> bool {
        &&& s1.all_vms.contains(vm)
        &&& (forall|p: PhysPage| #[trigger] pages.contains(p) ==> s1.hypervisor_owned.contains(p))
        &&& (forall|k: VmPageKey| #[trigger] entries.contains_key(k) ==> k.vm == vm)
        &&& s2.all_vms == s1.all_vms
        &&& s2.hypervisor_owned == s1.hypervisor_owned.difference(pages)
        &&& s2.vm_owned == s1.vm_owned.insert(vm, s1.vm_owned[vm].union(pages))
        &&& s2.shared_pages == s1.shared_pages
        &&& s2.s2_map == s1.s2_map.union_prefer_right(entries)
    }

    /// Bulk unmap + reclaim a region's pages from `vm` (counterpart of
    /// `HvMem::remove_region`).
    pub open spec fn remove_region_step(
        s1: SwView,
        s2: SwView,
        vm: VmId,
        pages: Set<PhysPage>,
        keys: Set<VmPageKey>,
    ) -> bool {
        &&& s1.all_vms.contains(vm)
        &&& (forall|p: PhysPage| #[trigger] pages.contains(p) ==> s1.vm_owned[vm].contains(p))
        &&& (forall|k: VmPageKey| #[trigger] keys.contains(k) ==> k.vm == vm)
        &&& s2.all_vms == s1.all_vms
        &&& s2.hypervisor_owned == s1.hypervisor_owned.union(pages)
        &&& s2.vm_owned == s1.vm_owned.insert(vm, s1.vm_owned[vm].difference(pages))
        &&& s2.shared_pages == s1.shared_pages
        &&& s2.s2_map == s1.s2_map.remove_keys(keys)
    }
}

} // verus!
