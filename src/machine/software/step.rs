use vstd::prelude::*;

use super::{Region, SoftwareView};
use crate::machine::types::*;

verus! {

// ---------------------------------------------------------------------------
// Software-only state transitions
//
// Each `*_step` predicate relates a pre-state `s1` to a post-state `s2`.
// Hardware state is absent; cross-cutting hardware effects are composed in
// `refinement::machine`.
// ---------------------------------------------------------------------------
impl SoftwareView {
    /// Install (or replace) the stage-2 mapping for `(vm, gpa)`.
    pub open spec fn map_step(
        s1: SoftwareView,
        s2: SoftwareView,
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
        // A CPU stage-2 edit leaves the IOMMU contexts untouched.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared
    }

    /// Remove the stage-2 mapping for `(vm, gpa)`.
    pub open spec fn unmap_step(
        s1: SoftwareView,
        s2: SoftwareView,
        vm: VmId,
        gpa: GuestPage,
    ) -> bool {
        let key = VmPageKey::new(vm, gpa);
        &&& s1.s2_map.contains_key(key)
        &&& s2.all_vms == s1.all_vms
        &&& s2.hypervisor_owned == s1.hypervisor_owned
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.shared_pages == s1.shared_pages
        &&& s2.s2_map == s1.s2_map.remove(key)
        // A CPU stage-2 edit leaves the IOMMU contexts untouched.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared
    }

    /// Install (or replace) the **IOMMU** stage-2 mapping for `(vm, gpa)` — the DMA
    /// counterpart of [`map_step`](Self::map_step).  Requires the target page to be one
    /// `vm` may DMA: a **private** DMA page (`iommu_owned`) or a **shared** page
    /// (`iommu_shared`, the GIC), confining a device's translation; the CPU state and
    /// the other VMs' IOMMU ownership are untouched, so it preserves `iommu_wf` outright
    /// (no cross-VM coupling — see `super::proof`).
    pub open spec fn iommu_map_step(
        s1: SoftwareView,
        s2: SoftwareView,
        vm: VmId,
        gpa: GuestPage,
        entry: S2Entry,
    ) -> bool {
        let key = VmPageKey::new(vm, gpa);
        &&& s1.all_vms.contains(vm)
        &&& s1.iommu_owned.contains_key(vm)
        &&& (s1.iommu_owned[vm].contains(entry.page) || s1.iommu_shared.contains(entry.page))
        &&& s2.all_vms == s1.all_vms
        &&& s2.hypervisor_owned == s1.hypervisor_owned
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.shared_pages == s1.shared_pages
        &&& s2.s2_map == s1.s2_map
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared
        &&& s2.iommu_s2_map == s1.iommu_s2_map.insert(key, entry)
    }

    /// Remove the **IOMMU** stage-2 mapping for `(vm, gpa)` — the DMA counterpart of
    /// [`unmap_step`](Self::unmap_step).  Leaves `iommu_owned` (the page stays
    /// DMA-owned until reclaimed) and all CPU state untouched.
    pub open spec fn iommu_unmap_step(
        s1: SoftwareView,
        s2: SoftwareView,
        vm: VmId,
        gpa: GuestPage,
    ) -> bool {
        let key = VmPageKey::new(vm, gpa);
        &&& s1.iommu_s2_map.contains_key(key)
        &&& s2.all_vms == s1.all_vms
        &&& s2.hypervisor_owned == s1.hypervisor_owned
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.shared_pages == s1.shared_pages
        &&& s2.s2_map == s1.s2_map
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared
        &&& s2.iommu_s2_map == s1.iommu_s2_map.remove(key)
    }

    /// Transfer `page` from the hypervisor pool to `vm`.
    pub open spec fn assign_page_step(
        s1: SoftwareView,
        s2: SoftwareView,
        vm: VmId,
        page: PhysPage,
    ) -> bool {
        &&& s1.all_vms.contains(vm)
        &&& s1.hypervisor_owned.contains(page)
        // IOMMU-aware guard: the page handed to `vm`'s CPU ownership must not be another
        // VM's private DMA page (else `iommu_ownership_wf` clause (2) would break).
        &&& forall|v1: VmId| #[trigger]
            s1.all_vms.contains(v1) && v1 != vm ==> !s1.iommu_owned[v1].contains(page)
        &&& s2.all_vms == s1.all_vms
        &&& s2.hypervisor_owned == s1.hypervisor_owned.remove(page)
        &&& s2.vm_owned == s1.vm_owned.insert(vm, s1.vm_owned[vm].insert(page))
        &&& s2.shared_pages == s1.shared_pages
        &&& s2.s2_map == s1.s2_map
        // Ownership transfer on the CPU side leaves the IOMMU contexts untouched.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared
    }

    /// Reclaim `page` from `vm` back to the hypervisor pool.
    pub open spec fn reclaim_page_step(
        s1: SoftwareView,
        s2: SoftwareView,
        vm: VmId,
        page: PhysPage,
    ) -> bool {
        &&& s1.all_vms.contains(vm)
        &&& s1.vm_owned.contains_key(vm) && s1.vm_owned[vm].contains(page)
        &&& s2.all_vms == s1.all_vms
        &&& s2.hypervisor_owned == s1.hypervisor_owned.insert(page)
        &&& s2.vm_owned == s1.vm_owned.insert(vm, s1.vm_owned[vm].remove(page))
        &&& s2.shared_pages == s1.shared_pages
        &&& s2.s2_map == s1.s2_map
        // Ownership transfer on the CPU side leaves the IOMMU contexts untouched.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared
    }

    /// Establish a symmetric sharing edge for `page` between `left` and `right`.
    pub open spec fn share_page_step(
        s1: SoftwareView,
        s2: SoftwareView,
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
        // CPU sharing does not touch the IOMMU contexts.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared
    }

    /// Remove the symmetric sharing edge for `page` between `left` and `right`.
    pub open spec fn unshare_page_step(
        s1: SoftwareView,
        s2: SoftwareView,
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
        // CPU sharing does not touch the IOMMU contexts.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared
    }

    // -----------------------------------------------------------------------
    // Region and VM-lifecycle steps  (the 4 `SoftwareRefinement` operations)
    //
    // Region steps are set/map algebra (the observable effect); their
    // decomposition into per-page steps is in `super::proof`.
    // -----------------------------------------------------------------------
    /// Register a fresh, empty VM (counterpart of `HvMem::add_zone`).
    pub open spec fn add_vm_step(s1: SoftwareView, s2: SoftwareView, vm: VmId) -> bool {
        &&& s2.all_vms == s1.all_vms.insert(vm)
        &&& s2.hypervisor_owned == s1.hypervisor_owned
        &&& s2.vm_owned == s1.vm_owned.insert(vm, Set::empty())
        &&& s2.shared_pages == s1.shared_pages
        &&& s2.s2_map == s1.s2_map
        // The fresh VM owns nothing for DMA either; `iommu_owned` tracks `all_vms`.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_owned == s1.iommu_owned.insert(vm, Set::empty())
        &&& s2.iommu_shared == s1.iommu_shared
    }

    /// Deregister an empty VM (counterpart of `HvMem::remove_zone`).
    pub open spec fn remove_vm_step(s1: SoftwareView, s2: SoftwareView, vm: VmId) -> bool {
        &&& s2.all_vms == s1.all_vms.remove(vm)
        &&& s2.hypervisor_owned == s1.hypervisor_owned
        &&& s2.vm_owned == s1.vm_owned.remove(vm)
        &&& s2.shared_pages == s1.shared_pages
        &&& s2.s2_map == s1.s2_map
        // Drop the VM's (empty) DMA ownership; `iommu_owned` tracks `all_vms`.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_owned == s1.iommu_owned.remove(vm)
        &&& s2.iommu_shared == s1.iommu_shared
    }

    /// Bulk assign + map a whole `region` (counterpart of `HvMem::insert_region`).
    pub open spec fn insert_region_step(
        s1: SoftwareView,
        s2: SoftwareView,
        region: Region,
    ) -> bool {
        &&& s2.all_vms == s1.all_vms
        &&& s2.hypervisor_owned == s1.hypervisor_owned.difference(region.pages())
        &&& s2.vm_owned == s1.vm_owned.insert(
            region.vm,
            s1.vm_owned[region.vm].union(region.pages()),
        )
        &&& s2.shared_pages == s1.shared_pages
        &&& s2.s2_map == s1.s2_map.union_prefer_right(region.entries())
        // A CPU region insert leaves the IOMMU contexts untouched.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared
    }

    /// Bulk unmap + reclaim a whole `region` (counterpart of `HvMem::remove_region`).
    pub open spec fn remove_region_step(
        s1: SoftwareView,
        s2: SoftwareView,
        region: Region,
    ) -> bool {
        &&& s2.all_vms == s1.all_vms
        &&& s2.hypervisor_owned == s1.hypervisor_owned.union(region.pages())
        &&& s2.vm_owned == s1.vm_owned.insert(
            region.vm,
            s1.vm_owned[region.vm].difference(region.pages()),
        )
        &&& s2.shared_pages == s1.shared_pages
        &&& s2.s2_map == s1.s2_map.remove_keys(region.entries().dom())
        // A CPU region remove leaves the IOMMU contexts untouched.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared
    }

    // -----------------------------------------------------------------------
    // Enabling preconditions for the 4 operations
    //
    // Closed (owned by the trusted model), so an implementation cannot weaken
    // them.  Each is the precondition under which the matching step preserves
    // `wf` (see `super::proof`).
    // -----------------------------------------------------------------------
    /// `vm` is fresh.
    pub open spec fn add_vm_enabled(s1: SoftwareView, vm: VmId) -> bool {
        !s1.all_vms.contains(vm)
    }

    /// `vm` exists, owns nothing (CPU *or* DMA), has no mappings (CPU *or* IOMMU), and is
    /// in no sharing edge — so dropping it strands nothing.
    pub open spec fn remove_vm_enabled(s1: SoftwareView, vm: VmId) -> bool {
        &&& s1.all_vms.contains(vm)
        &&& s1.vm_owned[vm] == Set::<PhysPage>::empty()
        &&& s1.iommu_owned[vm] == Set::<PhysPage>::empty()
        &&& (forall|k: VmPageKey| #[trigger] s1.s2_map.contains_key(k) ==> k.vm != vm)
        &&& (forall|k: VmPageKey| #[trigger] s1.iommu_s2_map.contains_key(k) ==> k.vm != vm)
        &&& (forall|e: SharedPage| #[trigger]
            s1.shared_pages.contains(e) ==> e.left != vm && e.right != vm)
    }

    /// `region` is an assignable unit for its VM in this state, its pages are free
    /// (in the hypervisor pool), and its guest pages are not yet mapped.
    pub open spec fn insert_region_enabled(s1: SoftwareView, region: Region) -> bool {
        &&& region.wf()
        &&& s1.all_vms.contains(region.vm)
        &&& s1.is_region_assignable(region)
        &&& (forall|p: PhysPage| #[trigger]
            region.pages().contains(p) ==> s1.hypervisor_owned.contains(p))
        &&& (forall|k: VmPageKey| #[trigger]
            region.entries().contains_key(k) ==> !s1.s2_map.contains_key(k))
        // IOMMU-aware guard: none of the region's pages is another VM's private DMA page
        // (else assigning them to `region.vm`'s CPU ownership breaks `iommu_ownership_wf`
        // clause (2)).  Discharged in the refinement from zone-region disjointness.
        &&& (forall|p: PhysPage, v1: VmId| #[trigger] region.pages().contains(p) && #[trigger]
            s1.all_vms.contains(v1) && v1 != region.vm ==> !s1.iommu_owned[v1].contains(p))
    }

    /// `region` is an assignable unit for its VM, is currently installed, *no
    /// other* mapping targets its pages, and its pages are in no sharing edge (so
    /// reclaiming them strands neither a dangling translation nor a borrower).
    /// `is_region_assignable` identifies `region` as a whole unit.
    pub open spec fn remove_region_enabled(s1: SoftwareView, region: Region) -> bool {
        &&& region.wf()
        &&& s1.all_vms.contains(region.vm)
        &&& s1.is_region_assignable(region)
        &&& (forall|p: PhysPage| #[trigger]
            region.pages().contains(p) ==> s1.vm_owned[region.vm].contains(p))
        &&& (forall|k: VmPageKey| #[trigger]
            region.entries().contains_key(k) ==> s1.s2_map.contains_key(k) && s1.s2_map[k]
                == region.entries()[k])
        &&& (forall|k: VmPageKey| #[trigger]
            s1.s2_map.contains_key(k) && !region.entries().contains_key(k)
                ==> !region.pages().contains(
                s1.s2_map[k].page,
            ))
        // Region pages are unshared: reclaiming a shared page would strand a borrower
        // (the analogue of the no-dangling clause above, for sharing edges).
        &&& (forall|e: SharedPage| #[trigger]
            s1.shared_pages.contains(e) ==> !region.pages().contains(e.page))
    }
}

} // verus!
