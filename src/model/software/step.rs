use vstd::prelude::*;

use super::{Region, SoftwareView};
use crate::model::types::{GuestPage, PhysPage, S2Entry, VmId, VmPageKey};

verus! {

/// Policy-neutral software operations produced by a concrete memory-policy
/// refinement. Region operations retain their policy-independent private/shared
/// classification; their decomposition into per-page machine actions belongs to
/// the SW+HW refinement layer.
#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub enum SoftwareOp {
    AddVm(VmId),
    RemoveVm(VmId),
    CpuInsertPrivateRegion(Region),
    CpuRemovePrivateRegion(Region),
    CpuInsertSharedRegion(Region),
    CpuRemoveSharedRegion(Region),
    IommuInsertPrivateRegion(Region),
    IommuRemovePrivateRegion(Region),
    IommuInsertSharedRegion(Region),
    IommuRemoveSharedRegion(Region),
}

// ---------------------------------------------------------------------------
// Software-only state transitions
//
// Each `*_step` predicate relates a pre-state `s1` to a post-state `s2`.
// Hardware state is absent; cross-cutting hardware effects are composed in
// `refinement::machine`.
// ---------------------------------------------------------------------------
impl SoftwareView {
    /// Atomically install one CPU mapping and add its physical target to `vm`'s
    /// S2-Private projection. The page may already be IOMMU-Private for the same
    /// VM, but is absent from every S2-Private and Shared projection.
    pub open spec fn map_s2_private_step(
        s1: SoftwareView,
        s2: SoftwareView,
        vm: VmId,
        gpa: GuestPage,
        entry: S2Entry,
    ) -> bool {
        let key = VmPageKey::new(vm, gpa);
        &&& s1.all_vms.contains(vm)
        &&& !s1.s2_map.contains_key(key)
        &&& (forall|v: VmId| #[trigger]
            s1.all_vms.contains(v) ==> !s1.s2_private_pages[v].contains(entry.page))
        &&& !s1.s2_shared_pages.contains(entry.page)
        &&& (forall|v: VmId| #[trigger]
            s1.all_vms.contains(v) && v != vm ==> !s1.iommu_private_pages[v].contains(entry.page))
        &&& !s1.iommu_shared_pages.contains(entry.page)
        &&& s2.all_vms == s1.all_vms
        &&& s2.s2_private_pages == s1.s2_private_pages.insert(vm, s1.s2_private_pages[vm].insert(entry.page))
        &&& s2.s2_shared_pages == s1.s2_shared_pages
        &&& s2.s2_map == s1.s2_map.insert(key, entry)
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_private_pages == s1.iommu_private_pages
        &&& s2.iommu_shared_pages == s1.iommu_shared_pages
    }

    /// Atomically remove one CPU mapping and its physical target from `vm`'s
    /// S2-Private projection. No other CPU mapping may target the page.
    pub open spec fn unmap_s2_private_step(
        s1: SoftwareView,
        s2: SoftwareView,
        vm: VmId,
        gpa: GuestPage,
        page: PhysPage,
    ) -> bool {
        let key = VmPageKey::new(vm, gpa);
        let post_map = s1.s2_map.remove(key);
        &&& s1.all_vms.contains(vm)
        &&& s1.s2_map.contains_key(key)
        &&& s1.s2_map[key].page == page
        &&& s1.s2_private_pages[vm].contains(page)
        &&& !s1.s2_shared_pages.contains(page)
        &&& (forall|k: VmPageKey| #[trigger]
            post_map.contains_key(k) ==> post_map[k].page != page)
        &&& s2.all_vms == s1.all_vms
        &&& s2.s2_private_pages == s1.s2_private_pages.insert(vm, s1.s2_private_pages[vm].remove(page))
        &&& s2.s2_shared_pages == s1.s2_shared_pages
        &&& s2.s2_map == post_map
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_private_pages == s1.iommu_private_pages
        &&& s2.iommu_shared_pages == s1.iommu_shared_pages
    }

    /// Atomically install one IOMMU mapping and add its target to `vm`'s
    /// IOMMU-Private projection. The same VM may already map the page on the CPU
    /// side, and the page may be S2-Shared; other VMs and the IOMMU-Shared
    /// projection may not classify it.
    pub open spec fn map_iommu_private_step(
        s1: SoftwareView,
        s2: SoftwareView,
        vm: VmId,
        gpa: GuestPage,
        entry: S2Entry,
    ) -> bool {
        let key = VmPageKey::new(vm, gpa);
        &&& s1.all_vms.contains(vm)
        &&& !s1.iommu_s2_map.contains_key(key)
        &&& (forall|v: VmId| #[trigger]
            s1.all_vms.contains(v) ==> !s1.iommu_private_pages[v].contains(entry.page))
        &&& (forall|v: VmId| #[trigger]
            s1.all_vms.contains(v) && v != vm ==> !s1.s2_private_pages[v].contains(entry.page))
        &&& !s1.iommu_shared_pages.contains(entry.page)
        &&& s2.all_vms == s1.all_vms
        &&& s2.s2_private_pages == s1.s2_private_pages
        &&& s2.s2_shared_pages == s1.s2_shared_pages
        &&& s2.s2_map == s1.s2_map
        &&& s2.iommu_private_pages
            == s1.iommu_private_pages.insert(vm, s1.iommu_private_pages[vm].insert(entry.page))
        &&& s2.iommu_shared_pages == s1.iommu_shared_pages
        &&& s2.iommu_s2_map == s1.iommu_s2_map.insert(key, entry)
    }

    /// Atomically remove one IOMMU mapping and its target from `vm`'s
    /// IOMMU-Private projection. No other IOMMU mapping may target the page.
    pub open spec fn unmap_iommu_private_step(
        s1: SoftwareView,
        s2: SoftwareView,
        vm: VmId,
        gpa: GuestPage,
        page: PhysPage,
    ) -> bool {
        let key = VmPageKey::new(vm, gpa);
        let post_map = s1.iommu_s2_map.remove(key);
        &&& s1.all_vms.contains(vm)
        &&& s1.iommu_s2_map.contains_key(key)
        &&& s1.iommu_s2_map[key].page == page
        &&& s1.iommu_private_pages[vm].contains(page)
        &&& !s1.iommu_shared_pages.contains(page)
        &&& (forall|k: VmPageKey| #[trigger]
            post_map.contains_key(k) ==> post_map[k].page != page)
        &&& s2.all_vms == s1.all_vms
        &&& s2.s2_private_pages == s1.s2_private_pages
        &&& s2.s2_shared_pages == s1.s2_shared_pages
        &&& s2.s2_map == s1.s2_map
        &&& s2.iommu_private_pages
            == s1.iommu_private_pages.insert(vm, s1.iommu_private_pages[vm].remove(page))
        &&& s2.iommu_shared_pages == s1.iommu_shared_pages
        &&& s2.iommu_s2_map == post_map
    }

    /// Atomically install one CPU mapping to shared memory and add its
    /// target to the dynamic S2-Shared projection. Existing shared aliases and
    /// IOMMU-Private classifications are permitted, while no S2-Private projection may
    /// contain the target.
    pub open spec fn map_s2_shared_step(
        s1: SoftwareView,
        s2: SoftwareView,
        vm: VmId,
        gpa: GuestPage,
        entry: S2Entry,
    ) -> bool {
        let key = VmPageKey::new(vm, gpa);
        &&& s1.all_vms.contains(vm)
        &&& !s1.s2_map.contains_key(key)
        &&& (forall|v: VmId| #[trigger]
            s1.all_vms.contains(v) ==> !s1.s2_private_pages[v].contains(entry.page))
        &&& s2.all_vms == s1.all_vms
        &&& s2.s2_private_pages == s1.s2_private_pages
        &&& s2.s2_shared_pages == s1.s2_shared_pages.insert(entry.page)
        &&& s2.s2_map == s1.s2_map.insert(key, entry)
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_private_pages == s1.iommu_private_pages
        &&& s2.iommu_shared_pages == s1.iommu_shared_pages
    }

    /// Atomically remove one CPU shared mapping. Its physical target
    /// remains S2-Shared exactly when a surviving CPU mapping still aliases it.
    pub open spec fn unmap_s2_shared_step(
        s1: SoftwareView,
        s2: SoftwareView,
        vm: VmId,
        gpa: GuestPage,
    ) -> bool {
        let key = VmPageKey::new(vm, gpa);
        let page = s1.s2_map[key].page;
        let post_map = s1.s2_map.remove(key);
        let aliased = exists|k: VmPageKey| #[trigger]
            post_map.contains_key(k) && post_map[k].page == page;
        &&& s1.all_vms.contains(vm)
        &&& s1.s2_map.contains_key(key)
        &&& s1.s2_shared_pages.contains(page)
        &&& s2.all_vms == s1.all_vms
        &&& s2.s2_private_pages == s1.s2_private_pages
        &&& s2.s2_shared_pages == if aliased { s1.s2_shared_pages } else { s1.s2_shared_pages.remove(page) }
        &&& s2.s2_map == post_map
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_private_pages == s1.iommu_private_pages
        &&& s2.iommu_shared_pages == s1.iommu_shared_pages
    }

    /// Atomically install one IOMMU mapping to shared memory and add its
    /// target to the dynamic IOMMU-Shared projection.
    pub open spec fn map_iommu_shared_step(
        s1: SoftwareView,
        s2: SoftwareView,
        vm: VmId,
        gpa: GuestPage,
        entry: S2Entry,
    ) -> bool {
        let key = VmPageKey::new(vm, gpa);
        &&& s1.all_vms.contains(vm)
        &&& !s1.iommu_s2_map.contains_key(key)
        &&& (forall|v: VmId| #[trigger]
            s1.all_vms.contains(v) ==> !s1.s2_private_pages[v].contains(entry.page)
                && !s1.iommu_private_pages[v].contains(entry.page))
        &&& s2.all_vms == s1.all_vms
        &&& s2.s2_private_pages == s1.s2_private_pages
        &&& s2.s2_shared_pages == s1.s2_shared_pages
        &&& s2.s2_map == s1.s2_map
        &&& s2.iommu_private_pages == s1.iommu_private_pages
        &&& s2.iommu_shared_pages == s1.iommu_shared_pages.insert(entry.page)
        &&& s2.iommu_s2_map == s1.iommu_s2_map.insert(key, entry)
    }

    /// Atomically remove one IOMMU shared mapping. Its target remains
    /// IOMMU-Shared exactly when a surviving IOMMU mapping still aliases it.
    pub open spec fn unmap_iommu_shared_step(
        s1: SoftwareView,
        s2: SoftwareView,
        vm: VmId,
        gpa: GuestPage,
    ) -> bool {
        let key = VmPageKey::new(vm, gpa);
        let page = s1.iommu_s2_map[key].page;
        let post_map = s1.iommu_s2_map.remove(key);
        let aliased = exists|k: VmPageKey| #[trigger]
            post_map.contains_key(k) && post_map[k].page == page;
        &&& s1.all_vms.contains(vm)
        &&& s1.iommu_s2_map.contains_key(key)
        &&& s1.iommu_shared_pages.contains(page)
        &&& s2.all_vms == s1.all_vms
        &&& s2.s2_private_pages == s1.s2_private_pages
        &&& s2.s2_shared_pages == s1.s2_shared_pages
        &&& s2.s2_map == s1.s2_map
        &&& s2.iommu_private_pages == s1.iommu_private_pages
        &&& s2.iommu_shared_pages == if aliased {
            s1.iommu_shared_pages
        } else {
            s1.iommu_shared_pages.remove(page)
        }
        &&& s2.iommu_s2_map == post_map
    }

    // -----------------------------------------------------------------------
    // Region and VM-lifecycle steps
    //
    // Region steps are set/map algebra (the observable effect); their
    // decomposition into per-page steps is in `super::proof`.
    // -----------------------------------------------------------------------
    /// Register a fresh, empty VM (counterpart of `HvMem::add_zone`).
    pub open spec fn add_vm_step(s1: SoftwareView, s2: SoftwareView, vm: VmId) -> bool {
        &&& s2.all_vms == s1.all_vms.insert(vm)
        &&& s2.s2_private_pages == s1.s2_private_pages.insert(vm, Set::empty())
        &&& s2.s2_shared_pages == s1.s2_shared_pages
        &&& s2.s2_map
            == s1.s2_map
        // The fresh VM has no IOMMU-Private pages; the map tracks `all_vms`.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_private_pages == s1.iommu_private_pages.insert(vm, Set::empty())
        &&& s2.iommu_shared_pages == s1.iommu_shared_pages
    }

    /// Deregister an empty VM (counterpart of `HvMem::remove_zone`).
    pub open spec fn remove_vm_step(s1: SoftwareView, s2: SoftwareView, vm: VmId) -> bool {
        &&& s2.all_vms == s1.all_vms.remove(vm)
        &&& s2.s2_private_pages == s1.s2_private_pages.remove(vm)
        &&& s2.s2_shared_pages == s1.s2_shared_pages
        &&& s2.s2_map
            == s1.s2_map
        // Drop the VM's empty IOMMU-Private entry; the map tracks `all_vms`.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_private_pages == s1.iommu_private_pages.remove(vm)
        &&& s2.iommu_shared_pages == s1.iommu_shared_pages
    }

    /// Apply the dynamic effect of installing an S2-Private region for
    /// `region.vm`.
    pub open spec fn cpu_insert_private_region_step(
        s1: SoftwareView,
        s2: SoftwareView,
        region: Region,
    ) -> bool {
        &&& s2.all_vms == s1.all_vms
        &&& s2.s2_private_pages == s1.s2_private_pages.insert(
            region.vm,
            s1.s2_private_pages[region.vm].union(region.pages()),
        )
        &&& s2.s2_shared_pages == s1.s2_shared_pages
        &&& s2.s2_map == s1.s2_map.union_prefer_right(
            region.entries(),
        )
        // CPU operations leave the IOMMU projection untouched.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_private_pages == s1.iommu_private_pages
        &&& s2.iommu_shared_pages == s1.iommu_shared_pages
    }

    /// Apply the dynamic effect of removing an S2-Private region for
    /// `region.vm`.
    pub open spec fn cpu_remove_private_region_step(
        s1: SoftwareView,
        s2: SoftwareView,
        region: Region,
    ) -> bool {
        &&& s2.all_vms == s1.all_vms
        &&& s2.s2_private_pages == s1.s2_private_pages.insert(
            region.vm,
            s1.s2_private_pages[region.vm].difference(region.pages()),
        )
        &&& s2.s2_shared_pages == s1.s2_shared_pages
        &&& s2.s2_map == s1.s2_map.remove_keys(
            region.entries().dom(),
        )
        // CPU operations leave the IOMMU projection untouched.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_private_pages == s1.iommu_private_pages
        &&& s2.iommu_shared_pages == s1.iommu_shared_pages
    }

    /// Apply the dynamic effect of installing an S2-Shared region. Physical
    /// aliases are permitted; `s2_map` records which VMs actually map the
    /// shared pages.
    pub open spec fn cpu_insert_shared_region_step(
        s1: SoftwareView,
        s2: SoftwareView,
        region: Region,
    ) -> bool {
        &&& s2.all_vms == s1.all_vms
        &&& s2.s2_private_pages == s1.s2_private_pages
        &&& s2.s2_shared_pages == s1.s2_shared_pages.union(region.pages())
        &&& s2.s2_map == s1.s2_map.union_prefer_right(region.entries())
        // CPU operations leave the IOMMU projection untouched.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_private_pages == s1.iommu_private_pages
        &&& s2.iommu_shared_pages == s1.iommu_shared_pages
    }

    /// Apply the dynamic effect of removing an S2-Shared region. A physical
    /// page remains in `s2_shared_pages` while any surviving CPU mapping still
    /// targets it.
    pub open spec fn cpu_remove_shared_region_step(
        s1: SoftwareView,
        s2: SoftwareView,
        region: Region,
    ) -> bool {
        let post_map = s1.s2_map.remove_keys(region.entries().dom());
        &&& s2.all_vms == s1.all_vms
        &&& s2.s2_private_pages == s1.s2_private_pages
        &&& s2.s2_shared_pages =~= Set::new(
            |p: PhysPage| {
                &&& s1.s2_shared_pages.contains(p)
                &&& (!region.pages().contains(p) || exists|k: VmPageKey| #[trigger]
                    post_map.contains_key(k) && post_map[k].page == p)
            },
        )
        &&& s2.s2_map == post_map
        // CPU operations leave the IOMMU projection untouched.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_private_pages == s1.iommu_private_pages
        &&& s2.iommu_shared_pages == s1.iommu_shared_pages
    }

    // -----------------------------------------------------------------------
    // Enabling preconditions for the region operations
    //
    // Closed (owned by the trusted model), so an implementation cannot weaken
    // them.  Each is the precondition under which the matching step preserves
    // `wf` (see `super::proof`).
    // -----------------------------------------------------------------------
    /// `vm` is fresh.
    pub open spec fn add_vm_enabled(s1: SoftwareView, vm: VmId) -> bool {
        !s1.all_vms.contains(vm)
    }

    /// `vm` exists, has no Private pages, and has no CPU or IOMMU mappings,
    /// so dropping it strands nothing.
    pub open spec fn remove_vm_enabled(s1: SoftwareView, vm: VmId) -> bool {
        &&& s1.all_vms.contains(vm)
        &&& s1.s2_private_pages[vm] == Set::<PhysPage>::empty()
        &&& s1.iommu_private_pages[vm] == Set::<PhysPage>::empty()
        &&& (forall|k: VmPageKey| #[trigger] s1.s2_map.contains_key(k) ==> k.vm != vm)
        &&& (forall|k: VmPageKey| #[trigger] s1.iommu_s2_map.contains_key(k) ==> k.vm != vm)
    }

    /// An S2-Private region is insertable when its physical pages have no
    /// existing S2-Private classification, are not S2-Shared, and its guest
    /// pages are fresh.
    pub open spec fn cpu_insert_private_region_enabled(
        s1: SoftwareView,
        region: Region,
    ) -> bool {
        &&& region.wf()
        &&& s1.all_vms.contains(region.vm)
        &&& (forall|p: PhysPage, v: VmId| #[trigger]
            region.pages().contains(p) && #[trigger] s1.all_vms.contains(v)
                ==> !s1.s2_private_pages[v].contains(p))
        &&& (forall|p: PhysPage| #[trigger]
            region.pages().contains(p) ==> !s1.s2_shared_pages.contains(p))
        &&& (forall|k: VmPageKey| #[trigger]
            region.entries().contains_key(k) ==> !s1.s2_map.contains_key(
                k,
            ))
        // The same VM may already DMA-map the Private page. Other VMs may not,
        // and no page may simultaneously belong to the IOMMU-Shared projection.
        &&& (forall|p: PhysPage, v1: VmId| #[trigger]
            region.pages().contains(p) && #[trigger] s1.all_vms.contains(v1) && v1 != region.vm
                ==> !s1.iommu_private_pages[v1].contains(p))
        &&& (forall|p: PhysPage| #[trigger]
            region.pages().contains(p) ==> !s1.iommu_shared_pages.contains(p))
    }

    /// A private CPU region is removable when it is installed and no other
    /// CPU mapping targets its physical pages.
    pub open spec fn cpu_remove_private_region_enabled(
        s1: SoftwareView,
        region: Region,
    ) -> bool {
        &&& region.wf()
        &&& s1.all_vms.contains(region.vm)
        &&& (forall|p: PhysPage| #[trigger]
            region.pages().contains(p) ==> s1.s2_private_pages[region.vm].contains(p))
        &&& (forall|k: VmPageKey| #[trigger]
            region.entries().contains_key(k) ==> s1.s2_map.contains_key(k) && s1.s2_map[k]
                == region.entries()[k])
        &&& (forall|k: VmPageKey| #[trigger]
            s1.s2_map.contains_key(k) && !region.entries().contains_key(k)
                ==> !region.pages().contains(
                s1.s2_map[k].page,
            ))
        &&& (forall|p: PhysPage| #[trigger]
            region.pages().contains(p) ==> !s1.s2_shared_pages.contains(p))
    }

    /// A shared CPU region is insertable at fresh guest pages. Its physical
    /// pages may already have other shared CPU mappings or IOMMU-Private/shared
    /// mappings, but cannot be S2-Private.
    pub open spec fn cpu_insert_shared_region_enabled(
        s1: SoftwareView,
        region: Region,
    ) -> bool {
        &&& region.wf()
        &&& s1.all_vms.contains(region.vm)
        &&& (forall|k: VmPageKey| #[trigger]
            region.entries().contains_key(k) ==> !s1.s2_map.contains_key(k))
        &&& (forall|p: PhysPage, v: VmId| #[trigger]
            region.pages().contains(p) && #[trigger] s1.all_vms.contains(v)
                ==> !s1.s2_private_pages[v].contains(p))
    }

    /// A shared CPU region is removable when its exact entries are installed.
    /// Other physical aliases are permitted and keep their pages in `s2_shared_pages`.
    pub open spec fn cpu_remove_shared_region_enabled(
        s1: SoftwareView,
        region: Region,
    ) -> bool {
        &&& region.wf()
        &&& s1.all_vms.contains(region.vm)
        &&& (forall|p: PhysPage| #[trigger]
            region.pages().contains(p) ==> s1.s2_shared_pages.contains(p))
        &&& (forall|k: VmPageKey| #[trigger]
            region.entries().contains_key(k) ==> s1.s2_map.contains_key(k)
                && s1.s2_map[k] == region.entries()[k])
    }

    // -----------------------------------------------------------------------
    // IOMMU region operations
    // -----------------------------------------------------------------------
    /// Apply the dynamic effect of installing an IOMMU-Private region for
    /// `region.vm`.
    pub open spec fn iommu_insert_private_region_step(
        s1: SoftwareView,
        s2: SoftwareView,
        region: Region,
    ) -> bool {
        &&& s2.all_vms == s1.all_vms
        &&& s2.s2_private_pages == s1.s2_private_pages
        &&& s2.s2_shared_pages == s1.s2_shared_pages
        &&& s2.s2_map == s1.s2_map
        &&& s2.iommu_shared_pages == s1.iommu_shared_pages
        &&& s2.iommu_private_pages == s1.iommu_private_pages.insert(
            region.vm,
            s1.iommu_private_pages[region.vm].union(region.pages()),
        )
        &&& s2.iommu_s2_map == s1.iommu_s2_map.union_prefer_right(region.entries())
    }

    /// Apply the dynamic effect of removing an IOMMU-Private region for
    /// `region.vm`.
    pub open spec fn iommu_remove_private_region_step(
        s1: SoftwareView,
        s2: SoftwareView,
        region: Region,
    ) -> bool {
        &&& s2.all_vms == s1.all_vms
        &&& s2.s2_private_pages == s1.s2_private_pages
        &&& s2.s2_shared_pages == s1.s2_shared_pages
        &&& s2.s2_map == s1.s2_map
        &&& s2.iommu_shared_pages == s1.iommu_shared_pages
        &&& s2.iommu_private_pages == s1.iommu_private_pages.insert(
            region.vm,
            s1.iommu_private_pages[region.vm].difference(region.pages()),
        )
        &&& s2.iommu_s2_map == s1.iommu_s2_map.remove_keys(region.entries().dom())
    }

    /// Apply the dynamic effect of installing an IOMMU-Shared region. Physical
    /// aliases are permitted independently of the CPU Shared mappings.
    pub open spec fn iommu_insert_shared_region_step(
        s1: SoftwareView,
        s2: SoftwareView,
        region: Region,
    ) -> bool {
        &&& s2.all_vms == s1.all_vms
        // IOMMU operations leave the CPU projection untouched.
        &&& s2.s2_private_pages == s1.s2_private_pages
        &&& s2.s2_shared_pages == s1.s2_shared_pages
        &&& s2.s2_map == s1.s2_map
        &&& s2.iommu_private_pages == s1.iommu_private_pages
        &&& s2.iommu_shared_pages == s1.iommu_shared_pages.union(region.pages())
        &&& s2.iommu_s2_map == s1.iommu_s2_map.union_prefer_right(region.entries())
    }

    /// Apply the dynamic effect of removing an IOMMU-Shared region. A physical
    /// page remains in `iommu_shared_pages` while any surviving IOMMU mapping
    /// still targets it.
    pub open spec fn iommu_remove_shared_region_step(
        s1: SoftwareView,
        s2: SoftwareView,
        region: Region,
    ) -> bool {
        let post_map = s1.iommu_s2_map.remove_keys(region.entries().dom());
        &&& s2.all_vms == s1.all_vms
        // IOMMU operations leave the CPU projection untouched.
        &&& s2.s2_private_pages == s1.s2_private_pages
        &&& s2.s2_shared_pages == s1.s2_shared_pages
        &&& s2.s2_map == s1.s2_map
        &&& s2.iommu_private_pages == s1.iommu_private_pages
        &&& s2.iommu_shared_pages =~= Set::new(
            |p: PhysPage| {
                &&& s1.iommu_shared_pages.contains(p)
                &&& (!region.pages().contains(p) || exists|k: VmPageKey| #[trigger]
                    post_map.contains_key(k) && post_map[k].page == p)
            },
        )
        &&& s2.iommu_s2_map == post_map
    }

    /// An IOMMU-Private region is insertable when its physical pages have no
    /// existing IOMMU-Private classification, are not IOMMU-Shared, and its
    /// guest pages are fresh. S2-Shared access is independent and is permitted.
    pub open spec fn iommu_insert_private_region_enabled(
        s1: SoftwareView,
        region: Region,
    ) -> bool {
        &&& region.wf()
        &&& s1.all_vms.contains(region.vm)
        &&& (forall|k: VmPageKey| #[trigger]
            region.entries().contains_key(k) ==> !s1.iommu_s2_map.contains_key(k))
        &&& (forall|p: PhysPage, v: VmId| #[trigger]
            region.pages().contains(p) && #[trigger] s1.all_vms.contains(v)
                ==> !s1.iommu_private_pages[v].contains(p))
        // The same VM may already CPU-map the Private page; other VMs may not.
        &&& (forall|p: PhysPage, v: VmId| #[trigger]
            region.pages().contains(p) && #[trigger] s1.all_vms.contains(v) && v != region.vm
                ==> !s1.s2_private_pages[v].contains(p))
        &&& (forall|p: PhysPage| #[trigger]
            region.pages().contains(p) ==> !s1.iommu_shared_pages.contains(p))
    }

    /// A private IOMMU region is removable when it is installed and no other
    /// IOMMU mapping targets its physical pages.
    pub open spec fn iommu_remove_private_region_enabled(
        s1: SoftwareView,
        region: Region,
    ) -> bool {
        &&& region.wf()
        &&& s1.all_vms.contains(region.vm)
        &&& (forall|p: PhysPage| #[trigger]
            region.pages().contains(p) ==> s1.iommu_private_pages[region.vm].contains(p))
        &&& (forall|k: VmPageKey| #[trigger]
            region.entries().contains_key(k) ==> s1.iommu_s2_map.contains_key(k)
                && s1.iommu_s2_map[k] == region.entries()[k])
        &&& (forall|k: VmPageKey| #[trigger]
            s1.iommu_s2_map.contains_key(k) && !region.entries().contains_key(k)
                ==> !region.pages().contains(s1.iommu_s2_map[k].page))
    }

    /// A shared IOMMU region is insertable at fresh guest pages. Its physical
    /// pages may already have shared CPU or IOMMU mappings, but may not be classified
    /// as private in either translation domain.
    pub open spec fn iommu_insert_shared_region_enabled(
        s1: SoftwareView,
        region: Region,
    ) -> bool {
        &&& region.wf()
        &&& s1.all_vms.contains(region.vm)
        &&& (forall|k: VmPageKey| #[trigger]
            region.entries().contains_key(k) ==> !s1.iommu_s2_map.contains_key(k))
        &&& (forall|p: PhysPage, v: VmId| #[trigger]
            region.pages().contains(p) && #[trigger] s1.all_vms.contains(v)
                ==> !s1.s2_private_pages[v].contains(p) && !s1.iommu_private_pages[v].contains(p))
    }

    /// A shared IOMMU region is removable when its exact entries are installed.
    /// Other physical aliases are permitted and keep their pages in `iommu_shared_pages`.
    pub open spec fn iommu_remove_shared_region_enabled(
        s1: SoftwareView,
        region: Region,
    ) -> bool {
        &&& region.wf()
        &&& s1.all_vms.contains(region.vm)
        &&& (forall|p: PhysPage| #[trigger]
            region.pages().contains(p) ==> s1.iommu_shared_pages.contains(p))
        &&& (forall|k: VmPageKey| #[trigger]
            region.entries().contains_key(k) ==> s1.iommu_s2_map.contains_key(k)
                && s1.iommu_s2_map[k] == region.entries()[k])
    }

    /// Dispatch one policy-neutral software operation. Enabledness is part of
    /// the relation so a refinement trace carries every premise needed by the
    /// view-level SW+HW composition proof.
    pub open spec fn step(s1: Self, s2: Self, op: SoftwareOp) -> bool {
        match op {
            SoftwareOp::AddVm(vm) => {
                Self::add_vm_enabled(s1, vm) && Self::add_vm_step(s1, s2, vm)
            },
            SoftwareOp::RemoveVm(vm) => {
                Self::remove_vm_enabled(s1, vm) && Self::remove_vm_step(s1, s2, vm)
            },
            SoftwareOp::CpuInsertPrivateRegion(region) => {
                Self::cpu_insert_private_region_enabled(s1, region)
                    && Self::cpu_insert_private_region_step(s1, s2, region)
            },
            SoftwareOp::CpuRemovePrivateRegion(region) => {
                Self::cpu_remove_private_region_enabled(s1, region)
                    && Self::cpu_remove_private_region_step(s1, s2, region)
            },
            SoftwareOp::CpuInsertSharedRegion(region) => {
                Self::cpu_insert_shared_region_enabled(s1, region)
                    && Self::cpu_insert_shared_region_step(s1, s2, region)
            },
            SoftwareOp::CpuRemoveSharedRegion(region) => {
                Self::cpu_remove_shared_region_enabled(s1, region)
                    && Self::cpu_remove_shared_region_step(s1, s2, region)
            },
            SoftwareOp::IommuInsertPrivateRegion(region) => {
                Self::iommu_insert_private_region_enabled(s1, region)
                    && Self::iommu_insert_private_region_step(s1, s2, region)
            },
            SoftwareOp::IommuRemovePrivateRegion(region) => {
                Self::iommu_remove_private_region_enabled(s1, region)
                    && Self::iommu_remove_private_region_step(s1, s2, region)
            },
            SoftwareOp::IommuInsertSharedRegion(region) => {
                Self::iommu_insert_shared_region_enabled(s1, region)
                    && Self::iommu_insert_shared_region_step(s1, s2, region)
            },
            SoftwareOp::IommuRemoveSharedRegion(region) => {
                Self::iommu_remove_shared_region_enabled(s1, region)
                    && Self::iommu_remove_shared_region_step(s1, s2, region)
            },
        }
    }

    /// Execute a finite sequence of policy-neutral software operations.
    pub open spec fn run_ops(start: Self, end: Self, ops: Seq<SoftwareOp>) -> bool
        decreases ops.len(),
    {
        if ops.len() == 0 {
            start == end
        } else {
            exists|next: Self|
                Self::step(start, next, ops[0])
                    && Self::run_ops(next, end, ops.skip(1))
        }
    }
}

/// Policy-neutral software execution relation used by every concrete memory
/// policy refinement.
pub open spec fn run_software_ops(
    start: SoftwareView,
    end: SoftwareView,
    ops: Seq<SoftwareOp>,
) -> bool {
    SoftwareView::run_ops(start, end, ops)
}

} // verus!
