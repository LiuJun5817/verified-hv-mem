use vstd::prelude::*;

use super::{Region, SoftwareView};
use crate::model::types::{GuestPage, PhysPage, S2Entry, VmId, VmPageKey};

verus! {

// ---------------------------------------------------------------------------
// Software-only state transitions
//
// Each `*_step` predicate relates a pre-state `s1` to a post-state `s2`.
// Hardware state is absent; cross-cutting hardware effects are composed in
// `refinement::machine`.
// ---------------------------------------------------------------------------
impl SoftwareView {
    /// Atomically install one CPU mapping and add its physical target to `vm`'s
    /// VM-private projection. The page may already be private to the same VM's
    /// IOMMU, but is absent from every CPU-private and shared projection.
    pub open spec fn map_vm_private_step(
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
            s1.all_vms.contains(v) ==> !s1.vm_owned[v].contains(entry.page))
        &&& !s1.vm_shared.contains(entry.page)
        &&& (forall|v: VmId| #[trigger]
            s1.all_vms.contains(v) && v != vm ==> !s1.iommu_owned[v].contains(entry.page))
        &&& !s1.iommu_shared.contains(entry.page)
        &&& s2.all_vms == s1.all_vms
        &&& s2.vm_owned == s1.vm_owned.insert(vm, s1.vm_owned[vm].insert(entry.page))
        &&& s2.vm_shared == s1.vm_shared
        &&& s2.s2_map == s1.s2_map.insert(key, entry)
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared
    }

    /// Atomically remove one CPU mapping and its physical target from `vm`'s
    /// VM-private projection. No other CPU mapping may target the page.
    pub open spec fn unmap_vm_private_step(
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
        &&& s1.vm_owned[vm].contains(page)
        &&& !s1.vm_shared.contains(page)
        &&& (forall|k: VmPageKey| #[trigger]
            post_map.contains_key(k) ==> post_map[k].page != page)
        &&& s2.all_vms == s1.all_vms
        &&& s2.vm_owned == s1.vm_owned.insert(vm, s1.vm_owned[vm].remove(page))
        &&& s2.vm_shared == s1.vm_shared
        &&& s2.s2_map == post_map
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared
    }

    /// Atomically install one IOMMU mapping and add its target to `vm`'s
    /// VM-private IOMMU projection. The same VM may already map the page on the
    /// CPU side; other VMs and both shared projections may not classify it.
    pub open spec fn iommu_map_vm_private_step(
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
            s1.all_vms.contains(v) ==> !s1.iommu_owned[v].contains(entry.page))
        &&& (forall|v: VmId| #[trigger]
            s1.all_vms.contains(v) && v != vm ==> !s1.vm_owned[v].contains(entry.page))
        &&& !s1.vm_shared.contains(entry.page)
        &&& !s1.iommu_shared.contains(entry.page)
        &&& s2.all_vms == s1.all_vms
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.vm_shared == s1.vm_shared
        &&& s2.s2_map == s1.s2_map
        &&& s2.iommu_owned
            == s1.iommu_owned.insert(vm, s1.iommu_owned[vm].insert(entry.page))
        &&& s2.iommu_shared == s1.iommu_shared
        &&& s2.iommu_s2_map == s1.iommu_s2_map.insert(key, entry)
    }

    /// Atomically remove one IOMMU mapping and its target from `vm`'s
    /// VM-private IOMMU projection. No other IOMMU mapping may target the page.
    pub open spec fn iommu_unmap_vm_private_step(
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
        &&& s1.iommu_owned[vm].contains(page)
        &&& !s1.iommu_shared.contains(page)
        &&& (forall|k: VmPageKey| #[trigger]
            post_map.contains_key(k) ==> post_map[k].page != page)
        &&& s2.all_vms == s1.all_vms
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.vm_shared == s1.vm_shared
        &&& s2.s2_map == s1.s2_map
        &&& s2.iommu_owned
            == s1.iommu_owned.insert(vm, s1.iommu_owned[vm].remove(page))
        &&& s2.iommu_shared == s1.iommu_shared
        &&& s2.iommu_s2_map == post_map
    }

    /// Atomically install one CPU mapping to global-shared memory and add its
    /// target to the dynamic CPU-shared projection. Existing shared aliases are
    /// permitted, while no private projection may contain the target.
    pub open spec fn map_global_shared_step(
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
            s1.all_vms.contains(v) ==> !s1.vm_owned[v].contains(entry.page)
                && !s1.iommu_owned[v].contains(entry.page))
        &&& s2.all_vms == s1.all_vms
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.vm_shared == s1.vm_shared.insert(entry.page)
        &&& s2.s2_map == s1.s2_map.insert(key, entry)
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared
    }

    /// Atomically remove one CPU global-shared mapping. Its physical target
    /// remains CPU-shared exactly when a surviving CPU mapping still aliases it.
    pub open spec fn unmap_global_shared_step(
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
        &&& s1.vm_shared.contains(page)
        &&& s2.all_vms == s1.all_vms
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.vm_shared == if aliased { s1.vm_shared } else { s1.vm_shared.remove(page) }
        &&& s2.s2_map == post_map
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared
    }

    /// Atomically install one IOMMU mapping to global-shared memory and add its
    /// target to the dynamic IOMMU-shared projection.
    pub open spec fn iommu_map_global_shared_step(
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
            s1.all_vms.contains(v) ==> !s1.vm_owned[v].contains(entry.page)
                && !s1.iommu_owned[v].contains(entry.page))
        &&& s2.all_vms == s1.all_vms
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.vm_shared == s1.vm_shared
        &&& s2.s2_map == s1.s2_map
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared.insert(entry.page)
        &&& s2.iommu_s2_map == s1.iommu_s2_map.insert(key, entry)
    }

    /// Atomically remove one IOMMU global-shared mapping. Its target remains
    /// IOMMU-shared exactly when a surviving IOMMU mapping still aliases it.
    pub open spec fn iommu_unmap_global_shared_step(
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
        &&& s1.iommu_shared.contains(page)
        &&& s2.all_vms == s1.all_vms
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.vm_shared == s1.vm_shared
        &&& s2.s2_map == s1.s2_map
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == if aliased {
            s1.iommu_shared
        } else {
            s1.iommu_shared.remove(page)
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
        &&& s2.vm_owned == s1.vm_owned.insert(vm, Set::empty())
        &&& s2.vm_shared == s1.vm_shared
        &&& s2.s2_map
            == s1.s2_map
        // The fresh VM owns nothing for DMA either; `iommu_owned` tracks `all_vms`.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_owned == s1.iommu_owned.insert(vm, Set::empty())
        &&& s2.iommu_shared == s1.iommu_shared
    }

    /// Deregister an empty VM (counterpart of `HvMem::remove_zone`).
    pub open spec fn remove_vm_step(s1: SoftwareView, s2: SoftwareView, vm: VmId) -> bool {
        &&& s2.all_vms == s1.all_vms.remove(vm)
        &&& s2.vm_owned == s1.vm_owned.remove(vm)
        &&& s2.vm_shared == s1.vm_shared
        &&& s2.s2_map
            == s1.s2_map
        // Drop the VM's (empty) DMA ownership; `iommu_owned` tracks `all_vms`.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_owned == s1.iommu_owned.remove(vm)
        &&& s2.iommu_shared == s1.iommu_shared
    }

    /// Install a CPU region drawn from `region.vm`'s zone-private budget.
    pub open spec fn cpu_insert_zone_private_region_step(
        s1: SoftwareView,
        s2: SoftwareView,
        region: Region,
    ) -> bool {
        &&& s2.all_vms == s1.all_vms
        &&& s2.vm_owned == s1.vm_owned.insert(
            region.vm,
            s1.vm_owned[region.vm].union(region.pages()),
        )
        &&& s2.vm_shared == s1.vm_shared
        &&& s2.s2_map == s1.s2_map.union_prefer_right(
            region.entries(),
        )
        // CPU operations leave the IOMMU projection untouched.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared
    }

    /// Remove a CPU region drawn from `region.vm`'s zone-private budget.
    pub open spec fn cpu_remove_zone_private_region_step(
        s1: SoftwareView,
        s2: SoftwareView,
        region: Region,
    ) -> bool {
        &&& s2.all_vms == s1.all_vms
        &&& s2.vm_owned == s1.vm_owned.insert(
            region.vm,
            s1.vm_owned[region.vm].difference(region.pages()),
        )
        &&& s2.vm_shared == s1.vm_shared
        &&& s2.s2_map == s1.s2_map.remove_keys(
            region.entries().dom(),
        )
        // CPU operations leave the IOMMU projection untouched.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared
    }

    /// Install a CPU region drawn from the global-shared budget. Physical aliases
    /// are permitted; `s2_map` records which VMs actually map the shared pages.
    pub open spec fn cpu_insert_global_shared_region_step(
        s1: SoftwareView,
        s2: SoftwareView,
        region: Region,
    ) -> bool {
        &&& s2.all_vms == s1.all_vms
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.vm_shared == s1.vm_shared.union(region.pages())
        &&& s2.s2_map == s1.s2_map.union_prefer_right(region.entries())
        // CPU operations leave the IOMMU projection untouched.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared
    }

    /// Remove a CPU region drawn from the global-shared budget. A physical page
    /// remains in `vm_shared` while any surviving CPU mapping still targets it.
    pub open spec fn cpu_remove_global_shared_region_step(
        s1: SoftwareView,
        s2: SoftwareView,
        region: Region,
    ) -> bool {
        let post_map = s1.s2_map.remove_keys(region.entries().dom());
        &&& s2.all_vms == s1.all_vms
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.vm_shared =~= Set::new(
            |p: PhysPage| {
                &&& s1.vm_shared.contains(p)
                &&& (!region.pages().contains(p) || exists|k: VmPageKey| #[trigger]
                    post_map.contains_key(k) && post_map[k].page == p)
            },
        )
        &&& s2.s2_map == post_map
        // CPU operations leave the IOMMU projection untouched.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared
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

    /// `vm` exists, owns nothing (CPU or DMA), and has no mappings (CPU or IOMMU),
    /// so dropping it strands nothing.
    pub open spec fn remove_vm_enabled(s1: SoftwareView, vm: VmId) -> bool {
        &&& s1.all_vms.contains(vm)
        &&& s1.vm_owned[vm] == Set::<PhysPage>::empty()
        &&& s1.iommu_owned[vm] == Set::<PhysPage>::empty()
        &&& (forall|k: VmPageKey| #[trigger] s1.s2_map.contains_key(k) ==> k.vm != vm)
        &&& (forall|k: VmPageKey| #[trigger] s1.iommu_s2_map.contains_key(k) ==> k.vm != vm)
    }

    /// A zone-private CPU region is insertable when its physical pages have no
    /// existing CPU-private owner, are not shared, and its guest pages are fresh.
    pub open spec fn cpu_insert_zone_private_region_enabled(
        s1: SoftwareView,
        region: Region,
    ) -> bool {
        &&& region.wf()
        &&& s1.all_vms.contains(region.vm)
        &&& (forall|p: PhysPage, v: VmId| #[trigger]
            region.pages().contains(p) && #[trigger] s1.all_vms.contains(v)
                ==> !s1.vm_owned[v].contains(p))
        &&& (forall|p: PhysPage| #[trigger]
            region.pages().contains(p) ==> !s1.vm_shared.contains(p))
        &&& (forall|k: VmPageKey| #[trigger]
            region.entries().contains_key(k) ==> !s1.s2_map.contains_key(
                k,
            ))
        // The same zone may already DMA-map the private page. Other zones may not,
        // and no page may simultaneously belong to the IOMMU-shared projection.
        &&& (forall|p: PhysPage, v1: VmId| #[trigger]
            region.pages().contains(p) && #[trigger] s1.all_vms.contains(v1) && v1 != region.vm
                ==> !s1.iommu_owned[v1].contains(p))
        &&& (forall|p: PhysPage| #[trigger]
            region.pages().contains(p) ==> !s1.iommu_shared.contains(p))
    }

    /// A zone-private CPU region is removable when it is installed and no other
    /// CPU mapping targets its physical pages.
    pub open spec fn cpu_remove_zone_private_region_enabled(
        s1: SoftwareView,
        region: Region,
    ) -> bool {
        &&& region.wf()
        &&& s1.all_vms.contains(region.vm)
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
        &&& (forall|p: PhysPage| #[trigger]
            region.pages().contains(p) ==> !s1.vm_shared.contains(p))
    }

    /// A global-shared CPU region is insertable at fresh guest pages. Its physical
    /// pages may already have other shared CPU or IOMMU mappings, but may not be
    /// classified as private in either translation domain.
    pub open spec fn cpu_insert_global_shared_region_enabled(
        s1: SoftwareView,
        region: Region,
    ) -> bool {
        &&& region.wf()
        &&& s1.all_vms.contains(region.vm)
        &&& (forall|k: VmPageKey| #[trigger]
            region.entries().contains_key(k) ==> !s1.s2_map.contains_key(k))
        &&& (forall|p: PhysPage, v: VmId| #[trigger]
            region.pages().contains(p) && #[trigger] s1.all_vms.contains(v)
                ==> !s1.vm_owned[v].contains(p) && !s1.iommu_owned[v].contains(p))
    }

    /// A global-shared CPU region is removable when its exact entries are installed.
    /// Other physical aliases are permitted and keep their pages in `vm_shared`.
    pub open spec fn cpu_remove_global_shared_region_enabled(
        s1: SoftwareView,
        region: Region,
    ) -> bool {
        &&& region.wf()
        &&& s1.all_vms.contains(region.vm)
        &&& (forall|p: PhysPage| #[trigger]
            region.pages().contains(p) ==> s1.vm_shared.contains(p))
        &&& (forall|k: VmPageKey| #[trigger]
            region.entries().contains_key(k) ==> s1.s2_map.contains_key(k)
                && s1.s2_map[k] == region.entries()[k])
    }

    // -----------------------------------------------------------------------
    // IOMMU region operations
    // -----------------------------------------------------------------------
    /// Install an IOMMU region drawn from `region.vm`'s zone-private budget.
    pub open spec fn iommu_insert_zone_private_region_step(
        s1: SoftwareView,
        s2: SoftwareView,
        region: Region,
    ) -> bool {
        &&& s2.all_vms == s1.all_vms
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.vm_shared == s1.vm_shared
        &&& s2.s2_map == s1.s2_map
        &&& s2.iommu_shared == s1.iommu_shared
        &&& s2.iommu_owned == s1.iommu_owned.insert(
            region.vm,
            s1.iommu_owned[region.vm].union(region.pages()),
        )
        &&& s2.iommu_s2_map == s1.iommu_s2_map.union_prefer_right(region.entries())
    }

    /// Remove an IOMMU region drawn from `region.vm`'s zone-private budget.
    pub open spec fn iommu_remove_zone_private_region_step(
        s1: SoftwareView,
        s2: SoftwareView,
        region: Region,
    ) -> bool {
        &&& s2.all_vms == s1.all_vms
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.vm_shared == s1.vm_shared
        &&& s2.s2_map == s1.s2_map
        &&& s2.iommu_shared == s1.iommu_shared
        &&& s2.iommu_owned == s1.iommu_owned.insert(
            region.vm,
            s1.iommu_owned[region.vm].difference(region.pages()),
        )
        &&& s2.iommu_s2_map == s1.iommu_s2_map.remove_keys(region.entries().dom())
    }

    /// Install an IOMMU region drawn from the global-shared budget. Physical aliases
    /// are permitted independently of the CPU shared mappings.
    pub open spec fn iommu_insert_global_shared_region_step(
        s1: SoftwareView,
        s2: SoftwareView,
        region: Region,
    ) -> bool {
        &&& s2.all_vms == s1.all_vms
        // IOMMU operations leave the CPU projection untouched.
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.vm_shared == s1.vm_shared
        &&& s2.s2_map == s1.s2_map
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared.union(region.pages())
        &&& s2.iommu_s2_map == s1.iommu_s2_map.union_prefer_right(region.entries())
    }

    /// Remove an IOMMU region drawn from the global-shared budget. A physical page
    /// remains in `iommu_shared` while any surviving IOMMU mapping still targets it.
    pub open spec fn iommu_remove_global_shared_region_step(
        s1: SoftwareView,
        s2: SoftwareView,
        region: Region,
    ) -> bool {
        let post_map = s1.iommu_s2_map.remove_keys(region.entries().dom());
        &&& s2.all_vms == s1.all_vms
        // IOMMU operations leave the CPU projection untouched.
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.vm_shared == s1.vm_shared
        &&& s2.s2_map == s1.s2_map
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared =~= Set::new(
            |p: PhysPage| {
                &&& s1.iommu_shared.contains(p)
                &&& (!region.pages().contains(p) || exists|k: VmPageKey| #[trigger]
                    post_map.contains_key(k) && post_map[k].page == p)
            },
        )
        &&& s2.iommu_s2_map == post_map
    }

    /// A zone-private IOMMU region is insertable when its physical pages have no
    /// existing IOMMU-private owner, are not shared, and its guest pages are fresh.
    pub open spec fn iommu_insert_zone_private_region_enabled(
        s1: SoftwareView,
        region: Region,
    ) -> bool {
        &&& region.wf()
        &&& s1.all_vms.contains(region.vm)
        &&& (forall|k: VmPageKey| #[trigger]
            region.entries().contains_key(k) ==> !s1.iommu_s2_map.contains_key(k))
        &&& (forall|p: PhysPage, v: VmId| #[trigger]
            region.pages().contains(p) && #[trigger] s1.all_vms.contains(v)
                ==> !s1.iommu_owned[v].contains(p))
        // The same zone may already CPU-map the private page; other zones may not.
        &&& (forall|p: PhysPage, v: VmId| #[trigger]
            region.pages().contains(p) && #[trigger] s1.all_vms.contains(v) && v != region.vm
                ==> !s1.vm_owned[v].contains(p))
        &&& (forall|p: PhysPage| #[trigger]
            region.pages().contains(p) ==> !s1.vm_shared.contains(p)
                && !s1.iommu_shared.contains(p))
    }

    /// A zone-private IOMMU region is removable when it is installed and no other
    /// IOMMU mapping targets its physical pages.
    pub open spec fn iommu_remove_zone_private_region_enabled(
        s1: SoftwareView,
        region: Region,
    ) -> bool {
        &&& region.wf()
        &&& s1.all_vms.contains(region.vm)
        &&& (forall|p: PhysPage| #[trigger]
            region.pages().contains(p) ==> s1.iommu_owned[region.vm].contains(p))
        &&& (forall|k: VmPageKey| #[trigger]
            region.entries().contains_key(k) ==> s1.iommu_s2_map.contains_key(k)
                && s1.iommu_s2_map[k] == region.entries()[k])
        &&& (forall|k: VmPageKey| #[trigger]
            s1.iommu_s2_map.contains_key(k) && !region.entries().contains_key(k)
                ==> !region.pages().contains(s1.iommu_s2_map[k].page))
    }

    /// A global-shared IOMMU region is insertable at fresh guest pages. Its physical
    /// pages may already have shared CPU or IOMMU mappings, but may not be classified
    /// as private in either translation domain.
    pub open spec fn iommu_insert_global_shared_region_enabled(
        s1: SoftwareView,
        region: Region,
    ) -> bool {
        &&& region.wf()
        &&& s1.all_vms.contains(region.vm)
        &&& (forall|k: VmPageKey| #[trigger]
            region.entries().contains_key(k) ==> !s1.iommu_s2_map.contains_key(k))
        &&& (forall|p: PhysPage, v: VmId| #[trigger]
            region.pages().contains(p) && #[trigger] s1.all_vms.contains(v)
                ==> !s1.vm_owned[v].contains(p) && !s1.iommu_owned[v].contains(p))
    }

    /// A global-shared IOMMU region is removable when its exact entries are installed.
    /// Other physical aliases are permitted and keep their pages in `iommu_shared`.
    pub open spec fn iommu_remove_global_shared_region_enabled(
        s1: SoftwareView,
        region: Region,
    ) -> bool {
        &&& region.wf()
        &&& s1.all_vms.contains(region.vm)
        &&& (forall|p: PhysPage| #[trigger]
            region.pages().contains(p) ==> s1.iommu_shared.contains(p))
        &&& (forall|k: VmPageKey| #[trigger]
            region.entries().contains_key(k) ==> s1.iommu_s2_map.contains_key(k)
                && s1.iommu_s2_map[k] == region.entries()[k])
    }
}

} // verus!
