use vstd::prelude::*;

use super::Region;
use crate::model::types::{PhysPage, S2Entry, VmId, VmPageKey};

verus! {

/// The software-controlled portion of the machine state.
///
/// All fields are derived from the hypervisor's data structures (zone list,
/// stage-2 page tables, and policy state). Private means protected by the
/// corresponding isolation theorem; Shared means explicitly outside that
/// Private guarantee. Neither classification creates access without an
/// installed translation.
pub ghost struct SoftwareView {
    /// Set of all VM identifiers currently managed by the hypervisor.
    pub all_vms: Set<VmId>,
    /// Per-VM pages currently classified S2-Private.
    pub s2_private_pages: Map<VmId, Set<PhysPage>>,
    /// Pages currently classified S2-Shared. This is a dynamic projection of
    /// installed mappings, not a static eligibility budget or a claim that
    /// every VM can access each page.
    pub s2_shared_pages: Set<PhysPage>,
    /// Per-VM pages currently classified IOMMU-Private. This is independent of
    /// `s2_private_pages`: a VM may IOMMU-map a Private page it has not CPU-mapped,
    /// and vice versa.
    pub iommu_private_pages: Map<VmId, Set<PhysPage>>,
    /// Pages currently classified IOMMU-Shared. CPU and IOMMU classifications
    /// are independent, so neither Shared projection need contain the other.
    pub iommu_shared_pages: Set<PhysPage>,
    /// Stage-2 page-table mappings installed by the hypervisor.
    pub s2_map: Map<VmPageKey, S2Entry>,
    /// IOMMU (SMMU) stage-2 mappings — a second stage-2 context per VM, for
    /// device DMA. A mapping target is classified either IOMMU-Private for its
    /// VM or IOMMU-Shared.
    pub iommu_s2_map: Map<VmPageKey, S2Entry>,
}

impl SoftwareView {
    /// `page` has an S2 classification compatible with a mapping by `vm`.
    /// The stage-2 map, not this predicate, records actual access.
    pub open spec fn s2_private_or_shared(&self, vm: VmId, page: PhysPage) -> bool {
        (self.s2_private_pages.contains_key(vm) && self.s2_private_pages[vm].contains(page))
            || self.s2_shared_pages.contains(page)
    }

    /// Per-VM S2-Private projections cover exactly `all_vms`, are pairwise
    /// disjoint, and do not overlap S2-Shared pages.
    pub open spec fn s2_classification_wf(&self) -> bool {
        &&& self.s2_private_pages.dom() == self.all_vms
        &&& forall|vm1: VmId, vm2: VmId| #[trigger]
            self.all_vms.contains(vm1) && #[trigger] self.all_vms.contains(vm2) && vm1 != vm2
                ==> forall|page: PhysPage| #[trigger]
                self.s2_private_pages[vm1].contains(page) ==> !self.s2_private_pages[vm2].contains(page)
        &&& forall|vm: VmId| #[trigger]
            self.all_vms.contains(vm) ==> forall|page: PhysPage| #[trigger]
                self.s2_private_pages[vm].contains(page) ==> !self.s2_shared_pages.contains(page)
    }

    /// Every stage-2 mapping targets a page classified S2-Private for the mapped
    /// VM or S2-Shared.
    pub open spec fn translation_wf(&self) -> bool {
        forall|key: VmPageKey| #[trigger]
            self.s2_map.contains_key(key) ==> {
                &&& self.all_vms.contains(key.vm)
                &&& self.s2_private_or_shared(key.vm, self.s2_map[key].page)
            }
    }

    /// IOMMU classification separation. Private S2/IOMMU pages are disjoint
    /// across VMs. IOMMU-Private pages are disjoint from IOMMU-Shared pages, but
    /// may also be S2-Shared because the classifications describe independent
    /// access paths. A VM may CPU-map and IOMMU-map the same Private page.
    pub open spec fn iommu_classification_wf(&self) -> bool {
        &&& self.iommu_private_pages.dom()
            == self.all_vms
        // (1) Private DMA pages are pairwise cross-VM disjoint.
        &&& forall|vm1: VmId, vm2: VmId| #[trigger]
            self.all_vms.contains(vm1) && #[trigger] self.all_vms.contains(vm2) && vm1 != vm2
                ==> forall|page: PhysPage| #[trigger]
                self.iommu_private_pages[vm1].contains(page) ==> !self.iommu_private_pages[vm2].contains(
                    page,
                )
                // (2) A VM's IOMMU-Private pages are never another VM's S2-Private pages.
        &&& forall|vm1: VmId, vm2: VmId| #[trigger]
            self.all_vms.contains(vm1) && #[trigger] self.all_vms.contains(vm2) && vm1 != vm2
                ==> forall|page: PhysPage| #[trigger]
                self.iommu_private_pages[vm1].contains(page) ==> !self.s2_private_pages[vm2].contains(
                    page,
                )
                // (3) IOMMU-Private pages are disjoint from IOMMU-Shared pages.
        &&& forall|vm: VmId| #[trigger]
            self.all_vms.contains(vm) ==> forall|page: PhysPage| #[trigger]
                self.iommu_private_pages[vm].contains(page) ==> !self.iommu_shared_pages.contains(page)
                // (4) S2-Private pages are disjoint from IOMMU-Shared pages.
        &&& forall|vm: VmId| #[trigger]
            self.all_vms.contains(vm) ==> forall|page: PhysPage| #[trigger]
                self.s2_private_pages[vm].contains(page) ==> !self.iommu_shared_pages.contains(page)
    }

    /// Every IOMMU stage-2 mapping targets a page classified IOMMU-Private for
    /// the mapped VM or IOMMU-Shared.
    pub open spec fn iommu_translation_wf(&self) -> bool {
        forall|key: VmPageKey| #[trigger]
            self.iommu_s2_map.contains_key(key) ==> {
                &&& self.all_vms.contains(key.vm)
                &&& self.iommu_private_pages.contains_key(key.vm)
                &&& (self.iommu_private_pages[key.vm].contains(self.iommu_s2_map[key].page)
                    || self.iommu_shared_pages.contains(self.iommu_s2_map[key].page))
            }
    }

    /// Combined IOMMU well-formedness. A VM may legitimately CPU-map and
    /// DMA-map the same Private page, so there is deliberately no same-VM
    /// `iommu_private_pages ∩ s2_private_pages = ∅` clause.
    pub open spec fn iommu_wf(&self) -> bool {
        &&& self.iommu_classification_wf()
        &&& self.iommu_translation_wf()
    }

    /// Combined software well-formedness invariant.
    pub open spec fn wf(&self) -> bool {
        &&& self.s2_classification_wf()
        &&& self.translation_wf()
        &&& self.iommu_wf()
    }
}

} // verus!
