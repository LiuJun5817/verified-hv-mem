use vstd::prelude::*;

use super::Region;
use crate::model::types::{PhysPage, S2Entry, VmId, VmPageKey};

verus! {

/// The software-controlled portion of the machine state.
///
/// All fields are derived from the hypervisor's data structures (zone list,
/// stage-2 page tables, page allocator).  An exec type implementing
/// `View<V = SoftwareView>` provides a spec-level mapping from its concrete fields.
pub ghost struct SoftwareView {
    /// Set of all VM identifiers currently managed by the hypervisor.
    pub all_vms: Set<VmId>,
    /// Physical pages held by the hypervisor (not assigned to any VM).
    pub hypervisor_owned: Set<PhysPage>,
    /// Per-VM CPU-mapped pages drawn from the zone's private budget.
    pub vm_owned: Map<VmId, Set<PhysPage>>,
    /// Physical pages currently targeted by at least one CPU mapping and drawn
    /// from the global-shared budget.  This is a dynamic projection of installed
    /// mappings, not the static global-shared budget itself.
    pub vm_shared: Set<PhysPage>,
    /// Per-VM IOMMU-mapped pages drawn from the zone's private budget. Kept
    /// separate from `vm_owned`: a VM may IOMMU-map a private page it has not
    /// CPU-mapped, and vice versa.
    pub iommu_owned: Map<VmId, Set<PhysPage>>,
    /// Physical pages currently targeted by at least one IOMMU mapping and drawn
    /// from the global-shared budget. `iommu_shared` and `vm_shared` are separate
    /// dynamic subsets of that budget; neither need contain the other.
    pub iommu_shared: Set<PhysPage>,
    /// Stage-2 page-table mappings installed by the hypervisor.
    pub s2_map: Map<VmPageKey, S2Entry>,
    /// IOMMU (SMMU) stage-2 mappings — a second stage-2 context per VM, for
    /// device DMA. A VM's IOMMU may map its private pages (`iommu_owned`) or
    /// global-shared pages (`iommu_shared`).
    pub iommu_s2_map: Map<VmPageKey, S2Entry>,
}

impl SoftwareView {
    /// Whether `region` is a unit assignable to its VM *in this state*.
    /// Uninterpreted at the machine level — an implementation characterizes it (via
    /// its region budget, a runtime check, …) with a refinement axiom (see
    /// `crate::refinement::software::axiom_assignable_from_budget`).  Being
    /// state-dependent, the machine model makes no region-budget assumption of its own.
    pub uninterp spec fn is_region_assignable(self, region: Region) -> bool;

    /// `page` is accessible to `vm` either because it is CPU-mapped private
    /// memory of `vm` or because it is currently mapped global-shared memory.
    pub open spec fn owned_or_shared(&self, vm: VmId, page: PhysPage) -> bool {
        (self.vm_owned.contains_key(vm) && self.vm_owned[vm].contains(page))
            || self.vm_shared.contains(page)
    }
    
    /// Per-VM private ownership sets cover exactly `all_vms`, are pairwise
    /// disjoint, and do not overlap the hypervisor pool or CPU-shared pages.
    pub open spec fn ownership_wf(&self) -> bool {
        &&& self.vm_owned.dom() == self.all_vms
        &&& forall|vm1: VmId, vm2: VmId| #[trigger]
            self.all_vms.contains(vm1) && #[trigger] self.all_vms.contains(vm2) && vm1 != vm2
                ==> forall|page: PhysPage| #[trigger]
                self.vm_owned[vm1].contains(page) ==> !self.vm_owned[vm2].contains(page)
        &&& forall|vm: VmId| #[trigger]
            self.all_vms.contains(vm) ==> forall|page: PhysPage| #[trigger]
                self.vm_owned[vm].contains(page) ==> !self.hypervisor_owned.contains(page)
        &&& forall|vm: VmId| #[trigger]
            self.all_vms.contains(vm) ==> forall|page: PhysPage| #[trigger]
                self.vm_owned[vm].contains(page) ==> !self.vm_shared.contains(page)
        &&& forall|page: PhysPage| #[trigger]
            self.vm_shared.contains(page) ==> !self.hypervisor_owned.contains(page)
    }

    /// Every stage-2 mapping targets a page owned or shared by the mapped VM.
    pub open spec fn translation_wf(&self) -> bool {
        forall|key: VmPageKey| #[trigger]
            self.s2_map.contains_key(key) ==> {
                &&& self.all_vms.contains(key.vm)
                &&& self.owned_or_shared(key.vm, self.s2_map[key].page)
            }
    }

    /// IOMMU ownership separation. Private CPU/IOMMU pages are disjoint across
    /// zones and from both dynamic shared sets. A VM may CPU-map and IOMMU-map
    /// the same page from its own private budget.
    pub open spec fn iommu_ownership_wf(&self) -> bool {
        &&& self.iommu_owned.dom()
            == self.all_vms
        // (1) Private DMA pages are pairwise cross-VM disjoint.
        &&& forall|vm1: VmId, vm2: VmId| #[trigger]
            self.all_vms.contains(vm1) && #[trigger] self.all_vms.contains(vm2) && vm1 != vm2
                ==> forall|page: PhysPage| #[trigger]
                self.iommu_owned[vm1].contains(page) ==> !self.iommu_owned[vm2].contains(
                    page,
                )
                // (2) A VM's private DMA pages are never another VM's CPU-owned pages.
        &&& forall|vm1: VmId, vm2: VmId| #[trigger]
            self.all_vms.contains(vm1) && #[trigger] self.all_vms.contains(vm2) && vm1 != vm2
                ==> forall|page: PhysPage| #[trigger]
                self.iommu_owned[vm1].contains(page) ==> !self.vm_owned[vm2].contains(
                    page,
                )
                // (3) Private DMA pages are disjoint from both shared projections.
        &&& forall|vm: VmId| #[trigger]
            self.all_vms.contains(vm) ==> forall|page: PhysPage| #[trigger]
                self.iommu_owned[vm].contains(page) ==> !self.iommu_shared.contains(
                    page,
                )
                    && !self.vm_shared.contains(page)
                // (4) CPU-private pages are disjoint from IOMMU-shared pages.
        &&& forall|vm: VmId| #[trigger]
            self.all_vms.contains(vm) ==> forall|page: PhysPage| #[trigger]
                self.vm_owned[vm].contains(page) ==> !self.iommu_shared.contains(page)
                // (5) Global-shared pages are outside the private hypervisor pool.
        &&& forall|page: PhysPage| #[trigger]
            self.iommu_shared.contains(page) ==> !self.hypervisor_owned.contains(page)
    }

    /// Every IOMMU stage-2 mapping targets a page the mapped VM is allowed to DMA: one
    /// of its private DMA pages (`iommu_owned`) or a currently mapped
    /// global-shared page (`iommu_shared`).
    pub open spec fn iommu_translation_wf(&self) -> bool {
        forall|key: VmPageKey| #[trigger]
            self.iommu_s2_map.contains_key(key) ==> {
                &&& self.all_vms.contains(key.vm)
                &&& self.iommu_owned.contains_key(key.vm)
                &&& (self.iommu_owned[key.vm].contains(self.iommu_s2_map[key].page)
                    || self.iommu_shared.contains(self.iommu_s2_map[key].page))
            }
    }

    /// Combined IOMMU well-formedness: private DMA pages are cross-zone
    /// disjoint and every IOMMU entry targets either private or global-shared
    /// memory. A VM may legitimately CPU-map and DMA-map the same private page,
    /// so there is deliberately no same-VM `iommu_owned ∩ vm_owned = ∅` clause.
    pub open spec fn iommu_wf(&self) -> bool {
        &&& self.iommu_ownership_wf()
        &&& self.iommu_translation_wf()
    }

    /// Combined software well-formedness invariant.
    pub open spec fn wf(&self) -> bool {
        &&& self.ownership_wf()
        &&& self.translation_wf()
        &&& self.iommu_wf()
    }
}

} // verus!
