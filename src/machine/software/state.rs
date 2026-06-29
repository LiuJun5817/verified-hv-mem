use vstd::prelude::*;

use super::Region;
use crate::machine::types::*;

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
    /// Per-VM physical page ownership.
    pub vm_owned: Map<VmId, Set<PhysPage>>,
    /// Explicit cross-VM sharing edges (stored symmetrically: both `(l,r)` and
    /// `(r,l)` are present for every sharing relationship).
    pub shared_pages: Set<SharedPage>,
    /// Stage-2 page-table mappings installed by the hypervisor.
    pub s2_map: Map<VmPageKey, S2Entry>,
    /// IOMMU (SMMU) stage-2 mappings — a *second* stage-2 context per VM, for
    /// device DMA.  A VM's IOMMU may map its private pages (`iommu_owned`) or pages
    /// shared with it (e.g. the GIC), exactly mirroring the CPU `s2_map` discipline.
    pub iommu_s2_map: Map<VmPageKey, S2Entry>,
    /// Per-VM physical pages a VM owns for IOMMU/DMA.  Kept *separate* from
    /// `vm_owned` (the CPU side): both are drawn from the VM's private region budget
    /// and are cross-VM disjoint, but a VM may IOMMU-map a page it has not CPU-mapped.
    pub iommu_owned: Map<VmId, Set<PhysPage>>,
    /// Pages that may be IOMMU-shared across *all* VMs (the GIC region).  A
    /// VM-independent set, distinct from the per-edge `shared_pages` CPU sharing
    /// graph: it is the *only* memory a page may be co-owned through across VMs.
    pub iommu_shared: Set<PhysPage>,
}

impl SoftwareView {
    // ------------------------------------------------------------------
    // Trusted abstract predicate (uninterpreted)
    // ------------------------------------------------------------------
    /// Whether `region` is a unit assignable to its VM *in this state*.
    /// Uninterpreted at the machine level — an implementation characterizes it (via
    /// its region budget, a runtime check, …) with a refinement axiom (see
    /// `crate::refinement::view::axiom_assignable_from_budget`).  Being
    /// state-dependent, the machine model makes no region-budget assumption of its own.
    pub uninterp spec fn is_region_assignable(self, region: Region) -> bool;

    // ------------------------------------------------------------------
    // Derived predicates
    // ------------------------------------------------------------------
    /// `page` is accessible to `vm` either because `vm` owns it outright
    /// or because it appears in an explicit sharing edge with `vm`.
    pub open spec fn owned_or_shared(&self, vm: VmId, page: PhysPage) -> bool {
        (self.vm_owned.contains_key(vm) && self.vm_owned[vm].contains(page)) || self.shared_with(
            vm,
            page,
        )
    }

    /// `vm` has a sharing edge for `page` (appears on either side of the edge).
    pub open spec fn shared_with(&self, vm: VmId, page: PhysPage) -> bool {
        exists|edge: SharedPage| #[trigger]
            self.shared_pages.contains(edge) && edge.page == page && (edge.left == vm || edge.right
                == vm)
    }


    // ------------------------------------------------------------------
    // Well-formedness predicates
    // ------------------------------------------------------------------
    /// Per-VM ownership sets cover exactly `all_vms`, are pairwise disjoint,
    /// and do not overlap with `hypervisor_owned`.
    pub open spec fn ownership_wf(&self) -> bool {
        &&& self.vm_owned.dom() == self.all_vms
        &&& forall|vm1: VmId, vm2: VmId| #[trigger]
            self.all_vms.contains(vm1) && #[trigger] self.all_vms.contains(vm2) && vm1 != vm2
                ==> forall|page: PhysPage| #[trigger]
                self.vm_owned[vm1].contains(page) ==> !self.vm_owned[vm2].contains(page)
        &&& forall|vm: VmId| #[trigger]
            self.all_vms.contains(vm) ==> forall|page: PhysPage| #[trigger]
                self.vm_owned[vm].contains(page) ==> !self.hypervisor_owned.contains(page)
    }

    /// Sharing edges are symmetric and only connect distinct, valid VMs.
    pub open spec fn sharing_wf(&self) -> bool {
        forall|edge: SharedPage| #[trigger]
            self.shared_pages.contains(edge) ==> {
                &&& edge.left != edge.right
                &&& self.all_vms.contains(edge.left)
                &&& self.all_vms.contains(edge.right)
                &&& self.shared_pages.contains(edge.reverse())
            }
    }

    /// Every stage-2 mapping targets a page owned or shared by the mapped VM.
    pub open spec fn translation_wf(&self) -> bool {
        forall|key: VmPageKey| #[trigger]
            self.s2_map.contains_key(key) ==> {
                &&& self.all_vms.contains(key.vm)
                &&& self.owned_or_shared(key.vm, self.s2_map[key].page)
            }
    }

    /// IOMMU ownership separation: `iommu_owned` covers exactly `all_vms`, and a VM's
    /// IOMMU pages may coincide with *another* VM's IOMMU pages **only on an
    /// explicitly shared page** (the GIC) — private (zone-budget) pages are
    /// zone-disjoint — and never coincide with another VM's CPU-owned pages.
    pub open spec fn iommu_ownership_wf(&self) -> bool {
        &&& self.iommu_owned.dom() == self.all_vms
        // Cross-VM IOMMU overlap is permitted only on `iommu_shared` pages (the GIC).
        &&& forall|vm1: VmId, vm2: VmId, page: PhysPage|
            self.all_vms.contains(vm1) && self.all_vms.contains(vm2) && vm1 != vm2
            && #[trigger] self.iommu_owned[vm1].contains(page)
            && #[trigger] self.iommu_owned[vm2].contains(page)
                ==> self.iommu_shared.contains(page)
        // A VM's IOMMU pages never coincide with another VM's CPU-owned pages.
        &&& forall|vm1: VmId, vm2: VmId| #[trigger]
            self.all_vms.contains(vm1) && #[trigger] self.all_vms.contains(vm2) && vm1 != vm2
                ==> forall|page: PhysPage| #[trigger]
                self.iommu_owned[vm1].contains(page) ==> !self.vm_owned[vm2].contains(page)
    }

    /// Every IOMMU stage-2 mapping targets a page the mapped VM owns for DMA
    /// (`iommu_owned`).  Combined with `iommu_ownership_wf`, this confines a VM's DMA
    /// to its private (zone-disjoint) pages plus explicitly shared pages (the GIC).
    pub open spec fn iommu_translation_wf(&self) -> bool {
        forall|key: VmPageKey| #[trigger]
            self.iommu_s2_map.contains_key(key) ==> {
                &&& self.all_vms.contains(key.vm)
                &&& self.iommu_owned.contains_key(key.vm)
                &&& self.iommu_owned[key.vm].contains(self.iommu_s2_map[key].page)
            }
    }

    /// Combined IOMMU well-formedness: the design's *memory separation* (private
    /// zone-budget pages are cross-VM disjoint; cross-VM IOMMU overlap only on shared
    /// GIC pages; IOMMU pages never alias another VM's CPU pages) **and** *sharing*
    /// (GIC pages are reachable via the sharing graph).  Proven to hold for every
    /// reachable implementation state by
    /// [`crate::refinement::view::lemma_reachable_iommu_separation`].
    ///
    /// Kept *separate* from [`wf`](Self::wf): folding the IOMMU invariant into the
    /// generic abstract transition system additionally requires IOMMU-aware guards on
    /// the generic page ops (`assign`/`share`/`unshare`) — tracked as follow-up work.
    pub open spec fn iommu_wf(&self) -> bool {
        &&& self.iommu_ownership_wf()
        &&& self.iommu_translation_wf()
    }

    /// Combined software well-formedness invariant.
    pub open spec fn wf(&self) -> bool {
        &&& self.ownership_wf()
        &&& self.sharing_wf()
        &&& self.translation_wf()
    }
}

} // verus!
