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
    /// Per-VM **private** physical pages a VM owns for IOMMU/DMA — its zone-budget DMA
    /// memory *excluding* the shared GIC (which is tracked separately in
    /// `iommu_shared`).  Kept *separate* from `vm_owned` (the CPU side): both are drawn
    /// from the VM's private region budget and are cross-VM disjoint, but a VM may
    /// IOMMU-map a page it has not CPU-mapped (and vice-versa).  Because the GIC is
    /// excluded, this set is genuinely private — pairwise disjoint across VMs with no
    /// exception.
    pub iommu_owned: Map<VmId, Set<PhysPage>>,
    /// Pages that may be IOMMU-shared across *all* VMs (the GIC region).  A
    /// VM-independent set, distinct from the per-edge `shared_pages` CPU sharing graph
    /// and from every VM's private `iommu_owned`: it is the *only* memory a VM's DMA may
    /// reach that is not its own private DMA page.
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

    /// IOMMU ownership separation.  `iommu_owned` holds each VM's **private** DMA pages
    /// (the shared GIC lives in `iommu_shared`), so its clauses are the crisp form of
    /// the design's rules: (1) private DMA pages are cross-VM disjoint — no GIC
    /// exception, since the GIC is not private; (2) a VM's private DMA pages are never
    /// another VM's CPU-owned pages; (3) private DMA pages are disjoint from the shared
    /// region.  A VM may still DMA-map *its own* CPU pages — there is deliberately no
    /// same-VM `iommu_owned ∩ vm_owned = ∅` clause.
    pub open spec fn iommu_ownership_wf(&self) -> bool {
        &&& self.iommu_owned.dom() == self.all_vms
        // (1) Private DMA pages are pairwise cross-VM disjoint.
        &&& forall|vm1: VmId, vm2: VmId| #[trigger]
            self.all_vms.contains(vm1) && #[trigger] self.all_vms.contains(vm2) && vm1 != vm2
                ==> forall|page: PhysPage| #[trigger]
                self.iommu_owned[vm1].contains(page) ==> !self.iommu_owned[vm2].contains(page)
        // (2) A VM's private DMA pages are never another VM's CPU-owned pages.
        &&& forall|vm1: VmId, vm2: VmId| #[trigger]
            self.all_vms.contains(vm1) && #[trigger] self.all_vms.contains(vm2) && vm1 != vm2
                ==> forall|page: PhysPage| #[trigger]
                self.iommu_owned[vm1].contains(page) ==> !self.vm_owned[vm2].contains(page)
        // (3) Private DMA pages are disjoint from the shared region (truly private).
        &&& forall|vm: VmId| #[trigger]
            self.all_vms.contains(vm) ==> forall|page: PhysPage| #[trigger]
                self.iommu_owned[vm].contains(page) ==> !self.iommu_shared.contains(page)
    }

    /// Every IOMMU stage-2 mapping targets a page the mapped VM is allowed to DMA: one
    /// of its **private** DMA pages (`iommu_owned`) or a **shared** page (`iommu_shared`,
    /// the GIC).  Combined with `iommu_ownership_wf`, this confines a VM's DMA to its
    /// private (zone-disjoint) pages plus the shared GIC.
    pub open spec fn iommu_translation_wf(&self) -> bool {
        forall|key: VmPageKey| #[trigger]
            self.iommu_s2_map.contains_key(key) ==> {
                &&& self.all_vms.contains(key.vm)
                &&& self.iommu_owned.contains_key(key.vm)
                &&& (self.iommu_owned[key.vm].contains(self.iommu_s2_map[key].page)
                    || self.iommu_shared.contains(self.iommu_s2_map[key].page))
            }
    }

    /// Combined IOMMU well-formedness: the design's **cross-VM** *memory separation*
    /// (private DMA pages are cross-VM disjoint and never alias another VM's CPU pages;
    /// the shared GIC is the only page a VM's DMA may reach that it does not privately
    /// own) and *translation confinement* (each IOMMU entry targets one of its VM's
    /// private DMA pages or the shared GIC).  Only cross-VM isolation is required: a VM
    /// may legitimately CPU-map *and* DMA-map the same page (both are drawn from its
    /// trusted `zone_regions`), so there is deliberately **no** same-VM
    /// `iommu_owned ∩ vm_owned = ∅` clause.  Proven for every reachable implementation
    /// state by [`crate::refinement::view::lemma_reachable_iommu_separation`].
    ///
    /// Note there is **no** `iommu_owned ∩ hypervisor_owned = ∅` ("pool-disjoint")
    /// clause: a private IOMMU-only page (DMA-mapped but not CPU-mapped) projects *into*
    /// the hypervisor pool, so such a clause would be false at the projection.
    ///
    /// Kept *separate* from [`wf`](Self::wf) for now: folding the IOMMU invariant into
    /// the generic abstract transition system requires IOMMU-aware cross-VM guards on
    /// the CPU page/region ops (`assign`/`insert_region` could move a page that another
    /// VM still DMA-maps), which couples to the machine-refinement layer
    /// (`refinement::machine` derives `SoftwareView::wf` through a CPU-only bridge and
    /// the region-trace partials mutate `vm_owned`).  That fold lands with the
    /// `MachineState` IOMMU rework.  The per-page DMA steps below preserve `iommu_wf`
    /// outright (no cross-VM coupling); see `super::proof`.
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
