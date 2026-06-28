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

    /// Combined software well-formedness invariant.
    pub open spec fn wf(&self) -> bool {
        &&& self.ownership_wf()
        &&& self.sharing_wf()
        &&& self.translation_wf()
    }
}

} // verus!
