use vstd::prelude::*;

use super::SwView;
use crate::machine::types::*;

verus! {

/// Specification trait for hypervisor software state management.
///
/// Any concrete type `T: View<V = SwView>` that implements this trait provides
/// exec-level operations whose observable effect on the abstract view is
/// exactly characterised by the matching [`SwView`] step predicate.
pub trait SoftwareOps: View<V = SwView> {
    // ------------------------------------------------------------------
    // Invariant
    // ------------------------------------------------------------------
    /// Internal consistency predicate.  Implementations must establish this
    /// at construction and preserve it across all operations.
    spec fn invariants(&self) -> bool;

    /// Invariants imply the abstract state is well-formed.
    broadcast proof fn inv_implies_wf(&self)
        requires
            #[trigger] self.invariants(),
        ensures
            self@.wf(),
    ;

    // ------------------------------------------------------------------
    // Stage-2 mapping management
    // ------------------------------------------------------------------
    /// Install (or replace) the stage-2 mapping for `(vm, gpa)`.
    fn map(&mut self, vm: Ghost<VmId>, gpa: Ghost<GuestPage>, entry: Ghost<S2Entry>)
        requires
            old(self).invariants(),
            old(self)@.all_vms.contains(vm@),
            old(self)@.owned_or_shared(vm@, entry@.page),
        ensures
            self.invariants(),
            SwView::map_step(old(self)@, self@, vm@, gpa@, entry@),
    ;

    /// Remove the stage-2 mapping for `(vm, gpa)`.
    fn unmap(&mut self, vm: Ghost<VmId>, gpa: Ghost<GuestPage>)
        requires
            old(self).invariants(),
            old(self)@.s2_map.contains_key(VmPageKey::new(vm@, gpa@)),
        ensures
            self.invariants(),
            SwView::unmap_step(old(self)@, self@, vm@, gpa@),
    ;

    // ------------------------------------------------------------------
    // Page ownership management
    // ------------------------------------------------------------------
    /// Transfer `page` from the hypervisor pool to `vm`.
    fn assign_page(&mut self, vm: Ghost<VmId>, page: Ghost<PhysPage>)
        requires
            old(self).invariants(),
            old(self)@.all_vms.contains(vm@),
            old(self)@.hypervisor_owned.contains(page@),
        ensures
            self.invariants(),
            SwView::assign_page_step(old(self)@, self@, vm@, page@),
    ;

    /// Reclaim `page` from `vm` back to the hypervisor pool.
    fn reclaim_page(&mut self, vm: Ghost<VmId>, page: Ghost<PhysPage>)
        requires
            old(self).invariants(),
            old(self)@.all_vms.contains(vm@),
            old(self)@.vm_owned.contains_key(vm@) && old(self)@.vm_owned[vm@].contains(page@),
        ensures
            self.invariants(),
            SwView::reclaim_page_step(old(self)@, self@, vm@, page@),
    ;

    // ------------------------------------------------------------------
    // Page sharing management
    // ------------------------------------------------------------------
    /// Establish a symmetric sharing edge for `page` between `left` and `right`.
    fn share_page(&mut self, left: Ghost<VmId>, right: Ghost<VmId>, page: Ghost<PhysPage>)
        requires
            old(self).invariants(),
            left@ != right@,
            old(self)@.all_vms.contains(left@) && old(self)@.all_vms.contains(right@),
            old(self)@.vm_owned.contains_key(left@) && old(self)@.vm_owned[left@].contains(page@),
        ensures
            self.invariants(),
            SwView::share_page_step(old(self)@, self@, left@, right@, page@),
    ;

    /// Remove the symmetric sharing edge for `page` between `left` and `right`.
    fn unshare_page(&mut self, left: Ghost<VmId>, right: Ghost<VmId>, page: Ghost<PhysPage>)
        requires
            old(self).invariants(),
            ({
                let edge = SharedPage { left: left@, right: right@, page: page@ };
                old(self)@.shared_pages.contains(edge)
                    && old(self)@.shared_pages.contains(edge.reverse())
            }),
        ensures
            self.invariants(),
            SwView::unshare_page_step(old(self)@, self@, left@, right@, page@),
    ;
}

} // verus!
