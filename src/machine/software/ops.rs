use vstd::prelude::*;

use super::{Region, SwView};
use crate::machine::types::*;

verus! {

/// Specification trait for hypervisor software state management.
///
/// A **ghost contract**: a concrete `T: View<V = SwView>` represents the
/// hypervisor's abstract memory state, and each transition is a `proof fn` taking
/// `self` by value whose effect on the view is characterised by the matching
/// [`SwView`] step predicate.  The implementing type is `BudgetSpec::State` itself
/// (see `crate::refinement`), so `invariants()` is the state machine's real
/// `invariant()`.
///
/// The four operations are what the hypervisor realizes: VM lifecycle (`add_vm` /
/// `remove_vm`) and region-bulk (`insert_region` / `remove_region`, over a
/// machine-level [`Region`]).  Each precondition is the closed `SwView::*_enabled`
/// predicate, owned by the trusted model, so an implementation cannot weaken it.
pub trait SoftwareOps: View<V = SwView> + Sized {
    /// Internal consistency predicate.  Implementations must establish this at
    /// construction and preserve it across all transitions.
    spec fn invariants(&self) -> bool;

    /// Invariants imply the abstract state is well-formed.
    broadcast proof fn inv_implies_wf(&self)
        requires
            #[trigger] self.invariants(),
        ensures
            self@.wf(),
    ;

    /// Register a fresh, empty VM.
    proof fn add_vm(self, vm: VmId) -> (post: Self)
        requires
            self.invariants(),
            SwView::add_vm_enabled(self@, vm),
        ensures
            post.invariants(),
            SwView::add_vm_step(self@, post@, vm),
    ;

    /// Deregister a VM that owns no pages, has no mappings, and shares nothing.
    proof fn remove_vm(self, vm: VmId) -> (post: Self)
        requires
            self.invariants(),
            SwView::remove_vm_enabled(self@, vm),
        ensures
            post.invariants(),
            SwView::remove_vm_step(self@, post@, vm),
    ;

    /// Assign `region`'s pages (from the hypervisor pool) to its VM and install
    /// its stage-2 entries.
    proof fn insert_region(self, region: Region) -> (post: Self)
        requires
            self.invariants(),
            SwView::insert_region_enabled(self@, region),
        ensures
            post.invariants(),
            SwView::insert_region_step(self@, post@, region),
    ;

    /// Unmap `region`'s entries and reclaim its pages back to the hypervisor pool.
    proof fn remove_region(self, region: Region) -> (post: Self)
        requires
            self.invariants(),
            SwView::remove_region_enabled(self@, region),
        ensures
            post.invariants(),
            SwView::remove_region_step(self@, post@, region),
    ;
}

} // verus!
