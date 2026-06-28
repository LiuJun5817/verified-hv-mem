use vstd::prelude::*;

use super::HwView;
use crate::machine::types::*;

verus! {

/// Specification trait for hardware-side TLB maintenance — the `HwView` analog of
/// [`SoftwareOps`](crate::machine::software::SoftwareOps).
///
/// A **ghost contract**: a concrete `T: View<V = HwView>` represents the
/// MMU/TLB state, and each transition is a `proof fn` taking `self` by value whose
/// effect on the view is characterised by the matching [`HwView`] step predicate.
/// The implementing type is `MmuSpec::State` itself (see
/// [`crate::machine::hardware::refine`]), so `invariants()` is the tokenized state
/// machine's real `invariant()` — i.e. full TLB coherence.
///
/// # Scope: the hypervisor-issued maintenance instructions only
///
/// `HardwareOps` covers exactly the transitions the *hypervisor* drives through a
/// maintenance instruction:
///
/// | `HardwareOps` op  | `HwView` step                       | instruction              |
/// |-------------------|-------------------------------------|--------------------------|
/// | `tlb_invalidate`  | [`HwView::unmap_invalidate_step`]   | `DSB ISH` + `TLBI IPAS2E1IS` |
/// | `map_fence`       | [`HwView::map_step`]                | `DSB ISH` (map side)     |
///
/// The autonomous TLB *fill* is an **environment** transition — it caches a
/// translation for whichever VM the scheduler is running, so it depends on
/// `active_vm`, which is no part of the MMU's token state — and is therefore out of
/// this contract, exactly as cross-VM sharing is out of `SoftwareOps`.
pub trait HardwareOps: View<V = HwView> + Sized {
    /// Internal consistency predicate.  Implementations must establish this at
    /// construction and preserve it across all transitions.
    spec fn invariants(&self) -> bool;

    /// Enabledness of [`map_fence`](HardwareOps::map_fence): the page is fresh for a
    /// live VM, so installing it grows the reachable map by exactly `(vm, gpa)`.
    /// Owned by the implementation (it depends on the reachable map's domain, not
    /// derivable from `HwView` alone), mirroring `SwView::*_enabled`.
    spec fn map_fresh(&self, vm: VmId, gpa: GuestPage) -> bool;

    /// Invariants imply the hardware view is well-formed.
    broadcast proof fn inv_implies_wf(&self)
        requires
            #[trigger] self.invariants(),
        ensures
            self@.wf(),
    ;

    /// Atomic break-before-make unmap of `(vm, gpa)`: the `DSB ISH` drops the page
    /// from the hardware-reachable map and the `TLBI IPAS2E1IS` broadcast flushes its
    /// cached entries, together.
    ///
    /// Always enabled: for a page absent from the reachable map this is a no-op (by
    /// the coherence invariant it has no cached entry either).
    proof fn tlb_invalidate(self, vm: VmId, gpa: GuestPage) -> (post: Self)
        requires
            self.invariants(),
        ensures
            post.invariants(),
            HwView::unmap_invalidate_step(self@, post@, vm, gpa),
    ;

    /// The map-side `DSB ISH` that makes a freshly written PTE walker-reachable,
    /// growing the reachable map by `(vm, gpa) => entry`.  Break-before-make on the
    /// map side needs no `TLBI` (the page was absent, so it had no cached entry), so
    /// the TLB is untouched.
    proof fn map_fence(self, vm: VmId, gpa: GuestPage, entry: S2Entry) -> (post: Self)
        requires
            self.invariants(),
            self.map_fresh(vm, gpa),
        ensures
            post.invariants(),
            HwView::map_step(self@, post@, vm, gpa, entry),
    ;
}

} // verus!
