use vstd::prelude::*;

use super::SwView;
use crate::machine::types::*;

verus! {

/// Specification trait for hypervisor software state management.
///
/// This is a **ghost contract**: a concrete type `T: View<V = SwView>`
/// represents the hypervisor's abstract memory state, and each transition is a
/// `proof fn` whose observable effect on the view is characterised by the
/// matching [`SwView`] step predicate.
///
/// The transitions take `self` **by value** (returning the post-state `Self`)
/// rather than `&mut self`: the implementing type is a pure-ghost value, and pure
/// ghost values have no mutability semantics — a transition is modelled as a
/// function `pre ↦ post`.  The implementing type is `BudgetSpec::State` itself
/// (see `crate::refinement`), so `invariants()` is the state machine's real
/// `invariant()` rather than a separate copy.
///
/// ## Granularity
///
/// Operations are **region-bulk** (`insert_region` / `remove_region`) plus VM
/// lifecycle (`add_vm` / `remove_vm`), matching what the hypervisor realizes and
/// what is derivable from the region-only budget state.  Per-page `map` / `unmap`
/// are *not* trait methods: they are not realizable from region-only state.  They
/// survive as the [`SwView`] step predicates that define a region step's meaning
/// (`SwView::insert_region_step` is the composition of the per-page `map_step` /
/// `assign_page_step`).
pub trait SoftwareOps: View<V = SwView> + Sized {
    // ------------------------------------------------------------------
    // Invariant
    // ------------------------------------------------------------------
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

    // ------------------------------------------------------------------
    // VM lifecycle
    // ------------------------------------------------------------------
    /// Register a fresh, empty VM.
    proof fn add_vm(self, vm: VmId) -> (post: Self)
        requires
            self.invariants(),
            !self@.all_vms.contains(vm),
        ensures
            post.invariants(),
            SwView::add_vm_step(self@, post@, vm),
    ;

    /// Deregister a VM that owns no pages and has no stage-2 mappings.
    proof fn remove_vm(self, vm: VmId) -> (post: Self)
        requires
            self.invariants(),
            self@.all_vms.contains(vm),
            self@.vm_owned[vm] == Set::<PhysPage>::empty(),
            forall|k: VmPageKey| #[trigger] self@.s2_map.contains_key(k) ==> k.vm != vm,
        ensures
            post.invariants(),
            SwView::remove_vm_step(self@, post@, vm),
    ;

    // ------------------------------------------------------------------
    // Region operations (assign + map / unmap + reclaim)
    // ------------------------------------------------------------------
    /// Precondition for `insert_region`
    spec fn insert_region_pre(
        self,
        vm: VmId,
        pages: Set<PhysPage>,
        entries: Map<VmPageKey, S2Entry>,
    ) -> bool;

    /// Assign `pages` (drawn from the hypervisor pool) to `vm` and install the
    /// stage-2 `entries` for them.
    proof fn insert_region(
        self,
        vm: VmId,
        pages: Set<PhysPage>,
        entries: Map<VmPageKey, S2Entry>,
    ) -> (post: Self)
        requires
            self.invariants(),
            self@.all_vms.contains(vm),
            Self::insert_region_pre(self, vm, pages, entries),
            forall|p: PhysPage| #[trigger] pages.contains(p) ==> self@.hypervisor_owned.contains(p),
            forall|k: VmPageKey| #[trigger] entries.contains_key(k) ==> k.vm == vm,
        ensures
            post.invariants(),
            SwView::insert_region_step(self@, post@, vm, pages, entries),
    ;

    /// Precondition for `remove_region` (implementor-defined, e.g. "`pages`/`keys`
    /// are exactly some region currently present in the zone").
    spec fn remove_region_pre(self, vm: VmId, pages: Set<PhysPage>, keys: Set<VmPageKey>) -> bool;

    /// Unmap the `keys` and reclaim `pages` from `vm` back to the hypervisor pool.
    proof fn remove_region(self, vm: VmId, pages: Set<PhysPage>, keys: Set<VmPageKey>) -> (post:
        Self)
        requires
            self.invariants(),
            self@.all_vms.contains(vm),
            Self::remove_region_pre(self, vm, pages, keys),
            forall|p: PhysPage| #[trigger] pages.contains(p) ==> self@.vm_owned[vm].contains(p),
            forall|k: VmPageKey| #[trigger] keys.contains(k) ==> k.vm == vm,
        ensures
            post.invariants(),
            SwView::remove_region_step(self@, post@, vm, pages, keys),
    ;
}

} // verus!
