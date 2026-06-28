//! Hardware-refinement layer: `impl HardwareRefinement for MmuSpec::State`.
//!
//! The `HardwareView` analog of [`crate::refinement`].  The abstract state **is** the
//! tokenized state machine's own `MmuSpec::State` (`s2map` + `vm_ids` + `tlb`);
//! [`HardwareView`] is a projection of it, and the contract `invariants()` is the
//! machine's real, inductively-proven `invariant()` (full TLB coherence).
//!
//! ```text
//!   HardwareRefinement              ghost contract; invariants() == MmuSpec invariant()
//!       ▲ impl (here)
//!   MmuSpec::State           the state machine's own state  (projected by `view`)
//!   ├─ s2map:  Map<VmId, Map<GuestPage, S2Entry>>   (walker-reachable; software side)
//!   ├─ vm_ids: Set<VmId>
//!   └─ tlb:    Map<TlbKey, TlbEntry>                (the only HardwareView-visible field)
//!       ▲ token soundness: the tokens `MmuHardware` holds are tokens of a
//!         reachable MmuSpec::State
//!   MmuHardware  (fires MmuSpec transitions behind the `HardwareInstr` asm seam)
//! ```
//!
//! # The projection
//!
//! The MMU governs the TLB and the walker-reachable `s2map`, so both carry over to
//! `HardwareView` (`tlb` and `s2map`).  `memory` and `active_vm` are governed by the data
//! plane and the scheduler, not the MMU, so they are empty (and the in-scope
//! transitions leave them fixed).
//!
//! Each transition method fires the matching `MmuSpec` macro transition via
//! `MmuSpec::take_step::*` (which supplies `post.invariant()`) and proves the
//! corresponding `HardwareView` step.
use crate::hardware::spec::MmuSpec;
use crate::machine::convert::flatten_s2map;
use crate::machine::hardware::HardwareView;
use crate::machine::types::*;
use vstd::prelude::*;

verus! {

/// Specification trait for hardware-side TLB maintenance — the `HardwareView` analog
/// of [`SoftwareRefinement`](super::software::SoftwareRefinement).
///
/// A **ghost contract**: a concrete `T: View<V = HardwareView>` represents the
/// MMU/TLB state, and each transition is a `proof fn` taking `self` by value whose
/// effect on the view is characterised by the matching [`HardwareView`] step
/// predicate.  The implementing type is `MmuSpec::State` (impl below), so
/// `invariants()` is the tokenized state machine's real `invariant()` (full TLB
/// coherence).
///
/// # Scope: the hypervisor-issued maintenance instructions only
///
/// | op               | `HardwareView` step                     | instruction                  |
/// |------------------|-----------------------------------------|------------------------------|
/// | `tlb_invalidate` | [`HardwareView::unmap_invalidate_step`]  | `DSB ISH` + `TLBI IPAS2E1IS` |
/// | `map_fence`      | [`HardwareView::map_step`]                | `DSB ISH` (map side)         |
///
/// The autonomous TLB *fill* is an **environment** transition (it depends on
/// `active_vm`, no part of the MMU's token state) — out of this contract, exactly as
/// cross-VM sharing is out of `SoftwareRefinement`.
pub trait HardwareRefinement: View<V = HardwareView> + Sized {
    /// Internal consistency predicate.  Implementations must establish this at
    /// construction and preserve it across all transitions.
    spec fn invariants(&self) -> bool;

    /// Enabledness of [`map_fence`](HardwareRefinement::map_fence): the page is fresh
    /// for a live VM, so installing it grows the reachable map by exactly `(vm, gpa)`.
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
    /// cached entries, together.  Always enabled (a no-op for an unreachable page).
    proof fn tlb_invalidate(self, vm: VmId, gpa: GuestPage) -> (post: Self)
        requires
            self.invariants(),
        ensures
            post.invariants(),
            HardwareView::unmap_invalidate_step(self@, post@, vm, gpa),
    ;

    /// The map-side `DSB ISH` that makes a freshly written PTE walker-reachable,
    /// growing the reachable map by `(vm, gpa) => entry`.  No `TLBI` (the page was
    /// absent, so it had no cached entry), so the TLB is untouched.
    proof fn map_fence(self, vm: VmId, gpa: GuestPage, entry: S2Entry) -> (post: Self)
        requires
            self.invariants(),
            self.map_fresh(vm, gpa),
        ensures
            post.invariants(),
            HardwareView::map_step(self@, post@, vm, gpa, entry),
    ;
}

// ───────────────────────── the abstraction relation R ───────────────────────
impl View for MmuSpec::State {
    type V = HardwareView;

    /// R: project the MMU state to the abstract `HardwareView`.  `tlb` and the (flattened)
    /// reachable `s2map` carry over — these are what the MMU governs.  `memory` and
    /// `active_vm` are empty: the data plane and scheduler are out of MMU scope.
    open spec fn view(&self) -> HardwareView {
        HardwareView {
            tlb: self.tlb,
            s2map: flatten_s2map(self.s2map),
            memory: Map::empty(),
            active_vm: Map::empty(),
        }
    }
}

// ───────────────────────── facts about the projection ───────────────────────
/// If `post` differs from `pre` only by removing `gpa` from `vm`'s slice, the
/// flattened map loses exactly the flat key `(vm, gpa)` — matching
/// `unmap_invalidate_step`.  Stated over `pre`/`post` directly (rather than a
/// closed-form `insert`) so it is robust to the macro's remove-then-insert shape.
proof fn lemma_flatten_remove(
    pre: Map<VmId, Map<GuestPage, S2Entry>>,
    post: Map<VmId, Map<GuestPage, S2Entry>>,
    vm: VmId,
    gpa: GuestPage,
)
    requires
        pre.contains_key(vm),
        post.dom() == pre.dom(),
        post[vm] == pre[vm].remove(gpa),
        forall|v: VmId| #[trigger] pre.contains_key(v) && v != vm ==> post[v] == pre[v],
    ensures
        flatten_s2map(post) == flatten_s2map(pre).remove(VmPageKey::new(vm, gpa)),
{
    let skey = VmPageKey::new(vm, gpa);
    assert(flatten_s2map(post) =~= flatten_s2map(pre).remove(skey)) by {
        assert forall|k: VmPageKey| #[trigger]
            flatten_s2map(post).contains_key(k) <==> flatten_s2map(pre).remove(skey).contains_key(
                k,
            ) by {
            if k.vm != vm && pre.contains_key(k.vm) {
                assert(post[k.vm] == pre[k.vm]);
            }
        }
    }
}

/// If `post` differs from `pre` only by inserting `gpa => entry` into `vm`'s slice,
/// the flattened map gains exactly the flat key `(vm, gpa)` — matching `map_step`.
proof fn lemma_flatten_insert(
    pre: Map<VmId, Map<GuestPage, S2Entry>>,
    post: Map<VmId, Map<GuestPage, S2Entry>>,
    vm: VmId,
    gpa: GuestPage,
    entry: S2Entry,
)
    requires
        pre.contains_key(vm),
        post.dom() == pre.dom(),
        post[vm] == pre[vm].insert(gpa, entry),
        forall|v: VmId| #[trigger] pre.contains_key(v) && v != vm ==> post[v] == pre[v],
    ensures
        flatten_s2map(post) == flatten_s2map(pre).insert(VmPageKey::new(vm, gpa), entry),
{
    let skey = VmPageKey::new(vm, gpa);
    assert(flatten_s2map(post) =~= flatten_s2map(pre).insert(skey, entry)) by {
        assert forall|k: VmPageKey| #[trigger]
            flatten_s2map(post).contains_key(k) <==> flatten_s2map(pre).insert(
                skey,
                entry,
            ).contains_key(k) by {
            if k.vm != vm && pre.contains_key(k.vm) {
                assert(post[k.vm] == pre[k.vm]);
            }
        }
    }
}

/// A page whose VM is absent from `s2map` is absent from the flattened map and has
/// no cached TLB entry (contrapositive of `inv_coherent`), so an unmap of it is a
/// no-op on both `s2map` and `tlb`.
proof fn lemma_absent_vm_noop(s: MmuSpec::State, vm: VmId, gpa: GuestPage)
    requires
        s.invariant(),
        !s.s2map.contains_key(vm),
    ensures
        flatten_s2map(s.s2map).remove(VmPageKey::new(vm, gpa)) == flatten_s2map(s.s2map),
        s.tlb.remove_keys(Set::new(|key: TlbKey| key.vm == vm && key.gpa == gpa)) == s.tlb,
{
    let targets = Set::new(|key: TlbKey| key.vm == vm && key.gpa == gpa);
    assert(!flatten_s2map(s.s2map).contains_key(VmPageKey::new(vm, gpa)));
    assert(flatten_s2map(s.s2map).remove(VmPageKey::new(vm, gpa)) =~= flatten_s2map(s.s2map));
    assert(s.tlb.remove_keys(targets) =~= s.tlb) by {
        assert forall|k: TlbKey| #[trigger] s.tlb.contains_key(k) implies !targets.contains(k) by {
            // inv_coherent: a cached key's vm is in s2map, but vm is not — so k.vm != vm.
            assert(s.s2map.contains_key(k.vm));
        }
    }
}

// ───────────────────────── the refinement ───────────────────────────────────
impl HardwareRefinement for MmuSpec::State {
    /// The contract invariant is the state machine's real invariant.
    open spec fn invariants(&self) -> bool {
        self.invariant()
    }

    /// `map` is enabled when the page is fresh for a live VM.
    open spec fn map_fresh(&self, vm: VmId, gpa: GuestPage) -> bool {
        &&& self.s2map.contains_key(vm)
        &&& !self.s2map[vm].contains_key(gpa)
    }

    broadcast proof fn inv_implies_wf(&self)
        ensures
            #[trigger] self@.wf(),
    {
        let hw = self@;
        // tlb_safe over the flattened reachable map follows directly from the MMU's
        // `inv_coherent` invariant (they are the same statement, un/flattened).
        assert forall|key: TlbKey| #[trigger] hw.tlb.contains_key(key) implies {
            let sk = VmPageKey::new(key.vm, key.gpa);
            &&& hw.s2map.contains_key(sk)
            &&& hw.tlb[key].as_s2_entry() == hw.s2map[sk]
        } by {
            assert(self.s2map.contains_key(key.vm));
            assert(self.s2map[key.vm].contains_key(key.gpa));
        }
    }

    proof fn tlb_invalidate(self, vm: VmId, gpa: GuestPage) -> (post: Self) {
        let post;
        if self.s2map.contains_key(vm) {
            // The page's VM is live: fire the atomic break-before-make transition —
            // it drops `(vm, gpa)` from the reachable map and flushes its TLB entries.
            post = MmuSpec::take_step::unmap_invalidate(self, vm, gpa);
            assert(post.s2map.dom() =~= self.s2map.dom());
            assert(post.s2map[vm] == self.s2map[vm].remove(gpa));
            lemma_flatten_remove(self.s2map, post.s2map, vm, gpa);
        } else {
            // No live VM ⇒ page already unreachable and uncached ⇒ a no-op.
            lemma_absent_vm_noop(self, vm, gpa);
            post = self;
        }
        assert(HardwareView::unmap_invalidate_step(self@, post@, vm, gpa));
        post
    }

    proof fn map_fence(self, vm: VmId, gpa: GuestPage, entry: S2Entry) -> (post: Self) {
        // `map_fresh` ⇒ the page is fresh for a live VM, so `map` grows the
        // reachable map by exactly `(vm, gpa) => entry`; the TLB is untouched.
        let post = MmuSpec::take_step::map(self, vm, gpa, entry);
        assert(post.s2map.dom() =~= self.s2map.dom());
        assert(post.s2map[vm] == self.s2map[vm].insert(gpa, entry));
        lemma_flatten_insert(self.s2map, post.s2map, vm, gpa, entry);
        assert(HardwareView::map_step(self@, post@, vm, gpa, entry));
        post
    }
}

} // verus!
