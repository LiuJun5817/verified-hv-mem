//! Hardware-refinement layer: `impl HardwareRefinement for HardwareSpec`.
//!
//! [`HardwareSpec`] is the hardware-side abstraction carrier: a pair of regime-neutral
//! `MmuSpec::State` instances, one for the CPU MMU and one for the SMMU/IOMMU.  The
//! projection into [`HardwareView`] exposes both walker-reachable maps and both TLBs.
//! This avoids having two competing `View` impls for `MmuSpec::State` while keeping the
//! MMU state machine itself shared between CPU and IOMMU.
use crate::hardware::spec::MmuSpec;
use crate::model::convert::flatten_s2map;
use crate::model::hardware::HardwareView;
use crate::model::types::*;
use vstd::prelude::*;

verus! {

/// The pair of hardware-side tokenized states: CPU MMU plus SMMU/IOMMU.
pub ghost struct HardwareSpec {
    pub mmu: MmuSpec::State,
    pub smmu: MmuSpec::State,
}

/// Specification trait for hardware-side TLB maintenance — the `HardwareView` analog
/// of [`SoftwareRefinement`](super::software::SoftwareRefinement).
///
/// A **ghost contract**: a concrete `T: View<V = HardwareView>` represents the full
/// hardware translation state, and each transition is a `proof fn` taking `self` by
/// value whose effect on the view is characterized by the matching [`HardwareView`]
/// step predicate.
pub trait HardwareRefinement: View<V = HardwareView> + Sized {
    /// Internal consistency predicate.  Implementations must establish this at
    /// construction and preserve it across all transitions.
    spec fn invariants(&self) -> bool;

    /// Enabledness of [`map_fence`](HardwareRefinement::map_fence): the CPU page is
    /// fresh for a live VM, so installing it grows the reachable map by exactly
    /// `(vm, gpa)`.
    spec fn map_fresh(&self, vm: VmId, gpa: GuestPage) -> bool;

    /// Enabledness of [`iommu_map_fence`](HardwareRefinement::iommu_map_fence): the
    /// IOMMU page is fresh for a live VM in the SMMU instance.
    spec fn iommu_map_fresh(&self, vm: VmId, gpa: GuestPage) -> bool;

    /// Invariants imply the full hardware view is well-formed.
    broadcast proof fn inv_implies_wf(&self)
        requires
            #[trigger] self.invariants(),
        ensures
            self@.wf(),
    ;

    /// CPU MMU atomic break-before-make unmap of `(vm, gpa)`.
    proof fn tlb_invalidate(self, vm: VmId, gpa: GuestPage) -> (post: Self)
        requires
            self.invariants(),
        ensures
            post.invariants(),
            HardwareView::unmap_invalidate_step(self@, post@, vm, gpa),
    ;

    /// CPU MMU map-side `DSB ISH` that makes a freshly written PTE walker-reachable.
    proof fn map_fence(self, vm: VmId, gpa: GuestPage, entry: S2Entry) -> (post: Self)
        requires
            self.invariants(),
            self.map_fresh(vm, gpa),
        ensures
            post.invariants(),
            HardwareView::map_step(self@, post@, vm, gpa, entry),
    ;

    /// SMMU/IOMMU atomic break-before-make unmap of `(vm, gpa)`.
    proof fn iommu_tlb_invalidate(self, vm: VmId, gpa: GuestPage) -> (post: Self)
        requires
            self.invariants(),
        ensures
            post.invariants(),
            HardwareView::iommu_unmap_invalidate_step(self@, post@, vm, gpa),
    ;

    /// SMMU/IOMMU map-side fence that makes a freshly written PTE walker-reachable.
    proof fn iommu_map_fence(self, vm: VmId, gpa: GuestPage, entry: S2Entry) -> (post: Self)
        requires
            self.invariants(),
            self.iommu_map_fresh(vm, gpa),
        ensures
            post.invariants(),
            HardwareView::iommu_map_step(self@, post@, vm, gpa, entry),
    ;
}

// ───────────────────────── the abstraction relation R ───────────────────────
impl View for HardwareSpec {
    type V = HardwareView;

    /// R: project both hardware translation units into the abstract `HardwareView`.
    /// `memory` and `active_vm` are still governed by the data plane and scheduler, so
    /// they are empty in this token-state projection.
    open spec fn view(&self) -> HardwareView {
        HardwareView {
            tlb: self.mmu.tlb,
            s2map: flatten_s2map(self.mmu.s2map),
            iommu_tlb: self.smmu.tlb,
            iommu_s2map: flatten_s2map(self.smmu.s2map),
            memory: Map::empty(),
            active_vm: Map::empty(),
        }
    }
}

// ───────────────────────── facts about the projection ───────────────────────
/// If `post` differs from `pre` only by removing `gpa` from `vm`'s slice, the
/// flattened map loses exactly the flat key `(vm, gpa)`.
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
/// the flattened map gains exactly the flat key `(vm, gpa)`.
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
/// no cached TLB entry, so an unmap of it is a no-op on both `s2map` and `tlb`.
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
            assert(s.s2map.contains_key(k.vm));
        }
    }
}

// ───────────────────────── the refinement ───────────────────────────────────
impl HardwareRefinement for HardwareSpec {
    open spec fn invariants(&self) -> bool {
        &&& self.mmu.invariant()
        &&& self.smmu.invariant()
    }

    open spec fn map_fresh(&self, vm: VmId, gpa: GuestPage) -> bool {
        &&& self.mmu.s2map.contains_key(vm)
        &&& !self.mmu.s2map[vm].contains_key(gpa)
    }

    open spec fn iommu_map_fresh(&self, vm: VmId, gpa: GuestPage) -> bool {
        &&& self.smmu.s2map.contains_key(vm)
        &&& !self.smmu.s2map[vm].contains_key(gpa)
    }

    broadcast proof fn inv_implies_wf(&self)
        ensures
            #[trigger] self@.wf(),
    {
        let hw = self@;
        assert forall|key: TlbKey| #[trigger] hw.tlb.contains_key(key) implies {
            let sk = VmPageKey::new(key.vm, key.gpa);
            &&& hw.s2map.contains_key(sk)
            &&& hw.tlb[key].as_s2_entry() == hw.s2map[sk]
        } by {
            assert(self.mmu.s2map.contains_key(key.vm));
            assert(self.mmu.s2map[key.vm].contains_key(key.gpa));
        }
        assert forall|key: TlbKey| #[trigger] hw.iommu_tlb.contains_key(key) implies {
            let sk = VmPageKey::new(key.vm, key.gpa);
            &&& hw.iommu_s2map.contains_key(sk)
            &&& hw.iommu_tlb[key].as_s2_entry() == hw.iommu_s2map[sk]
        } by {
            assert(self.smmu.s2map.contains_key(key.vm));
            assert(self.smmu.s2map[key.vm].contains_key(key.gpa));
        }
        assert(hw.tlb_safe());
        assert(hw.iommu_tlb_safe());
    }

    proof fn tlb_invalidate(self, vm: VmId, gpa: GuestPage) -> (post: Self) {
        let mmu_post;
        if self.mmu.s2map.contains_key(vm) {
            mmu_post = MmuSpec::take_step::unmap_invalidate(self.mmu, vm, gpa);
            assert(mmu_post.s2map.dom() =~= self.mmu.s2map.dom());
            assert(mmu_post.s2map[vm] == self.mmu.s2map[vm].remove(gpa));
            lemma_flatten_remove(self.mmu.s2map, mmu_post.s2map, vm, gpa);
        } else {
            lemma_absent_vm_noop(self.mmu, vm, gpa);
            mmu_post = self.mmu;
        }
        let post = HardwareSpec { mmu: mmu_post, smmu: self.smmu };
        assert(HardwareView::unmap_invalidate_step(self@, post@, vm, gpa));
        post
    }

    proof fn map_fence(self, vm: VmId, gpa: GuestPage, entry: S2Entry) -> (post: Self) {
        let mmu_post = MmuSpec::take_step::map(self.mmu, vm, gpa, entry);
        assert(mmu_post.s2map.dom() =~= self.mmu.s2map.dom());
        assert(mmu_post.s2map[vm] == self.mmu.s2map[vm].insert(gpa, entry));
        lemma_flatten_insert(self.mmu.s2map, mmu_post.s2map, vm, gpa, entry);
        let post = HardwareSpec { mmu: mmu_post, smmu: self.smmu };
        assert(HardwareView::map_step(self@, post@, vm, gpa, entry));
        post
    }

    proof fn iommu_tlb_invalidate(self, vm: VmId, gpa: GuestPage) -> (post: Self) {
        let smmu_post;
        if self.smmu.s2map.contains_key(vm) {
            smmu_post = MmuSpec::take_step::unmap_invalidate(self.smmu, vm, gpa);
            assert(smmu_post.s2map.dom() =~= self.smmu.s2map.dom());
            assert(smmu_post.s2map[vm] == self.smmu.s2map[vm].remove(gpa));
            lemma_flatten_remove(self.smmu.s2map, smmu_post.s2map, vm, gpa);
        } else {
            lemma_absent_vm_noop(self.smmu, vm, gpa);
            smmu_post = self.smmu;
        }
        let post = HardwareSpec { mmu: self.mmu, smmu: smmu_post };
        assert(HardwareView::iommu_unmap_invalidate_step(self@, post@, vm, gpa));
        post
    }

    proof fn iommu_map_fence(self, vm: VmId, gpa: GuestPage, entry: S2Entry) -> (post: Self) {
        let smmu_post = MmuSpec::take_step::map(self.smmu, vm, gpa, entry);
        assert(smmu_post.s2map.dom() =~= self.smmu.s2map.dom());
        assert(smmu_post.s2map[vm] == self.smmu.s2map[vm].insert(gpa, entry));
        lemma_flatten_insert(self.smmu.s2map, smmu_post.s2map, vm, gpa, entry);
        let post = HardwareSpec { mmu: self.mmu, smmu: smmu_post };
        assert(HardwareView::iommu_map_step(self@, post@, vm, gpa, entry));
        post
    }
}

} // verus!
