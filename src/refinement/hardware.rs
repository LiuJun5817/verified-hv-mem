//! Hardware-refinement layer: `impl HardwareRefinement for HardwareSpec`.
//!
//! [`HardwareSpec`] is the hardware-side abstraction carrier: a pair of regime-neutral
//! `MmuSpec::State` instances, one for the CPU MMU and one for the SMMU/IOMMU.  The
//! projection into [`HardwareView`] exposes both walker-reachable maps and both TLBs.
//! This avoids having two competing `View` impls for `MmuSpec::State` while keeping the
//! MMU state machine itself shared between CPU and IOMMU.
use vstd::prelude::*;

verus! {

use crate::hardware::spec::{MmuSpec, MmuVmState};
use crate::model::hardware::HardwareView;
use crate::model::types::{GuestPage, S2Entry, TlbKey, VmId, VmPageKey};
use crate::model::convert::*;

/// The pair of hardware-side tokenized states: CPU MMU plus SMMU/IOMMU.
pub ghost struct HardwareSpec {
    pub mmu: MmuSpec::State,
    pub smmu: MmuSpec::State,
}

/// Project the compound VM shards to the previous per-VM reachable-map shape.
pub open spec fn vm_s2maps(
    vms: Map<VmId, MmuVmState>,
) -> Map<VmId, Map<GuestPage, S2Entry>> {
    Map::new(|vm: VmId| vms.contains_key(vm), |vm: VmId| vms[vm].s2map)
}

/// Flatten all per-VM reachable mappings into machine keys.
pub open spec fn flatten_vm_s2(vms: Map<VmId, MmuVmState>) -> Map<VmPageKey, S2Entry> {
    flatten_s2map(vm_s2maps(vms))
}

/// Flatten all per-VM TLB shards into the hardware TLB map.
pub open spec fn flatten_vm_tlb(vms: Map<VmId, MmuVmState>) -> Map<TlbKey, crate::model::types::TlbEntry> {
    Map::new(
        |key: TlbKey| vms.contains_key(key.vm) && vms[key.vm].tlb.contains_key(key),
        |key: TlbKey| vms[key.vm].tlb[key],
    )
}

proof fn lemma_flatten_vm_tlb_same(
    pre: Map<VmId, MmuVmState>,
    post: Map<VmId, MmuVmState>,
)
    requires
        post.dom() == pre.dom(),
        forall|vm: VmId| #[trigger] pre.contains_key(vm)
            ==> post[vm].tlb == pre[vm].tlb,
    ensures
        flatten_vm_tlb(post) == flatten_vm_tlb(pre),
{
    assert(flatten_vm_tlb(post) =~= flatten_vm_tlb(pre)) by {
        assert forall|key: TlbKey| #[trigger]
            flatten_vm_tlb(post).contains_key(key)
                == flatten_vm_tlb(pre).contains_key(key) by {
        }
    }
}

proof fn lemma_flatten_vm_tlb_remove(
    pre: Map<VmId, MmuVmState>,
    post: Map<VmId, MmuVmState>,
    vm: VmId,
    gpa: GuestPage,
)
    requires
        pre.contains_key(vm),
        post.dom() == pre.dom(),
        post[vm].tlb == pre[vm].tlb.remove_keys(
            Set::new(|key: TlbKey| key.vm == vm && key.gpa == gpa),
        ),
        forall|v: VmId| #[trigger] pre.contains_key(v) && v != vm
            ==> post[v].tlb == pre[v].tlb,
        forall|v: VmId| #[trigger] pre.contains_key(v) ==> pre[v].coherent(v),
    ensures
        flatten_vm_tlb(post) == flatten_vm_tlb(pre).remove_keys(
            Set::new(|key: TlbKey| key.vm == vm && key.gpa == gpa),
        ),
{
    let targets = Set::new(|key: TlbKey| key.vm == vm && key.gpa == gpa);
    assert(flatten_vm_tlb(post) =~= flatten_vm_tlb(pre).remove_keys(targets)) by {
        assert forall|key: TlbKey| #[trigger]
            flatten_vm_tlb(post).contains_key(key)
                == flatten_vm_tlb(pre).remove_keys(targets).contains_key(key) by {
            if pre.contains_key(key.vm) && key.vm != vm {
                assert(!pre[vm].tlb.contains_key(key)) by {
                    if pre[vm].tlb.contains_key(key) {
                        assert(key.vm == vm);
                    }
                }
            }
        }
    }
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
    /// `memory` is governed by the data plane, so it is empty in this token-state
    /// projection.
    open spec fn view(&self) -> HardwareView {
        HardwareView {
            tlb: flatten_vm_tlb(self.mmu.vms),
            s2map: flatten_vm_s2(self.mmu.vms),
            iommu_tlb: flatten_vm_tlb(self.smmu.vms),
            iommu_s2map: flatten_vm_s2(self.smmu.vms),
            memory: Map::empty(),
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
        !s.vms.contains_key(vm),
    ensures
        flatten_vm_s2(s.vms).remove(VmPageKey::new(vm, gpa)) == flatten_vm_s2(s.vms),
        flatten_vm_tlb(s.vms).remove_keys(
            Set::new(|key: TlbKey| key.vm == vm && key.gpa == gpa),
        ) == flatten_vm_tlb(s.vms),
{
    let targets = Set::new(|key: TlbKey| key.vm == vm && key.gpa == gpa);
    assert(!flatten_vm_s2(s.vms).contains_key(VmPageKey::new(vm, gpa)));
    assert(flatten_vm_s2(s.vms).remove(VmPageKey::new(vm, gpa)) =~= flatten_vm_s2(s.vms));
    assert(flatten_vm_tlb(s.vms).remove_keys(targets) =~= flatten_vm_tlb(s.vms)) by {
        assert forall|k: TlbKey| #[trigger] flatten_vm_tlb(s.vms).contains_key(k)
            implies !targets.contains(k) by {
            assert(s.vms.contains_key(k.vm));
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
        &&& self.mmu.vms.contains_key(vm)
        &&& !self.mmu.vms[vm].s2map.contains_key(gpa)
    }

    open spec fn iommu_map_fresh(&self, vm: VmId, gpa: GuestPage) -> bool {
        &&& self.smmu.vms.contains_key(vm)
        &&& !self.smmu.vms[vm].s2map.contains_key(gpa)
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
            assert(self.mmu.vms.contains_key(key.vm));
            assert(self.mmu.vms[key.vm].s2map.contains_key(key.gpa));
        }
        assert forall|key: TlbKey| #[trigger] hw.iommu_tlb.contains_key(key) implies {
            let sk = VmPageKey::new(key.vm, key.gpa);
            &&& hw.iommu_s2map.contains_key(sk)
            &&& hw.iommu_tlb[key].as_s2_entry() == hw.iommu_s2map[sk]
        } by {
            assert(self.smmu.vms.contains_key(key.vm));
            assert(self.smmu.vms[key.vm].s2map.contains_key(key.gpa));
        }
        assert(hw.tlb_safe());
        assert(hw.iommu_tlb_safe());
    }

    proof fn tlb_invalidate(self, vm: VmId, gpa: GuestPage) -> (post: Self) {
        let mmu_post;
        if self.mmu.vms.contains_key(vm) {
            mmu_post = MmuSpec::take_step::unmap_invalidate(self.mmu, vm, gpa);
            assert(vm_s2maps(mmu_post.vms).dom() =~= vm_s2maps(self.mmu.vms).dom());
            assert(vm_s2maps(mmu_post.vms)[vm]
                == vm_s2maps(self.mmu.vms)[vm].remove(gpa));
            lemma_flatten_remove(
                vm_s2maps(self.mmu.vms), vm_s2maps(mmu_post.vms), vm, gpa,
            );
            assert(mmu_post.vms.dom() =~= self.mmu.vms.dom());
            assert(mmu_post.vms[vm].tlb == self.mmu.vms[vm].tlb.remove_keys(
                Set::new(|key: TlbKey| key.vm == vm && key.gpa == gpa),
            ));
            lemma_flatten_vm_tlb_remove(self.mmu.vms, mmu_post.vms, vm, gpa);
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
        assert(vm_s2maps(mmu_post.vms).dom() =~= vm_s2maps(self.mmu.vms).dom());
        assert(vm_s2maps(mmu_post.vms)[vm]
            == vm_s2maps(self.mmu.vms)[vm].insert(gpa, entry));
        lemma_flatten_insert(
            vm_s2maps(self.mmu.vms), vm_s2maps(mmu_post.vms), vm, gpa, entry,
        );
        assert(mmu_post.vms.dom() =~= self.mmu.vms.dom());
        lemma_flatten_vm_tlb_same(self.mmu.vms, mmu_post.vms);
        let post = HardwareSpec { mmu: mmu_post, smmu: self.smmu };
        assert(HardwareView::map_step(self@, post@, vm, gpa, entry));
        post
    }

    proof fn iommu_tlb_invalidate(self, vm: VmId, gpa: GuestPage) -> (post: Self) {
        let smmu_post;
        if self.smmu.vms.contains_key(vm) {
            smmu_post = MmuSpec::take_step::unmap_invalidate(self.smmu, vm, gpa);
            assert(vm_s2maps(smmu_post.vms).dom() =~= vm_s2maps(self.smmu.vms).dom());
            assert(vm_s2maps(smmu_post.vms)[vm]
                == vm_s2maps(self.smmu.vms)[vm].remove(gpa));
            lemma_flatten_remove(
                vm_s2maps(self.smmu.vms), vm_s2maps(smmu_post.vms), vm, gpa,
            );
            assert(smmu_post.vms.dom() =~= self.smmu.vms.dom());
            assert(smmu_post.vms[vm].tlb == self.smmu.vms[vm].tlb.remove_keys(
                Set::new(|key: TlbKey| key.vm == vm && key.gpa == gpa),
            ));
            lemma_flatten_vm_tlb_remove(self.smmu.vms, smmu_post.vms, vm, gpa);
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
        assert(vm_s2maps(smmu_post.vms).dom() =~= vm_s2maps(self.smmu.vms).dom());
        assert(vm_s2maps(smmu_post.vms)[vm]
            == vm_s2maps(self.smmu.vms)[vm].insert(gpa, entry));
        lemma_flatten_insert(
            vm_s2maps(self.smmu.vms), vm_s2maps(smmu_post.vms), vm, gpa, entry,
        );
        assert(smmu_post.vms.dom() =~= self.smmu.vms.dom());
        lemma_flatten_vm_tlb_same(self.smmu.vms, smmu_post.vms);
        let post = HardwareSpec { mmu: self.mmu, smmu: smmu_post };
        assert(HardwareView::iommu_map_step(self@, post@, vm, gpa, entry));
        post
    }
}

} // verus!
