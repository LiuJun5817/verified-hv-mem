use super::state::MachineState;
use crate::model::types::{CpuId, GuestPage, MachineAction, PhysPage, TlbKey, VmId, VmPageKey};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// CPU and DMA isolation on the abstract `MachineState`.
//
// The public proof surface is the two paper-facing reachable-state theorems:
// `lemma_cpu_isolation` and `lemma_dma_isolation`. Their shared structure is:
//
//   reachable -> wf -> effective translation is policy-authorized
//                    -> cross-VM policy separation
// ---------------------------------------------------------------------------
impl MachineState {
    /// The empty initial machine state is well formed.
    proof fn lemma_init_wf(s: MachineState)
        requires
            MachineState::init(s),
        ensures
            s.wf(),
    {
        assert(s.vm_owned.dom() =~= s.all_vms());
        assert(s.ownership_wf());
        assert(s.translation_wf());
        assert(s.tlb_safe());
    }

    /// Every state visited by an execution from a well-formed start is well formed.
    proof fn lemma_execution_wf(trace: Seq<MachineState>, acts: Seq<MachineAction>, k: int)
        requires
            MachineState::is_execution(trace, acts),
            trace[0].wf(),
            0 <= k < trace.len(),
        ensures
            trace[k].wf(),
    {
        assert(trace.len() == acts.len() + 1);
        if k > 0 {
            let i = k - 1;
            assert(0 <= i < acts.len());
            assert(MachineState::step(trace[i], trace[i + 1], acts[i]));
            assert(trace[i + 1].wf());
            assert(trace[i + 1] == trace[k]);
        }
    }

    /// Every state reachable from `init` is well formed.
    proof fn lemma_reachable_wf(s: MachineState)
        requires
            MachineState::reachable(s),
        ensures
            s.wf(),
    {
        let (trace, acts) = choose|trace: Seq<MachineState>, acts: Seq<MachineAction>|
            {
                &&& MachineState::is_execution(trace, acts)
                &&& MachineState::init(trace[0])
                &&& trace[trace.len() - 1] == s
            };
        assert(trace.len() == acts.len() + 1);
        Self::lemma_init_wf(trace[0]);
        Self::lemma_execution_wf(trace, acts, trace.len() - 1);
    }

    /// In a well-formed state, a successful effective CPU translation targets
    /// either an S2-private page of the translating VM or an installed S2-shared
    /// page. `tlb_safe` connects a cached entry to the hardware-reachable map,
    /// `sync` connects that map to the software map, and `translation_wf`
    /// supplies the policy classification.
    proof fn lemma_cpu_translation_authorized(
        s: MachineState,
        cpu: CpuId,
        vm: VmId,
        gpa: GuestPage,
        page: PhysPage,
    )
        requires
            s.wf(),
            s.cpu_translates_to(cpu, vm, gpa, page),
        ensures
            s.s2_private(vm, page) || s.s2_shared(page),
    {
        let key = TlbKey::new(cpu, vm, gpa);
        let sk = VmPageKey::new(vm, gpa);
        assert(s.effective_entry(cpu, vm, gpa) is Some);
        assert(s.effective_entry(cpu, vm, gpa)->Some_0.page == page);
        assert(s.s2_map.contains_key(sk) && s.s2_map[sk].page == page) by {
            assert(s.sync());
            if s.tlb.contains_key(key) {
                assert(s.tlb_safe());
            }
        }
        assert(s.translation_wf());
        assert(s.all_vms().contains(vm));
        assert(s.owned_or_shared(vm, page));
        if s.vm_owned.contains_key(vm) && s.vm_owned[vm].contains(page) {
            assert(s.ownership_wf());
            assert(!s.vm_shared.contains(page));
            assert(s.s2_private(vm, page));
        } else {
            assert(s.vm_shared.contains(page));
            assert(s.s2_shared(page));
        }
    }

    /// Cross-VM S2-private sets are disjoint, and an S2-private page is outside
    /// the installed all-VM-shared projection.
    proof fn lemma_s2_target_excludes_other_private(
        s: MachineState,
        subject: VmId,
        protected: PhysPage,
        other: VmId,
        target: PhysPage,
    )
        requires
            s.wf(),
            other != subject,
            s.s2_private(subject, protected),
            s.s2_private(other, target) || s.s2_shared(target),
        ensures
            target != protected,
    {
        if target == protected {
            if s.s2_private(other, target) {
                assert(s.ownership_wf());
                assert(!s.vm_owned[other].contains(protected));
                assert(false);
            } else {
                assert(s.s2_shared(target));
                assert(s.vm_shared.contains(protected));
                assert(false);
            }
        }
    }

    /// CPU isolation. In every reachable state, an environment VM cannot
    /// translate any guest page to an S2-private page of the subject. The explicit
    /// `cpu` parameter accounts for every per-CPU cached translation represented by
    /// the machine model.
    pub proof fn lemma_cpu_isolation(
        s: MachineState,
        subject: VmId,
        protected: PhysPage,
        environment: VmId,
        cpu: CpuId,
        gpa: GuestPage,
        target: PhysPage,
    )
        requires
            MachineState::reachable(s),
            environment != subject,
            s.s2_private(subject, protected),
            s.cpu_translates_to(cpu, environment, gpa, target),
        ensures
            target != protected,
    {
        Self::lemma_reachable_wf(s);
        Self::lemma_cpu_translation_authorized(s, cpu, environment, gpa, target);
        Self::lemma_s2_target_excludes_other_private(
            s,
            subject,
            protected,
            environment,
            target,
        );
    }

    /// In a well-formed state, a successful effective DMA translation targets
    /// either an IOMMU-private page of the translating VM or an installed
    /// IOMMU-shared page. `iommu_tlb_safe`, `iommu_sync`, and
    /// `iommu_translation_wf` establish the classification.
    proof fn lemma_dma_translation_authorized(
        s: MachineState,
        stream: CpuId,
        vm: VmId,
        iova: GuestPage,
        page: PhysPage,
    )
        requires
            s.wf(),
            s.dma_translates_to(stream, vm, iova, page),
        ensures
            s.iommu_private(vm, page) || s.iommu_shared_page(page),
    {
        let key = TlbKey::new(stream, vm, iova);
        let sk = VmPageKey::new(vm, iova);
        assert(s.iommu_effective_entry(stream, vm, iova) is Some);
        assert(s.iommu_effective_entry(stream, vm, iova)->Some_0.page == page);
        assert(s.iommu_s2_map.contains_key(sk) && s.iommu_s2_map[sk].page == page) by {
            assert(s.iommu_sync());
            if s.iommu_tlb.contains_key(key) {
                assert(s.iommu_tlb_safe());
            }
        }
        assert(s.iommu_translation_wf());
        assert(s.all_vms().contains(vm));
        assert(s.iommu_owned.contains_key(vm));
        if s.iommu_owned[vm].contains(page) {
            assert(s.iommu_ownership_wf());
            assert(!s.iommu_shared.contains(page));
            assert(s.iommu_private(vm, page));
        } else {
            assert(s.iommu_shared.contains(page));
            assert(s.iommu_shared_page(page));
        }
    }

    /// A different VM's DMA-authorized target cannot be either an IOMMU-private
    /// or an S2-private page of the subject. The four clauses of
    /// `iommu_ownership_wf` cover private-IOMMU/private-IOMMU,
    /// private-IOMMU/private-S2, and both private/shared cases.
    proof fn lemma_dma_target_excludes_other_private(
        s: MachineState,
        subject: VmId,
        protected: PhysPage,
        other: VmId,
        target: PhysPage,
    )
        requires
            s.wf(),
            other != subject,
            s.iommu_private(subject, protected) || s.s2_private(subject, protected),
            s.iommu_private(other, target) || s.iommu_shared_page(target),
        ensures
            target != protected,
    {
        if target == protected {
            assert(s.iommu_ownership_wf());
            if s.iommu_private(other, target) {
                if s.iommu_private(subject, protected) {
                    assert(!s.iommu_owned[other].contains(protected));
                    assert(false);
                } else {
                    assert(s.s2_private(subject, protected));
                    assert(!s.vm_owned[subject].contains(protected));
                    assert(false);
                }
            } else {
                assert(s.iommu_shared_page(target));
                assert(s.iommu_shared.contains(protected));
                if s.iommu_private(subject, protected) {
                    assert(false);
                } else {
                    assert(s.s2_private(subject, protected));
                    assert(false);
                }
            }
        }
    }

    /// DMA isolation. In every reachable state, a device assigned to an
    /// environment VM cannot translate any IOVA page to either an IOMMU-private
    /// or an S2-private page of the subject. The explicit `stream` parameter
    /// accounts for every cached SMMU translation represented by the model.
    pub proof fn lemma_dma_isolation(
        s: MachineState,
        subject: VmId,
        protected: PhysPage,
        environment: VmId,
        stream: CpuId,
        iova: GuestPage,
        target: PhysPage,
    )
        requires
            MachineState::reachable(s),
            environment != subject,
            s.dma_translates_to(stream, environment, iova, target),
            s.iommu_private(subject, protected) || s.s2_private(subject, protected),
        ensures
            target != protected,
    {
        Self::lemma_reachable_wf(s);
        Self::lemma_dma_translation_authorized(s, stream, environment, iova, target);
        Self::lemma_dma_target_excludes_other_private(
            s,
            subject,
            protected,
            environment,
            target,
        );
    }
}

} // verus!
