use vstd::prelude::*;

use super::state::MachineState;
use crate::machine::types::*;

verus! {

impl MachineState {
    /// `s2` is reachable from `s1` by one step of some VM *other than* `subject`.
    /// The subject-vs-environment split exists only here, to state isolation; it
    /// is not part of the machine state.
    pub open spec fn env_reachable(s1: MachineState, s2: MachineState, subject: VmId) -> bool {
        exists|vm: VmId, op: VmMemOp| vm != subject && #[trigger] MachineState::vm_step(s1, s2, vm, op)
    }

    /// **Th1 — Integrity**
    ///
    /// If a guest-virtual address `gva` is readable by the `subject` VM in state
    /// `s1` and its backing physical page is subject-private, then after any
    /// single environment-VM step to `s2` the subject reads the same value.
    ///
    /// Proof obligation: `admit()` — to be discharged once the step invariants are
    /// in place.
    pub proof fn lemma_integrity(
        s1: MachineState,
        s2: MachineState,
        subject: VmId,
        cpu: CpuId,
        gva: GuestWordAddr,
    )
        requires
            s1.wf(),
            s1.all_vms().contains(subject),
            Self::env_reachable(s1, s2, subject),
            s1.read_observation(cpu, subject, gva) is Some,
            s1.private_page(subject, s1.effective_entry(cpu, subject, gva.page())->Some_0.page),
        ensures
            s2.read_observation(cpu, subject, gva) == s1.read_observation(cpu, subject, gva),
    {
        admit()
    }

    /// **Th2 — Confidentiality**
    ///
    /// Given a subject-private physical page `page` in `s1`, after any single
    /// environment-VM step to `s2`, an environment VM `vm` cannot read out the
    /// content of `page`: any successful read by `vm` resolves elsewhere.
    ///
    /// Proof obligation: `admit()` — to be discharged once the step invariants are
    /// in place.
    pub proof fn lemma_confidentiality(
        s1: MachineState,
        s2: MachineState,
        subject: VmId,
        page: PhysPage,
        vm: VmId,
        cpu: CpuId,
        gva: GuestWordAddr,
    )
        requires
            s1.wf(),
            s1.all_vms().contains(subject),
            Self::env_reachable(s1, s2, subject),
            s1.private_page(subject, page),
            s1.all_vms().contains(vm),
            vm != subject,
            s2.read_observation(cpu, vm, gva) is Some,
        ensures
            s2.translated_word(cpu, vm, gva)->Some_0.page() != page,
    {
        admit()
    }
}

} // verus!
