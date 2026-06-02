use vstd::prelude::*;

use super::state::MachineState;
use crate::machine::types::*;

verus! {

impl MachineState {
    /// **Th1 — Integrity**
    ///
    /// If a guest-virtual address `gva` is readable by the subject VM in state
    /// `s1` and its backing physical page is subject-private, then after any
    /// single environment-VM step to `s2` the subject VM reads the same value
    /// at `gva`.
    ///
    /// Proof obligation: `admit()` — to be discharged once the full step
    /// invariants are in place.
    pub proof fn lemma_integrity(s1: MachineState, s2: MachineState, cpu: CpuId, gva: GuestWordAddr)
        requires
            s1.wf(),
            Self::env_reachable(s1, s2),
            s1.read_observation(cpu, s1.subject, gva) is Some,
            s1.subject_private_page(s1.effective_entry(cpu, s1.subject, gva.page())->Some_0.page),
        ensures
            s2.read_observation(cpu, s2.subject, gva) == s1.read_observation(cpu, s1.subject, gva),
    {
        admit()
    }

    /// **Th2 — Confidentiality**
    ///
    /// Given a subject-private physical page `page` in `s1`, after any single
    /// environment-VM step to `s2`, environment VM `vm` cannot read out the
    /// content stored in `page`: any successful read by `vm` resolves to a
    /// different physical page.
    ///
    /// Proof obligation: `admit()` — to be discharged once the full step
    /// invariants are in place.
    pub proof fn lemma_confidentiality(
        s1: MachineState,
        s2: MachineState,
        page: PhysPage,
        vm: VmId,
        cpu: CpuId,
        gva: GuestWordAddr,
    )
        requires
            s1.wf(),
            Self::env_reachable(s1, s2),
            s1.subject_private_page(page),
            s1.environment_vms.contains(vm),
            s2.read_observation(cpu, vm, gva) is Some,
        ensures
            s2.translated_word(cpu, vm, gva)->Some_0.page() != page,
    {
        admit()
    }
}

} // verus!
