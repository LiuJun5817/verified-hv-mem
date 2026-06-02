use vstd::prelude::*;

use super::HwView;
use crate::machine::types::*;

verus! {

// ---------------------------------------------------------------------------
// Hardware-only state transitions
//
// Each `*_step` predicate relates two `HwView` snapshots.  `s1` is the
// pre-state; `s2` is the post-state.  Software state (`SwView`) is absent —
// cross-cutting effects that span both views are composed in
// `machine::machine::refine`.
// ---------------------------------------------------------------------------
impl HwView {
    /// Mark any TLB entries for `(vm, gpa)` as pending invalidation.
    ///
    /// Called alongside a software map/unmap step.  The actual TLB shootdown
    /// is performed later via [`tlbi_step`].
    pub open spec fn pending_invalidation_step(s1: HwView, s2: HwView, vm: VmId, gpa: GuestPage) -> bool {
        let targets = Set::new(
            |key: TlbKey| key.vm == vm && key.gpa == gpa && s1.tlb.contains_key(key),
        );
        &&& s2.pending_invalidations == s1.pending_invalidations.union(targets)
        &&& s2.tlb == s1.tlb
        &&& s2.active_vm == s1.active_vm
        &&& s2.memory == s1.memory
    }

    /// Hardware MMU silently fills the TLB with a stage-2 PTE.
    ///
    /// `s2_map` is provided as an argument because the TLB fill reads the
    /// current page-table contents, which live in the software state.
    pub open spec fn tlb_fill_step(
        s1: HwView,
        s2: HwView,
        s2_map: Map<VmPageKey, S2Entry>,
        cpu: CpuId,
        vm: VmId,
        gpa: GuestPage,
    ) -> bool {
        let tkey = TlbKey::new(cpu, vm, gpa);
        let skey = VmPageKey::new(vm, gpa);
        &&& s1.active_vm.contains_key(cpu) && s1.active_vm[cpu] == vm
        &&& s2_map.contains_key(skey)
        &&& !s1.pending_invalidations.contains(tkey)
        &&& s2.pending_invalidations == s1.pending_invalidations
        &&& s2.active_vm == s1.active_vm
        &&& s2.memory == s1.memory
        &&& s2.tlb == s1.tlb.insert(
            tkey,
            TlbEntry {
                page: s2_map[skey].page,
                access: s2_map[skey].access,
                generation: s2_map[skey].generation,
            },
        )
    }

    /// Remove a single TLB entry for `(cpu, vm, gpa)` and clear its pending
    /// flag.
    ///
    /// On AArch64: this is the effect of one `TLBI IPAS2E1IS` acknowledgement.
    pub open spec fn tlbi_step(s1: HwView, s2: HwView, cpu: CpuId, vm: VmId, gpa: GuestPage) -> bool {
        let tkey = TlbKey::new(cpu, vm, gpa);
        &&& s2.tlb == s1.tlb.remove(tkey)
        &&& s2.pending_invalidations == s1.pending_invalidations.remove(tkey)
        &&& s2.active_vm == s1.active_vm
        &&& s2.memory == s1.memory
    }

    /// Schedule `vm` onto `cpu`.
    ///
    /// On AArch64: writing `VTTBR_EL2` before `ERET`.
    pub open spec fn context_switch_step(s1: HwView, s2: HwView, cpu: CpuId, vm: VmId) -> bool {
        &&& s2.active_vm == s1.active_vm.insert(cpu, vm)
        &&& s2.tlb == s1.tlb
        &&& s2.pending_invalidations == s1.pending_invalidations
        &&& s2.memory == s1.memory
    }

    /// Data Synchronization Barrier — no observable state change.
    ///
    /// The ordering guarantee is captured by the barrier consistency predicate
    /// in `machine::machine`; at the state-machine level DSB is a no-op.
    pub open spec fn dsb_step(s1: HwView, s2: HwView) -> bool {
        s2 == s1
    }

    /// Instruction Synchronization Barrier — no observable state change.
    pub open spec fn isb_step(s1: HwView, s2: HwView) -> bool {
        s2 == s1
    }
}

} // verus!
