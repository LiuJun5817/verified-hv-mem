use vstd::prelude::*;

use crate::machine::types::*;

verus! {

/// The hardware-controlled portion of the machine state.
///
/// These fields are managed by the hardware (TLB, physical memory, CPU
/// scheduler) or represent in-flight hardware operations (pending TLB
/// invalidations).  They are never stored in exec variables; callers supply
/// them as `Ghost<HwView>` witnesses that are erased at compile time.
pub ghost struct HwView {
    /// Current TLB contents, keyed by `(cpu, vm, gpa)`.
    pub tlb: Map<TlbKey, TlbEntry>,
    /// TLB keys whose invalidation has been broadcast but not yet acknowledged
    /// by all CPUs.
    pub pending_invalidations: Set<TlbKey>,
    /// Physical memory contents at word granularity.
    pub memory: Map<PhysWordAddr, DataWord>,
    /// Which VM is currently scheduled on each CPU.
    pub active_vm: Map<CpuId, VmId>,
}

} // verus!
