use vstd::prelude::*;

use crate::machine::types::*;

verus! {

/// The concrete, execution-visible substrate of running guests.
///
/// `HwView` holds the part of the machine a VM — or the security property —
/// can *observe or perturb*: the data memory reachable through translation, the
/// TLB that caches translations and may lag a mapping edit, and the per-CPU VM
/// schedule.  Everything *authoritative* (ownership, the intended mapping
/// `s2_map`, the memory partition) is policy and lives in
/// [`crate::machine::software::SwView`].
///
/// # The MMU is split deliberately, and the halves meet at `s2_map`
///
/// An MMU is a *page-table walk* plus a *TLB*.  These are different kinds of
/// thing, so they live in different layers:
///
/// * The **walk** is a stateless function `memory → mapping`.  It has nothing to
///   persist, so it is modelled as a *refinement*, not as state: the
///   `page_table` module's `view` (`ExPageTable → PageTableState`) **is** the
///   walk, and its result is exactly `SwView::s2_map`.  Re-encoding it here would
///   either assume the memory→mapping link (no assurance) or re-derive the walk
///   over flat memory (breaking the abstraction), so it is intentionally absent.
/// * The **TLB** is a *stateful* cache of that result that can go **stale** —
///   which is the whole reason it needs first-class state and a coherence
///   invariant (`MachineState::tlb_safe`).  Hence it lives here.
///
/// They join at `s2_map`: the walk produces it; the TLB caches it; `tlb_safe`
/// says the cache agrees with it.  The model fills the TLB from `s2_map`
/// (not from raw page-table bytes), which is sound precisely because
/// `s2_map == walk(memory)` by the `page_table` refinement.
///
/// These fields are never stored in exec variables; callers supply them as
/// `Ghost<HwView>` witnesses that are erased at compile time.
pub ghost struct HwView {
    /// Current TLB contents, keyed by `(cpu, vm, gpa)`.
    pub tlb: Map<TlbKey, TlbEntry>,
    /// TLB keys whose invalidation has been broadcast but not yet acknowledged
    /// by all CPUs.
    pub pending_invalidations: Set<TlbKey>,
    /// The VM-observable **data plane**: physical memory values at addresses that
    /// translations resolve to (VM-owned ∪ shared pages).  This is *not* a model
    /// of all DRAM — page-table bytes and hypervisor-internal memory are
    /// abstracted into `SwView` (`s2_map`, ownership) and realized only in the
    /// implementation, tied back by the refinement layers.
    pub memory: Map<PhysWordAddr, DataWord>,
    /// Which VM is currently scheduled on each CPU.
    pub active_vm: Map<CpuId, VmId>,
}

impl HwView {
    /// Hardware well-formedness: every pending invalidation refers to a TLB entry
    /// that is actually cached.
    ///
    /// This is the pure-hardware invariant.  Cross-cutting TLB coherence
    /// (`tlb_safe`) additionally relates the TLB to the software `s2_map`, so it
    /// lives at the assembled `MachineState` rather than here.
    pub open spec fn wf(&self) -> bool {
        forall|key: TlbKey| #[trigger]
            self.pending_invalidations.contains(key) ==> self.tlb.contains_key(key)
    }
}

} // verus!
