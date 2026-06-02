use vstd::prelude::*;

use super::HwView;
use crate::machine::types::*;

verus! {

/// Trusted contracts for hardware-level instructions.
///
/// Each method is an exec `fn` that can appear in hypervisor code.  Ghost
/// parameters carry the hardware state for spec-level reasoning; they are
/// erased at compile time.
///
/// Platform implementations provide `#[verifier::external_body]` bodies
/// containing the actual `asm!` instructions, citing the architecture
/// reference manual for correctness.
///
/// ## Stage-2 PTE writes
///
/// PTE writes are hypervisor software operations performed through
/// `PageTableMem`.  They belong to the [`super::super::software`] layer and
/// must not appear here.
pub trait HardwareOps: Sized {
    // ------------------------------------------------------------------
    // S2 TLB invalidation broadcast
    // ------------------------------------------------------------------
    /// Broadcast a TLB invalidation for the entry `(cpu, vm, gpa)`.
    ///
    /// On AArch64: `TLBI IPAS2E1IS`.  Must be bracketed by `DSB ISH`
    /// (before) and a completion `DSB ISH` (after) to ensure ordering
    /// and visibility.
    fn issue_tlbi_s2(
        &self,
        cpu: Ghost<CpuId>,
        vm: Ghost<VmId>,
        gpa: Ghost<GuestPage>,
        hw: Ghost<HwView>,
    ) -> (hw_post: Ghost<HwView>)
        ensures
            HwView::tlbi_step(hw@, hw_post@, cpu@, vm@, gpa@),
    ;

    // ------------------------------------------------------------------
    // Data Synchronization Barrier (DSB ISH)
    // ------------------------------------------------------------------
    /// Issue a Data Synchronization Barrier in the inner-shareable domain.
    ///
    /// On AArch64: `DSB ISH`.
    fn issue_dsb_ish(&self, hw: Ghost<HwView>) -> (hw_post: Ghost<HwView>)
        ensures
            HwView::dsb_step(hw@, hw_post@),
    ;

    // ------------------------------------------------------------------
    // Instruction Synchronization Barrier (ISB)
    // ------------------------------------------------------------------
    /// Issue an Instruction Synchronization Barrier.
    ///
    /// On AArch64: `ISB`.
    fn issue_isb(&self, hw: Ghost<HwView>) -> (hw_post: Ghost<HwView>)
        ensures
            HwView::isb_step(hw@, hw_post@),
    ;
}

} // verus!
