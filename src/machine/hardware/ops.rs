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
    /// Broadcast a stage-2 TLB invalidation for the IPA `(vm, gpa)` across every
    /// PE in the inner-shareable domain.
    ///
    /// On AArch64: a single `TLBI IPAS2E1IS` instruction.  Because it is
    /// inner-shareable it is a *broadcast* — one instruction removes the cached
    /// `(*, vm, gpa)` entries on **every** PE — so it takes no per-CPU argument;
    /// its whole-domain effect is [`HwView::tlbi_ipa_broadcast_step`] (the per-CPU
    /// [`HwView::tlbi_step`] is only an internal model of a single PE's
    /// acknowledgement, not exposed as an instruction).  Must be followed by a
    /// completion `DSB ISH` ([`issue_dsb_ish`]) before the new translation may be
    /// relied upon; together they realize the synchronous flush of
    /// `MachineState::hv_map_step` / `hv_unmap_step` (see `machine::machine::refine`).
    fn issue_tlbi_s2(
        &self,
        vm: Ghost<VmId>,
        gpa: Ghost<GuestPage>,
        hw: Ghost<HwView>,
    ) -> (hw_post: Ghost<HwView>)
        ensures
            HwView::tlbi_ipa_broadcast_step(hw@, hw_post@, vm@, gpa@),
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
