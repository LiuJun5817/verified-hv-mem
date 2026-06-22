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
/// ## Barriers carry no abstract state — break-before-make is a TCB obligation
///
/// At the `HwView`-state level TLB invalidation is folded into the **synchronous**
/// flush of `MachineState::{hv_map,hv_unmap}_step`, so the barriers (`DSB`, `ISB`)
/// change no abstract state ([`HwView::dsb_step`] / [`HwView::isb_step`] are the
/// identity).  Consequently the model does **not** enforce that running code emits
/// the break-before-make sequence (`PTE-write-invalid → DSB ISH → TLBI IPAS2E1IS →
/// DSB ISH`) or that reclaim waits for completion.  That ordering is an explicit
/// **implementation / TCB obligation** — trusted at the same boundary as the
/// `asm!` strings themselves — and is documented at `hv_unmap_step` /
/// `page_is_quiescent`.  (Turning the back half of that sequence into a real
/// theorem would require the async/pending `HwView` revision; the first `DSB`
/// — PTE write becoming visible to table walkers — is uncapturable at this
/// modeling altitude, since `tlb_fill_step` already reads the updated `s2_map`.)
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
    /// On AArch64: a single `TLBI IPAS2E1IS, Xt` instruction.  Because it is
    /// inner-shareable it is a *broadcast* — one instruction removes the cached
    /// `(*, vm, gpa)` entries on **every** PE — so it takes no per-CPU argument;
    /// its whole-domain effect is [`HwView::tlbi_ipa_broadcast_step`] (the per-CPU
    /// [`HwView::tlbi_step`] is only an internal model of a single PE's
    /// acknowledgement, not exposed as an instruction).  It must be followed by a
    /// completion `DSB ISH` ([`issue_dsb_ish`](HardwareOps::issue_dsb_ish)) before
    /// the new translation may be relied upon (see the trait-level note).
    ///
    /// `IPAS2E1IS` is a **register-form** maintenance op: the target IPA travels in
    /// `Xt` as `Xt[..] = IPA >> 12`, which for the model's 4K pages is exactly the
    /// guest page number.  Hence the real `usize` operand `ipa_page`; the spec page
    /// identity is `GuestPage(ipa_page as nat)`, so the trusted body cannot claim to
    /// invalidate a page other than the one the instruction actually targets.  The
    /// VMID is *not* an operand — it is read from the current `VTTBR_EL2`, which the
    /// caller must already have set to `vm`.
    fn issue_tlbi_s2(&self, ipa_page: usize, vm: Ghost<VmId>, hw: Ghost<HwView>) -> (hw_post: Ghost<
        HwView,
    >)
        ensures
            HwView::tlbi_ipa_broadcast_step(hw@, hw_post@, vm@, GuestPage(ipa_page as nat)),
    ;

    // ------------------------------------------------------------------
    // Data Synchronization Barrier (DSB ISH)
    // ------------------------------------------------------------------
    /// Issue a Data Synchronization Barrier in the inner-shareable domain.
    ///
    /// On AArch64: `DSB ISH`.  It does not retire until the preceding
    /// `TLBI IPAS2E1IS` has completed on every PE in the domain.  No abstract state
    /// change ([`HwView::dsb_step`] is the identity).
    fn issue_dsb_ish(&self, hw: Ghost<HwView>) -> (hw_post: Ghost<HwView>)
        ensures
            HwView::dsb_step(hw@, hw_post@),
    ;

    // ------------------------------------------------------------------
    // Instruction Synchronization Barrier (ISB)
    // ------------------------------------------------------------------
    /// Issue an Instruction Synchronization Barrier.
    ///
    /// On AArch64: `ISB`.  Synchronizes only the executing PE's own context.  No
    /// abstract state change ([`HwView::isb_step`] is the identity).
    fn issue_isb(&self, hw: Ghost<HwView>) -> (hw_post: Ghost<HwView>)
        ensures
            HwView::isb_step(hw@, hw_post@),
    ;
}

} // verus!
