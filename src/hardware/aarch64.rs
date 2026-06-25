//! AArch64 realization of the [`HardwareOps`] trust contract.
//!
//! Each method wraps a real maintenance / barrier instruction in an
//! `#[verifier::external_body]` exec `fn` and is *axiomatized* to refine the
//! corresponding `HwView` step (the `ensures` is inherited from the trait).
//! These bodies are the trusted seam between running code and the abstract
//! `HwView` state machine: the proof in `machine::machine::refine` consumes the
//! very same step predicates that these instructions are declared to realize.
//!
//! ## Trust boundary
//!
//! The `asm!` strings are trusted against the Arm Architecture Reference Manual,
//! not proved against a formal ISA model.  The ghost return value records the
//! abstract effect the instruction is *defined* to have; because the function is
//! `external_body`, Verus takes that effect on faith.  Likewise, emitting the
//! barriers in the correct break-before-make order is an implementation / TCB
//! obligation, not something the model enforces (see [`HardwareOps`]).
//!
//! `TLBI IPAS2E1IS` is a register-form op, so it takes a **real** `usize`
//! operand `ipa_page` (the IPA `>> 12`, i.e. the guest page number); the spec
//! page identity is derived from it as `GuestPage(ipa_page as nat)`.  The VMID is
//! abstracted (ghost `vm`): it is read from the current `VTTBR_EL2`, which the
//! caller must already have programmed to `vm`.
use super::mmu::HardwareInst;
use core::arch::asm;
use vstd::prelude::*;

verus! {

/// Zero-sized handle to the AArch64 hardware.  Carries no state; it only gives
/// hypervisor code a value on which to call the [`HardwareOps`] instructions.
pub struct Aarch64Hw;

impl HardwareInst for Aarch64Hw {
    #[verifier::external_body]
    fn issue_tlbi_s2(ipa_page: usize) {
        // Broadcast a stage-2 IPA invalidation across the inner-shareable domain.
        // `IPAS2E1IS` requires a register operand: Xt holds IPA >> 12 = the 4K
        // guest page number.  One instruction removes every cached `(*, vm, gpa)`
        // entry on every PE (VMID comes from VTTBR_EL2).
        unsafe {
            asm!("tlbi ipas2e1is, {x}", x = in(reg) ipa_page);
        }
    }

    #[verifier::external_body]
    fn issue_dsb_ish() {
        // Data Synchronization Barrier, inner-shareable.  Does not retire until the
        // preceding broadcast has completed on every PE; no architectural state
        // change (`HwView::dsb_step` is the identity).
        unsafe {
            asm!("dsb ish");
        }
    }

    #[verifier::external_body]
    fn issue_isb() {
        // Instruction Synchronization Barrier.  No architectural state change
        // (`HwView::isb_step` is the identity).
        unsafe {
            asm!("isb");
        }
    }
}

} // verus!
