//! AArch64 realization of the [`HardwareInstr`] trust contract.
//!
//! Each method wraps a real maintenance / barrier instruction in an
//! `#[verifier::external_body]` exec `fn` containing the `asm!`.  These bodies are
//! the trusted seam between running code and the MMU state machine: `MmuHardware`
//! pairs each instruction with the ghost transition it realizes.
//!
//! ## Trust boundary
//!
//! The `asm!` strings are trusted against the Arm Architecture Reference Manual,
//! not proved against a formal ISA model.  `TLBI IPAS2E1IS` is a register-form op,
//! so it takes a **real** `usize` operand `ipa_page` (the IPA `>> 12`, i.e. the
//! guest page number); `MmuHardware::unmap_dsb_tlbi` derives the spec page from it.
//! The VMID is read from the current `VTTBR_EL2`, which the caller must already
//! have programmed.
use super::mmu::HardwareInstr;
use core::arch::asm;
use vstd::prelude::*;

verus! {

/// Zero-sized AArch64 [`HardwareInstr`] implementor: the asm-emitting backend that
/// `MmuHardware` is parameterized over.
pub struct Aarch64Hw;

impl HardwareInstr for Aarch64Hw {
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
        // preceding broadcast has completed on every PE.
        unsafe {
            asm!("dsb ish");
        }
    }

    #[verifier::external_body]
    fn issue_isb() {
        // Instruction Synchronization Barrier (executing PE's own context).
        unsafe {
            asm!("isb");
        }
    }
}

} // verus!
