//! AArch64 realization of the stage-2 maintenance trust contract — both regimes:
//! the CPU MMU ([`MmuInstr`]) and the SMMU/IOMMU ([`SmmuInstr`]), combined under
//! [`HardwareInstr`].
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
//! The CPU invalidation seam includes the completion `DSB ISH`, matching the
//! model's synchronous invalidate transition.  The VMID is read from the current
//! `VTTBR_EL2`, which the caller must already have programmed.
//!
//! The SMMU command-queue methods ([`SmmuInstr`]) are currently placeholder bodies
//! (`dsb ish`): the real `CMD_TLBI_S2_IPA`/`CMD_SYNC` command-queue MMIO writes
//! depend on the platform's SMMU base address (configuration), so they are a
//! documented trusted seam to be filled in per platform.
use super::mmu::{HardwareInstr, MmuInstr, SmmuInstr};
use core::arch::asm;
use vstd::prelude::*;

verus! {

/// Zero-sized AArch64 backend that `MmuHardware` is parameterized over.  It
/// implements both regime seams — [`MmuInstr`] (CPU MMU) and [`SmmuInstr`] (SMMU) —
/// and so satisfies the combined [`HardwareInstr`] marker.
pub struct Aarch64Hw;

impl MmuInstr for Aarch64Hw {
    #[verifier::external_body]
    fn issue_tlbi_s2_sync(ipa_page: usize) {
        // Broadcast and complete a CPU stage-2 IPA invalidation across the
        // inner-shareable domain.
        // `IPAS2E1IS` requires a register operand: Xt holds IPA >> 12 = the 4K
        // guest page number.  One instruction removes every cached `(*, vm, gpa)`
        // entry on every PE (VMID comes from VTTBR_EL2); the following DSB makes
        // that invalidation complete before the model transition fires.
        unsafe {
            asm!("tlbi ipas2e1is, {x}", x = in(reg) ipa_page);
            asm!("dsb ish");
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

impl SmmuInstr for Aarch64Hw {
    #[verifier::external_body]
    fn issue_smmu_tlbi_s2(_ipa_page: usize) {
        // SMMUv3 stage-2 IPA invalidation: build a `CMD_TLBI_S2_IPA` command (with
        // `Addr = ipa_page` and the VMID from the device context) and write it to the
        // SMMU command queue (MMIO).  The SMMU is a device, not a CPU, so this is a
        // queue write rather than a `TLBI` instruction; a `DSB ISH` orders the write
        // to the queue, and `issue_smmu_sync` (CMD_SYNC) completes it.  Left as a
        // documented trusted seam (the concrete MMIO base is platform configuration).
        unsafe {
            asm!("dsb ish");
        }
    }

    #[verifier::external_body]
    fn issue_smmu_sync() {
        // SMMUv3 `CMD_SYNC`: write a CMD_SYNC to the command queue and poll the
        // consumer index / wait for completion, guaranteeing preceding commands
        // (CMD_TLBI_S2_IPA, configuration invalidations) are observed.  Ordered with
        // a `DSB ISH`; the queue-polling MMIO is platform configuration.
        unsafe {
            asm!("dsb ish");
        }
    }
}

impl HardwareInstr for Aarch64Hw {}

} // verus!
