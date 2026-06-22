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
use core::arch::asm;
use vstd::prelude::*;

use crate::machine::hardware::{HardwareOps, HwView};
use crate::machine::types::*;

verus! {

/// Zero-sized handle to the AArch64 hardware.  Carries no state; it only gives
/// hypervisor code a value on which to call the [`HardwareOps`] instructions.
pub struct Aarch64Hw;

impl HardwareOps for Aarch64Hw {
    #[verifier::external_body]
    fn issue_tlbi_s2(&self, ipa_page: usize, vm: Ghost<VmId>, hw: Ghost<HwView>) -> (hw_post: Ghost<
        HwView,
    >) {
        // Broadcast a stage-2 IPA invalidation across the inner-shareable domain.
        // `IPAS2E1IS` requires a register operand: Xt holds IPA >> 12 = the 4K
        // guest page number.  One instruction removes every cached `(*, vm, gpa)`
        // entry on every PE (VMID comes from VTTBR_EL2).
        unsafe {
            asm!("tlbi ipas2e1is, {x}", x = in(reg) ipa_page);
        }
        // The abstract effect realized by the broadcast (see
        // `HwView::tlbi_ipa_broadcast_step`): drop every cached entry for the
        // target IPA together with its pending-invalidation flag.
        let ghost gpa = GuestPage(ipa_page as nat);
        let ghost targets = Set::new(
            |key: TlbKey| key.vm == vm@ && key.gpa == gpa && hw@.tlb.contains_key(key),
        );
        Ghost(
            HwView {
                tlb: hw@.tlb.remove_keys(targets),
                pending_invalidations: hw@.pending_invalidations.difference(targets),
                active_vm: hw@.active_vm,
                memory: hw@.memory,
            },
        )
    }

    #[verifier::external_body]
    fn issue_dsb_ish(&self, hw: Ghost<HwView>) -> (hw_post: Ghost<HwView>) {
        // Data Synchronization Barrier, inner-shareable.  Does not retire until the
        // preceding broadcast has completed on every PE; no architectural state
        // change (`HwView::dsb_step` is the identity).
        unsafe {
            asm!("dsb ish");
        }
        hw
    }

    #[verifier::external_body]
    fn issue_isb(&self, hw: Ghost<HwView>) -> (hw_post: Ghost<HwView>) {
        // Instruction Synchronization Barrier.  No architectural state change
        // (`HwView::isb_step` is the identity).
        unsafe {
            asm!("isb");
        }
        hw
    }
}

} // verus!
