//! Slice 3 of the SW/HW co-verification plan: the **encapsulation skeleton**.
//!
//! [`MmuHardware`] is the concrete handle that owns the `MmuSpec` instance and
//! the single global TLB token.  Its methods fire the MMU transitions *in their
//! bodies*; in the grounded implementation each also runs the real maintenance
//! instruction (`DSB ISH` / `TLBI IPAS2E1IS`) as an `#[verifier::external_body]`
//! wrapper — the asm and the transition firing then sit behind the same trust
//! boundary as `Aarch64Hw`'s other instructions.
//!
//! # Why the `Instance` is private — the forcing
//!
//! A `tokenized_state_machine!` transition is a `proof fn` on the `Instance`: any
//! code that can name an `MmuSpec::Instance` value can fire it in ghost code with
//! no real instruction.  The whole forcing argument rests on **keeping the
//! instance out of implementation hands**:
//!
//! * `MmuHardware::instance` is a **private** field and is never returned, so only
//!   the methods in this module can fire a transition.
//! * The implementation (e.g. `MemorySet::remove`) holds only [`MmuS2MapToken`]s
//!   — page-ownership tokens — and an `&MmuHardware`.  With those it can *call*
//!   `dsb_unmap` / `tlbi`, but it cannot fire `unmap` / `invalidate` itself,
//!   because it has no `Instance`.
//!
//! Concretely: to discharge `remove`'s post-condition the impl must give up a
//! page's `s2map` token, and the only thing that consumes it is [`dsb_unmap`],
//! whose body runs the real `DSB`.  Omitting the instruction leaves the token in
//! hand and the post unprovable.  (`MmuSpec::Instance` is constant-sharded and so
//! freely duplicable; the encapsulation works precisely because a copy is *never*
//! handed out.)
use crate::machine::hardware::mmu::{
    invalidation_targets, MmuInstance, MmuS2MapToken, MmuTlbToken,
};
use crate::machine::types::*;
use core::marker::PhantomData;
use vstd::prelude::*;
use vstd::tokens::InstanceId;

verus! {


/// Trusted hardware-level instructions.
///
/// Each method is an exec `fn` that can appear in hypervisor code. Platform implementations
/// provide `#[verifier::external_body]` bodies containing the actual `asm!` instructions, 
/// citing the architecture reference manual for correctness.
pub trait HardwareInst {
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
    fn issue_tlbi_s2(ipa_page: usize);

    // ------------------------------------------------------------------
    // Data Synchronization Barrier (DSB ISH)
    // ------------------------------------------------------------------
    /// Issue a Data Synchronization Barrier in the inner-shareable domain.
    ///
    /// On AArch64: `DSB ISH`.  It does not retire until the preceding
    /// `TLBI IPAS2E1IS` has completed on every PE in the domain.  No abstract state
    /// change ([`HwView::dsb_step`] is the identity).
    fn issue_dsb_ish();

    // ------------------------------------------------------------------
    // Instruction Synchronization Barrier (ISB)
    // ------------------------------------------------------------------
    /// Issue an Instruction Synchronization Barrier.
    ///
    /// On AArch64: `ISB`.  Synchronizes only the executing PE's own context.  No
    /// abstract state change ([`HwView::isb_step`] is the identity).
    fn issue_isb();
}

/// Concrete MMU hardware handle: the `HardwareOps`-side owner of the `MmuSpec`
/// instance and the global TLB token.
pub struct MmuHardware<I> where I: HardwareInst {
    /// PRIVATE — the instance handle.  Never handed out (see module docs): this
    /// is what keeps transitions un-fireable by ordinary token-holding code.
    instance: Tracked<MmuInstance>,
    /// PRIVATE — the single global TLB token (variable-sharded).
    tlb: Tracked<MmuTlbToken>,
    /// Phantom type parameter for the platform-specific instruction implementation.
    _phantom: PhantomData<I>,
}

impl<I: HardwareInst> MmuHardware<I> {
    /// The `MmuSpec` instance this handle drives.
    pub closed spec fn inst_id(&self) -> InstanceId {
        self.instance@.id()
    }

    /// The current TLB contents (the value of the encapsulated `tlb` token).
    pub closed spec fn tlb_view(&self) -> Map<TlbKey, TlbEntry> {
        self.tlb@.value()
    }

    /// The TLB token belongs to this handle's instance.
    pub closed spec fn wf(&self) -> bool {
        self.tlb@.instance_id() == self.instance@.id()
    }

    /// `DSB ISH` after writing a PTE invalid: the unmap becomes walker-visible.
    ///
    /// Fires the `unmap` transition, **consuming** the page's `s2map` token — the
    /// forcing seam.  After this the caller no longer owns the `(vm, gpa)`
    /// mapping token, so it cannot claim the page is still mapped.  (The real
    /// `dsb ish` is global; in the per-page Route A loop only `(vm, gpa)` was
    /// pending, so firing the single `unmap` is faithful.)
    pub fn dsb_unmap(
        &self,
        vm: Ghost<VmId>,
        gpa: Ghost<GuestPage>,
        s2_tok: Tracked<MmuS2MapToken>,
    )
        requires
            self.wf(),
            s2_tok@.instance_id() == self.inst_id(),
            s2_tok@.key() == VmPageKey::new(vm@, gpa@),
    {
        // Grounded impl
        I::issue_dsb_ish();
        proof {
            self.instance.borrow().unmap(vm@, gpa@, s2_tok.get());
        }
    }

    /// `TLBI IPAS2E1IS, Xt` broadcast: clears every CPU's cached entry for
    /// `(vm, gpa)`.  Fires the `invalidate` transition on the encapsulated TLB
    /// token.  `ipa_page` is the real operand (`IPA >> 12`); the spec page is
    /// derived from it, exactly as in `Aarch64Hw::issue_tlbi_s2`.
    pub fn tlbi(&mut self, ipa_page: usize, vm: Ghost<VmId>, gpa: Ghost<GuestPage>)
        requires
            old(self).wf(),
            gpa@ == GuestPage(ipa_page as nat),
        ensures
            self.wf(),
            self.inst_id() == old(self).inst_id(),
            self.tlb_view() == old(self).tlb_view().remove_keys(invalidation_targets(vm@, gpa@)),
    {
        // Grounded impl
        I::issue_tlbi_s2(ipa_page);
        proof {
            self.instance.borrow().invalidate(vm@, gpa@, self.tlb.borrow_mut());
        }
    }
}

} // verus!
