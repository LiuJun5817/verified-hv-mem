//! The concrete MMU hardware handle ([`MmuHardware`]) and its asm seam
//! ([`HardwareInstr`]).
//!
//! [`HardwareInstr`] is the trusted, architecture-specific instruction seam: each
//! method wraps a real maintenance instruction in `#[verifier::external_body]` asm
//! and carries no abstract state.  [`MmuHardware<I>`] owns the `MmuSpec` instance
//! and the global `s2map`/`tlb` tokens; its methods pair those instructions with
//! the matching ghost transitions, so the asm and the transition firing sit behind
//! one trust boundary.
//!
//! # Why the `Instance` is private — the forcing
//!
//! A `tokenized_state_machine!` transition is a `proof fn` on the `Instance`: any
//! code that can name an `MmuSpec::Instance` could fire it in ghost code with no
//! real instruction.  The forcing rests on keeping the instance out of
//! implementation hands: `MmuHardware`'s fields are **private** and never handed
//! out, so only this module's methods fire transitions.  `MemorySet::remove` holds
//! an `&mut MmuHardware` and can *call* [`MmuHardware::unmap_dsb_tlbi`], but cannot
//! fire `unmap`/`invalidate` itself.  And `unmap_dsb_tlbi`'s post — restoring the
//! [`synced`](MmuHardware::synced) sync point — is unprovable unless its real
//! `DSB`+`TLBI` actually run, since only they advance the encapsulated tokens.
use crate::machine::hardware::mmu::{MmuInstance, MmuS2MapToken, MmuTlbToken, MmuVmIdsToken};
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
pub trait HardwareInstr {
    // ------------------------------------------------------------------
    // S2 TLB invalidation broadcast
    // ------------------------------------------------------------------
    /// Broadcast a stage-2 TLB invalidation for the IPA `(vm, gpa)` across every
    /// PE in the inner-shareable domain.
    ///
    /// On AArch64: a single `TLBI IPAS2E1IS, Xt` instruction.  Because it is
    /// inner-shareable it is a *broadcast* — one instruction removes the cached
    /// `(*, vm, gpa)` entries on **every** PE — so it takes no per-CPU argument.
    /// It must be followed by a completion `DSB ISH` ([`issue_dsb_ish`]) before the
    /// new translation may be relied upon.
    ///
    /// `IPAS2E1IS` is a **register-form** maintenance op: the target IPA travels in
    /// `Xt` as `Xt[..] = IPA >> 12`, which for the model's 4K pages is exactly the
    /// guest page number — hence the real `usize` operand `ipa_page`.  The VMID is
    /// *not* an operand; it is read from the current `VTTBR_EL2`, which the caller
    /// must already have programmed.  ([`MmuHardware::unmap_dsb_tlbi`] derives the
    /// spec page from `ipa_page`, so the asm and the ghost transition agree.)
    fn issue_tlbi_s2(ipa_page: usize);

    // ------------------------------------------------------------------
    // Data Synchronization Barrier (DSB ISH)
    // ------------------------------------------------------------------
    /// Issue a Data Synchronization Barrier in the inner-shareable domain.
    ///
    /// On AArch64: `DSB ISH`.  It does not retire until the preceding
    /// `TLBI IPAS2E1IS` has completed on every PE in the domain.
    fn issue_dsb_ish();

    // ------------------------------------------------------------------
    // Instruction Synchronization Barrier (ISB)
    // ------------------------------------------------------------------
    /// Issue an Instruction Synchronization Barrier.
    ///
    /// On AArch64: `ISB`.  Synchronizes only the executing PE's own context.
    fn issue_isb();
}

/// Concrete MMU hardware handle: the owner of the `MmuSpec` instance and the
/// global `s2map`/`tlb` tokens.  An **exec** struct carrying `Tracked` fields, so
/// it threads through exec code (`MemorySet::remove`) as `&mut MmuHardware<I>`
/// while its methods drive both the real instructions and the ghost transitions.
pub struct MmuHardware<I> where I: HardwareInstr {
    /// PRIVATE — the instance handle.  Never handed out (see module docs): this
    /// is what keeps transitions un-fireable by ordinary token-holding code.
    instance: Tracked<MmuInstance>,
    /// PRIVATE — the live-vm mirror token, consumed/produced by `add_vm`.
    vm_ids: Tracked<MmuVmIdsToken>,
    /// PRIVATE — the single global TLB token (variable-sharded).
    tlb: Tracked<MmuTlbToken>,
    /// Phantom type parameter for the platform-specific instruction implementation.
    _phantom: PhantomData<I>,
}

impl<I: HardwareInstr> MmuHardware<I> {
    /// The `MmuSpec` instance this handle drives.
    pub closed spec fn inst_id(&self) -> InstanceId {
        self.instance@.id()
    }

    /// The set of live vms (the `vm_ids` mirror).
    pub closed spec fn live_vms(&self) -> Set<VmId> {
        self.vm_ids@.value()
    }

    /// The encapsulated `tlb`/`vm_ids` tokens belong to this handle's instance.
    /// (`s2map` is *not* here — its per-vm slices live in the zone locks; only the
    /// instance + global `tlb` + the `vm_ids` mirror are encapsulated here.  Full
    /// `tlb_coherent` is the `MmuSpec` invariant, so it never needs threading.)
    pub closed spec fn wf(&self) -> bool {
        &&& self.tlb@.instance_id() == self.instance@.id()
        &&& self.vm_ids@.instance_id() == self.instance@.id()
    }

    /// Register a fresh vm: fires `add_vm`, **minting** that zone's `s2map` slice
    /// token (empty), which the caller stores in the new zone's lock.
    pub fn add_vm(&mut self, vm: Ghost<VmId>) -> (res: Tracked<MmuS2MapToken>)
        requires
            old(self).wf(),
            !old(self).live_vms().contains(vm@),
        ensures
            self.wf(),
            self.inst_id() == old(self).inst_id(),
            self.live_vms() == old(self).live_vms().insert(vm@),
            res@.instance_id() == self.inst_id(),
            res@.key() == vm@,
            res@.value() == Map::<GuestPage, S2Entry>::empty(),
    {
        let tracked new_tok = self.instance.borrow().add_vm(vm@, self.vm_ids.borrow_mut());
        Tracked(new_tok)
    }

    /// One per-page break-before-make step: the caller has written the PTE invalid;
    /// this issues the `DSB ISH` (drops `(vm, gpa)` from the vm's slice) and the
    /// `TLBI IPAS2E1IS` broadcast (clears the page's cached entries) — together,
    /// firing the bundled `unmap_invalidate`.  Consumes the vm's slice token and
    /// returns it with the page removed; `tlb_coherent` is preserved by the `MmuSpec`
    /// invariant, so it is not part of this contract.
    ///
    /// `ipa_page` is the real operand (`IPA >> 12`); the spec page is **derived**
    /// from it, so the asm and the ghost transition target the same page.
    pub fn unmap_dsb_tlbi(
        &mut self,
        s2_tok: Tracked<MmuS2MapToken>,
        ipa_page: usize,
        vm: Ghost<VmId>,
    ) -> (res: Tracked<MmuS2MapToken>)
        requires
            old(self).wf(),
            s2_tok@.instance_id() == old(self).inst_id(),
            s2_tok@.key() == vm@,
        ensures
            self.wf(),
            self.inst_id() == old(self).inst_id(),
            self.live_vms() == old(self).live_vms(),
            res@.instance_id() == self.inst_id(),
            res@.key() == vm@,
            res@.value() == s2_tok@.value().remove(GuestPage(ipa_page as nat)),
    {
        let ghost gpa = GuestPage(ipa_page as nat);
        let tracked s2 = s2_tok.get();
        I::issue_dsb_ish();
        I::issue_tlbi_s2(ipa_page);
        let tracked new_tok = self.instance.borrow().unmap_invalidate(
            vm@,
            gpa,
            s2,
            self.tlb.borrow_mut(),
        );
        Tracked(new_tok)
    }

    /// Map side of break-before-make: the caller has written a *fresh* PTE; this
    /// issues the `DSB ISH` that makes it walker-reachable, firing `map` (adds
    /// `(gpa => entry)` to the vm's slice).  No `TLBI` — by the `MmuSpec` invariant a
    /// page absent from the slice has no cached entry.  Consumes the vm's slice token
    /// (with the page absent) and returns it with the page inserted.
    pub fn map_dsb(
        &mut self,
        s2_tok: Tracked<MmuS2MapToken>,
        ipa_page: usize,
        vm: Ghost<VmId>,
        entry: Ghost<S2Entry>,
    ) -> (res: Tracked<MmuS2MapToken>)
        requires
            old(self).wf(),
            s2_tok@.instance_id() == old(self).inst_id(),
            s2_tok@.key() == vm@,
            !s2_tok@.value().contains_key(GuestPage(ipa_page as nat)),
        ensures
            self.wf(),
            self.inst_id() == old(self).inst_id(),
            self.live_vms() == old(self).live_vms(),
            res@.instance_id() == self.inst_id(),
            res@.key() == vm@,
            res@.value() == s2_tok@.value().insert(GuestPage(ipa_page as nat), entry@),
    {
        let ghost gpa = GuestPage(ipa_page as nat);
        let tracked s2 = s2_tok.get();
        I::issue_dsb_ish();
        let tracked new_tok = self.instance.borrow().map(vm@, gpa, entry@, s2);
        Tracked(new_tok)
    }
}

} // verus!
