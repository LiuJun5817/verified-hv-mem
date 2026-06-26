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
    /// PRIVATE — the s2map reachable by MMU page table walk.
    s2map: Tracked<MmuS2MapToken>,
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

    /// The current TLB contents (the value of the encapsulated `tlb` token).
    pub closed spec fn tlb_view(&self) -> Map<TlbKey, TlbEntry> {
        self.tlb@.value()
    }

    /// The TLB token belongs to this handle's instance.
    pub closed spec fn wf(&self) -> bool {
        self.tlb@.instance_id() == self.instance@.id() && self.s2map@.instance_id() == self.instance@.id()
    }

    /// The model's TLB-coherence predicate (the body of `MachineState::tlb_safe`),
    /// stated over a bare `(s2_map, tlb)` pair so it can be discharged here.
    pub closed spec fn tlb_coherent(&self) -> bool {
        forall|key: TlbKey| #[trigger]
            self.tlb@.value().contains_key(key) ==> {
                let sk = VmPageKey::new(key.vm, key.gpa);
                &&& self.s2map@.value().contains_key(sk)
                &&& self.tlb_view()[key].as_s2_entry() == self.s2map@.value()[sk]
            }
    }
    
    /// The `vm`-owned slice of the MMU-reachable stage-2 map.
    pub closed spec fn s2map_slice(&self, vm: VmId) -> Map<VmPageKey, S2Entry> {
        self.s2map@.value().restrict(Set::new(|k: VmPageKey| k.vm == vm))
    }

    /// Sync point for **one** `vm`: the MMU's `vm`-slice equals that zone's
    /// projected mappings, and the (global) TLB is coherent.  Being per-vm, the
    /// sync points of distinct zones compose — the global MMU can simultaneously be
    /// synced for every vm (their slices are disjoint and `tlb_coherent` is shared).
    pub closed spec fn synced(&self, vm: VmId, mappings: Map<VmPageKey, S2Entry>) -> bool {
        self.wf() && self.s2map_slice(vm) == mappings && self.tlb_coherent()
    }

    /// One per-page break-before-make step on the tokenized MMU: the caller has
    /// already written the PTE invalid; this issues the `DSB ISH` (making the unmap
    /// walker-visible — fires `unmap`, dropping `(vm, gpa)` from `s2map`) and the
    /// `TLBI IPAS2E1IS` broadcast (fires `invalidate`, clearing the page's stale TLB
    /// entries).  Pre/post are the [`synced`](Self::synced) sync point: it takes a
    /// sync point for `vm`'s `mappings` to one for `mappings.remove((vm, gpa))`.
    ///
    /// `ipa_page` is the real operand (`IPA >> 12`); the spec page is **derived**
    /// from it (`GuestPage(ipa_page as nat)`), so the asm and the ghost transitions
    /// target the same page.  The post is provable only because both instructions
    /// run — the encapsulated tokens are the sole way to advance the MMU state.
    pub fn unmap_dsb_tlbi(
        &mut self,
        mappings: Ghost<Map<VmPageKey, S2Entry>>,
        ipa_page: usize,
        vm: Ghost<VmId>,
    )
        requires
            old(self).synced(vm@, mappings@),
        ensures
            self.synced(vm@, mappings@.remove(VmPageKey::new(vm@, GuestPage(ipa_page as nat)))),
            self.inst_id() == old(self).inst_id(),
    {
        // The spec page is *derived* from the real operand, so the ghost transition
        // and the asm cannot target different pages.
        let ghost gpa = GuestPage(ipa_page as nat);
        // Grounded impl: DSB makes the (already-written-invalid) PTE walker-visible,
        // then the broadcast TLBI clears the stale entries.
        I::issue_dsb_ish();
        I::issue_tlbi_s2(ipa_page);
        proof {
            self.instance.borrow().unmap_invalidate(
                vm@,
                gpa,
                self.s2map.borrow_mut(),
                self.tlb.borrow_mut(),
            );
            // Removing the `(vm, gpa)` key from `s2map` and restricting to `vm`'s
            // slice commute (the key is in the slice), so the new slice is the old
            // slice minus that key.
            assert(self.s2map_slice(vm@) =~= mappings@.remove(VmPageKey::new(vm@, gpa)));
        }
    }

    /// Map side of break-before-make: the caller has written a *fresh* PTE; this
    /// issues the `DSB ISH` that makes it walker-reachable (fires `map`, adding
    /// `(vm, gpa) => entry` to `s2map`).  No `TLBI` is needed — by the invariant a
    /// page absent from `s2map` has no cached entry, so nothing stale can disagree.
    /// Takes a sync point for `vm`'s `mappings` (with the page **absent**) to one
    /// for `mappings.insert((vm, gpa) => entry)`.
    pub fn map_dsb(
        &mut self,
        mappings: Ghost<Map<VmPageKey, S2Entry>>,
        ipa_page: usize,
        vm: Ghost<VmId>,
        entry: Ghost<S2Entry>,
    )
        requires
            old(self).synced(vm@, mappings@),
            !mappings@.contains_key(VmPageKey::new(vm@, GuestPage(ipa_page as nat))),
        ensures
            self.synced(
                vm@,
                mappings@.insert(VmPageKey::new(vm@, GuestPage(ipa_page as nat)), entry@),
            ),
            self.inst_id() == old(self).inst_id(),
    {
        let ghost gpa = GuestPage(ipa_page as nat);
        // The page is absent from `vm`'s slice (= `mappings`), and `vm`'s slice is
        // `s2map` restricted to `vm`, so the page is absent from the whole `s2map`
        // — discharging `map`'s freshness `require`.
        proof {
            assert(!self.s2map@.value().contains_key(VmPageKey::new(vm@, gpa)));
        }
        I::issue_dsb_ish();
        proof {
            self.instance.borrow().map(vm@, gpa, entry@, self.s2map.borrow_mut());
            assert(self.s2map_slice(vm@) =~= mappings@.insert(VmPageKey::new(vm@, gpa), entry@));
        }
    }
}

} // verus!
