//! The concrete stage-2 hardware handle ([`MmuHardware`]) and its asm seams
//! ([`MmuInstr`] for the CPU MMU, [`SmmuInstr`] for the IOMMU/SMMU).
//!
//! # Two regimes, one abstraction, two instances
//!
//! The hypervisor drives **two independent stage-2 translation regimes**: the CPU
//! **MMU** (instruction/data accesses by guests) and the **SMMU** — the IOMMU that
//! translates device DMA.  In hardware they are genuinely separate structures with
//! **separate TLBs**: a CPU `TLBI IPAS2E1IS` does not flush the SMMU TLB, and an
//! SMMU `CMD_TLBI_S2_IPA` does not flush the CPU TLB.  They also walk **separate
//! page tables** here (each zone keeps a distinct `cpu_mem_set` and
//! `iommu_mem_set`).
//!
//! Both regimes obey the *same* abstract law, so they share the
//! [`MmuSpec`](crate::hardware::spec) state-machine **type** — but as **two distinct
//! `Instance`s** with disjoint `s2map`/`tlb`/`vm_ids` tokens.  Concretely the
//! hypervisor holds two `MmuHardware` values, threaded separately as `mmu` (the CPU
//! MMU) and `iommu_mmu` (the SMMU); a maintenance call on one cannot touch the
//! other's tokens.
//!
//! # The asm seams are split by regime
//!
//! Only the *real instructions* differ between regimes, so the trusted asm seam is
//! split in two:
//!
//! * [`MmuInstr`] — CPU MMU maintenance (`TLBI IPAS2E1IS`, `DSB ISH`);
//! * [`SmmuInstr`] — SMMU command-queue maintenance (`CMD_TLBI_S2_IPA`, `CMD_SYNC`).
//!
//! [`HardwareInstr`] is just the combined marker (`MmuInstr + SmmuInstr`) a single
//! platform backend (e.g. `Aarch64Hw`) implements.  Each method wraps a real
//! instruction in `#[verifier::external_body]` asm and carries no abstract state.
//! [`MmuHardware<I>`] owns one regime's `MmuSpec` instance and its global
//! `tlb`/`vm_ids` tokens; its CPU methods ([`MmuHardware::unmap_dsb_tlbi`],
//! [`MmuHardware::map_dsb`]) emit `MmuInstr` asm and its SMMU methods
//! ([`MmuHardware::iommu_unmap_invalidate`], [`MmuHardware::iommu_map_sync`]) emit
//! `SmmuInstr` asm — each pairing the instructions with the matching ghost
//! transition, so the asm and the transition firing sit behind one trust boundary.
//!
//! # Why the `Instance` is private — the forcing
//!
//! A `tokenized_state_machine!` transition is a `proof fn` on the `Instance`: any
//! code that can name an `MmuSpec::Instance` could fire it in ghost code with no
//! real instruction.  The forcing rests on keeping the instance out of
//! implementation hands: `MmuHardware`'s fields are **private** and never handed
//! out, so only this module's methods fire transitions.  `MemorySet::remove` holds
//! an `&mut MmuHardware` and can *call* [`MmuHardware::unmap_dsb_tlbi`], but cannot
//! fire `unmap`/`invalidate` itself.  And `unmap_dsb_tlbi`'s postcondition is
//! unprovable unless its real `DSB`+`TLBI` actually run, since only they advance
//! the encapsulated tokens.
use crate::hardware::spec::{MmuInstance, MmuS2MapToken, MmuSpec, MmuTlbToken, MmuVmIdsToken};
use crate::model::types::{GuestPage, S2Entry, VmId};
use core::marker::PhantomData;
use vstd::prelude::*;

verus! {

/// Trusted **CPU MMU** stage-2 maintenance instructions.
///
/// Each method is an exec `fn` that can appear in hypervisor code. Platform
/// implementations provide `#[verifier::external_body]` bodies containing the actual
/// `asm!` instructions, citing the architecture reference manual for correctness.
/// These drive the **CPU MMU** regime only; the SMMU analogs live in [`SmmuInstr`].
pub trait MmuInstr {
    // ------------------------------------------------------------------
    // S2 TLB invalidation broadcast
    // ------------------------------------------------------------------
    /// Broadcast and complete a CPU stage-2 TLB invalidation for the IPA
    /// `(vm, gpa)` across every PE in the inner-shareable domain.
    ///
    /// On AArch64 this is `TLBI IPAS2E1IS, Xt` followed by the completion
    /// `DSB ISH`.  `IPAS2E1IS` is inner-shareable, so the invalidation is a
    /// broadcast over every PE in that domain and takes no per-CPU argument; the
    /// trailing `DSB ISH` is part of this method because the model-level invalidate
    /// transition is synchronous.  This flushes only the **CPU** TLB — the SMMU TLB
    /// is unaffected (use [`SmmuInstr::issue_smmu_tlbi_s2`]).
    ///
    /// `IPAS2E1IS` is a **register-form** maintenance op: the target IPA travels in
    /// `Xt` as `Xt[..] = IPA >> 12`, which for the model's 4K pages is exactly the
    /// guest page number — hence the real `usize` operand `ipa_page`.  The VMID is
    /// *not* an operand; it is read from the current `VTTBR_EL2`, which the caller
    /// must already have programmed.  ([`MmuHardware::unmap_dsb_tlbi`] derives the
    /// spec page from `ipa_page`, so the asm and the ghost transition agree.)
    fn issue_tlbi_s2_sync(ipa_page: usize);

    // ------------------------------------------------------------------
    // Data Synchronization Barrier (DSB ISH)
    // ------------------------------------------------------------------
    /// Issue a Data Synchronization Barrier in the inner-shareable domain.
    ///
    /// On AArch64: `DSB ISH`.  Before a TLBI, this makes prior page-table writes
    /// visible to walkers; after a TLBI, it waits for the invalidation to complete
    /// on every PE in the domain.
    fn issue_dsb_ish();
}

/// Trusted **IOMMU (SMMU)** stage-2 maintenance instructions.
///
/// The device-side counterpart of [`MmuInstr`]: same abstract effect (stage-2
/// invalidation + completion), but the SMMU is an MMIO command-queue device, so the
/// "instructions" are command-queue writes rather than CPU `TLBI`/`DSB`.  Driving
/// the SMMU regime never touches the CPU MMU's TLB, and vice versa.
pub trait SmmuInstr {
    // ------------------------------------------------------------------
    // SMMU stage-2 IPA invalidation
    // ------------------------------------------------------------------
    /// Invalidate the SMMU stage-2 TLB for the IPA `(stream, gpa)`.
    ///
    /// On Arm SMMUv3 this is a `CMD_TLBI_S2_IPA` command enqueued on the command
    /// queue (the IPA travels as `Addr = IPA >> 12`, the 4K guest page number; the
    /// VMID comes from the device's STE/CD).  Unlike the CPU `TLBI`, the SMMU is an
    /// MMIO device, so the "instruction" is a command-queue write; it must be
    /// followed by [`issue_smmu_sync`](Self::issue_smmu_sync) before the new
    /// translation may be relied on.  Flushes only the **SMMU** TLB.
    fn issue_smmu_tlbi_s2(ipa_page: usize);

    // ------------------------------------------------------------------
    // SMMU command-queue synchronization (CMD_SYNC)
    // ------------------------------------------------------------------
    /// SMMU command-queue synchronization barrier (`CMD_SYNC`).
    ///
    /// Completes all preceding command-queue commands — the SMMU analog of the CPU
    /// `DSB ISH` for stage-2 maintenance.  After it returns, the preceding
    /// `CMD_TLBI_S2_IPA` (or a fresh stage-2 PTE) is guaranteed observed by the SMMU.
    fn issue_smmu_sync();
}

/// Combined platform seam: a single backend that drives **both** stage-2 regimes —
/// the CPU MMU ([`MmuInstr`]) and the SMMU ([`SmmuInstr`]).  It is only a marker, so
/// every `I: HardwareInstr` bound (in `MemorySet`, `Zone`, `HvMem`, …) keeps working
/// while the actual instructions are cleanly partitioned into the two regime traits.
pub trait HardwareInstr: MmuInstr + SmmuInstr {

}

/// Concrete stage-2 hardware handle for **one regime** — the owner of that
/// regime's `MmuSpec` instance and its global `tlb`/`vm_ids` tokens.  The
/// hypervisor builds two of these: one for the CPU MMU (threaded as `mmu`) and one
/// for the SMMU/IOMMU (threaded as `iommu_mmu`).  They are distinct instances with
/// disjoint tokens, so a CPU invalidation can never advance the SMMU's TLB token
/// and vice versa.
///
/// An **exec** struct carrying `Tracked` fields, so it threads through exec code
/// (`MemorySet::remove`) as `&mut MmuHardware<I>` while its methods drive both the
/// real instructions and the ghost transitions.  Its CPU methods emit [`MmuInstr`]
/// asm; its SMMU methods emit [`SmmuInstr`] asm.
pub struct MmuHardware<I> where I: HardwareInstr {
    /// PRIVATE — the instance handle.  Never handed out (see module docs): this
    /// is what keeps transitions un-fireable by ordinary token-holding code.
    instance: Tracked<MmuInstance>,
    /// PRIVATE — the live-vm mirror token, updated by `add_vm` and `remove_vm`.
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

    /// Create a new `MmuHardware`.
    pub fn new() -> (res: Self)
        ensures
            res.live_vms() =~= Set::<VmId>::empty(),
            res.wf(),
    {
        let tracked (Tracked(inst), Tracked(s2map_tok), Tracked(vm_ids_tok), Tracked(tlb_tok)) =
            MmuSpec::Instance::initialize();
        MmuHardware {
            instance: Tracked(inst),
            vm_ids: Tracked(vm_ids_tok),
            tlb: Tracked(tlb_tok),
            _phantom: PhantomData,
        }
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

    /// Deregister a vm after all of its walker-reachable mappings have been removed.
    /// The empty slice has no coherent TLB entries, so no hardware invalidation is
    /// needed at this lifecycle boundary.
    pub fn remove_vm(&mut self, vm: Ghost<VmId>, s2_tok: Tracked<MmuS2MapToken>)
        requires
            old(self).wf(),
            old(self).live_vms().contains(vm@),
            s2_tok@.instance_id() == old(self).inst_id(),
            s2_tok@.key() == vm@,
            s2_tok@.value() == Map::<GuestPage, S2Entry>::empty(),
        ensures
            self.wf(),
            self.inst_id() == old(self).inst_id(),
            self.live_vms() == old(self).live_vms().remove(vm@),
    {
        let tracked s2 = s2_tok.get();
        proof {
            self.instance.borrow().remove_vm(vm@, s2, self.vm_ids.borrow_mut());
        }
    }

    // ── CPU MMU stage-2 maintenance ─────────────────────────────────────────────
    // Emit `MmuInstr` asm (`DSB ISH` / `TLBI IPAS2E1IS`) and run on the CPU MMU
    // instance.  The SMMU counterparts are further below.
    /// One per-page break-before-make step: the caller has written the PTE invalid;
    /// this issues the pre-TLBI `DSB ISH` (drops `(vm, gpa)` from the vm's slice)
    /// and the completed `TLBI IPAS2E1IS` broadcast (clears the page's cached
    /// entries) — together, firing the bundled `unmap_invalidate`.  Consumes the
    /// vm's slice token and returns it with the page removed; `tlb_coherent` is
    /// preserved by the `MmuSpec` invariant, so it is not part of this contract.
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
        I::issue_tlbi_s2_sync(ipa_page);
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

    // ── SMMU (IOMMU) stage-2 maintenance ────────────────────────────────────────
    // The device-side counterparts of the CPU methods above.  Same ghost transitions
    // (the `MmuSpec` model is regime-agnostic), but they emit `SmmuInstr` command-
    // queue asm instead of CPU `DSB`/`TLBI`, and run on the separate `iommu_mmu`
    // instance — so their tokens never alias the CPU MMU's.
    /// SMMU counterpart of [`unmap_dsb_tlbi`](Self::unmap_dsb_tlbi): one per-page
    /// break-before-make unmap on the IOMMU regime.
    ///
    /// Issues the SMMU stage-2 invalidation (`CMD_TLBI_S2_IPA`) and the command-queue
    /// completion barrier (`CMD_SYNC`) — *not* a CPU `DSB`/`TLBI` — firing the same
    /// abstract `unmap_invalidate` transition on this (IOMMU) instance's tokens.
    pub fn iommu_unmap_invalidate(
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
        I::issue_smmu_tlbi_s2(ipa_page);
        I::issue_smmu_sync();
        let tracked new_tok = self.instance.borrow().unmap_invalidate(
            vm@,
            gpa,
            s2,
            self.tlb.borrow_mut(),
        );
        Tracked(new_tok)
    }

    /// SMMU counterpart of [`map_dsb`](Self::map_dsb): the map-side break-before-make
    /// completion on the IOMMU regime.
    ///
    /// Issues the SMMU command-queue completion barrier (`CMD_SYNC`) so the freshly
    /// written stage-2 PTE is observed by the SMMU, firing the same abstract `map`
    /// transition.  No invalidation — by the `MmuSpec` invariant an absent page has
    /// no cached entry.
    pub fn iommu_map_sync(
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
        I::issue_smmu_sync();
        let tracked new_tok = self.instance.borrow().map(vm@, gpa, entry@, s2);
        Tracked(new_tok)
    }
}

} // verus!
