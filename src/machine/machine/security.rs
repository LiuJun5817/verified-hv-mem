use vstd::prelude::*;

use super::state::MachineState;
use crate::machine::types::*;

verus! {

impl MachineState {
    /// `s2` is reachable from `s1` by one step of some VM *other than* `subject`.
    /// The subject-vs-environment split exists only here, to state isolation; it
    /// is not part of the machine state.
    pub open spec fn env_reachable(s1: MachineState, s2: MachineState, subject: VmId) -> bool {
        exists|vm: VmId, op: VmMemOp| vm != subject && #[trigger] MachineState::vm_step(s1, s2, vm, op)
    }

    // ─────────────────────────── proof helpers ──────────────────────────────
    /// In a `wf` state, a successful translation resolves to a page the VM is
    /// entitled to (owned or shared) — the bridge from `tlb_safe` + `translation_wf`.
    proof fn lemma_translation_targets_owned(s: MachineState, cpu: CpuId, vm: VmId, gpa: GuestPage)
        requires
            s.wf(),
            s.effective_entry(cpu, vm, gpa) is Some,
        ensures
            s.all_vms().contains(vm),
            s.owned_or_shared(vm, s.effective_entry(cpu, vm, gpa)->Some_0.page),
    {
        let key = TlbKey::new(cpu, vm, gpa);
        let sk = VmPageKey::new(vm, gpa);
        // The effective entry's page is the stage-2 map's page for `(vm, gpa)`:
        // a cached TLB entry agrees with the map (`tlb_safe`); otherwise the entry
        // *is* the map entry.
        assert(s.s2_map.contains_key(sk) && s.effective_entry(cpu, vm, gpa)->Some_0.page
            == s.s2_map[sk].page) by {
            if s.tlb.contains_key(key) {
                assert(s.tlb_safe());
            }
        }
        // `translation_wf` at `sk` (note `sk.vm == vm`) gives ownership/sharing.
        assert(s.translation_wf());
    }

    /// A `subject`-private page is owned or shared by no *other* VM.  Owned: by
    /// ownership disjointness; shared: a private page lies in no edge at all.
    proof fn lemma_private_excludes_other(
        s: MachineState,
        subject: VmId,
        other: VmId,
        page: PhysPage,
    )
        requires
            s.ownership_wf(),
            s.all_vms().contains(subject),
            s.all_vms().contains(other),
            other != subject,
            s.private_page(subject, page),
        ensures
            !s.owned_or_shared(other, page),
    {
        assert(!s.owned_or_shared(other, page)) by {
            if s.owned_or_shared(other, page) {
                if s.vm_owned.contains_key(other) && s.vm_owned[other].contains(page) {
                    // ownership disjointness vs. the subject (who owns `page`).
                    assert(!s.vm_owned[subject].contains(page));
                    assert(false);
                } else {
                    // then `other` reaches `page` via a sharing edge — but a private
                    // page is in no edge.
                    assert(s.shared_with(other, page));
                    let e = choose|e: SharedPage|
                        s.shared_pages.contains(e) && e.page == page && (e.left == other
                            || e.right == other);
                    assert(s.shared_pages.contains(e) && e.page == page);
                    assert(false);
                }
            }
        }
    }

    /// Page/word round-trip: a word built from `(page, off)` reports `page` as its
    /// page, for any in-range `off`.
    proof fn lemma_page_word_roundtrip(p: PhysPage, off: nat)
        requires
            off < PAGE_WORDS,
        ensures
            p.word(off).page() == p,
    {
        assert((p.0 * PAGE_WORDS + off) / PAGE_WORDS == p.0) by (nonlinear_arith)
            requires
                off < PAGE_WORDS,
                PAGE_WORDS > 0,
        ;
    }

    /// Every environment step — whatever the op — preserves identity, ownership and
    /// translation, and lands in a `wf` state.  (Only physical memory may change,
    /// and only on a write.)
    proof fn lemma_env_step_facts(s1: MachineState, s2: MachineState, subject: VmId)
        requires
            Self::env_reachable(s1, s2, subject),
        ensures
            s2.wf(),
            s2.same_identity_as(&s1),
            s2.same_ownership_as(&s1),
            s2.same_translation_as(&s1),
    {
        let (vm, op) = choose|vm: VmId, op: VmMemOp|
            vm != subject && MachineState::vm_step(s1, s2, vm, op);
        assert(MachineState::vm_step(s1, s2, vm, op));
        match op {
            VmMemOp::Read(c, g) => { assert(MachineState::vm_read_step(s1, s2, vm, c, g)); },
            VmMemOp::Write(c, g, v) => { assert(MachineState::vm_write_step(s1, s2, vm, c, g, v)); },
            VmMemOp::HyperCall(c, r) => { assert(MachineState::vm_hypercall_step(s1, s2, vm, c, r)); },
        }
    }

    // ─────────────────────────── isolation theorems ─────────────────────────
    /// **Read isolation** (spatial confidentiality).
    ///
    /// After any single environment-VM step, no environment VM `vm ≠ subject` can
    /// read a `subject`-private page: any successful read by `vm` resolves to a
    /// *different* physical page.  This is access-control isolation over plain
    /// (unencrypted) memory — secrecy by *non-mapping*, not by encryption: the
    /// environment never holds a translation into the page.
    pub proof fn lemma_read_isolation(
        s1: MachineState,
        s2: MachineState,
        subject: VmId,
        page: PhysPage,
        vm: VmId,
        cpu: CpuId,
        gva: GuestWordAddr,
    )
        requires
            s1.wf(),
            s1.all_vms().contains(subject),
            Self::env_reachable(s1, s2, subject),
            s1.private_page(subject, page),
            s1.all_vms().contains(vm),
            vm != subject,
            s2.read_observation(cpu, vm, gva) is Some,
        ensures
            s2.translated_word(cpu, vm, gva)->Some_0.page() != page,
    {
        Self::lemma_env_step_facts(s1, s2, subject);
        // Identity & ownership carry over, so the page is still subject-private in `s2`.
        assert(s2.all_vms().contains(subject) && s2.all_vms().contains(vm));
        assert(s2.private_page(subject, page));
        let gpa = gva.page();
        assert(s2.effective_entry(cpu, vm, gpa) is Some);
        let ep = s2.effective_entry(cpu, vm, gpa)->Some_0.page;
        // `vm`'s read targets an owned-or-shared page, which can't be the private one.
        Self::lemma_translation_targets_owned(s2, cpu, vm, gpa);
        Self::lemma_private_excludes_other(s2, subject, vm, page);
        assert(ep != page);
        assert(gva.offset() < PAGE_WORDS);
        Self::lemma_page_word_roundtrip(ep, gva.offset());
    }

    /// **Write isolation** (spatial integrity).
    ///
    /// If the `subject` reads `gva` from a private backing page in `s1`, then after
    /// any single environment-VM step the `subject` reads the *same* value.  No
    /// environment write can reach the page — tamper-resistance by ownership
    /// disjointness, not by a cryptographic MAC.
    pub proof fn lemma_write_isolation(
        s1: MachineState,
        s2: MachineState,
        subject: VmId,
        cpu: CpuId,
        gva: GuestWordAddr,
    )
        requires
            s1.wf(),
            s1.all_vms().contains(subject),
            Self::env_reachable(s1, s2, subject),
            s1.read_observation(cpu, subject, gva) is Some,
            s1.private_page(subject, s1.effective_entry(cpu, subject, gva.page())->Some_0.page),
        ensures
            s2.read_observation(cpu, subject, gva) == s1.read_observation(cpu, subject, gva),
    {
        let gpa = gva.page();
        let subj_page = s1.effective_entry(cpu, subject, gpa)->Some_0.page;
        let subj_paddr = s1.translated_word(cpu, subject, gva)->Some_0;
        // The subject's translation is preserved across any env step.
        Self::lemma_env_step_facts(s1, s2, subject);
        assert(subj_paddr.page() == subj_page) by {
            assert(gva.offset() < PAGE_WORDS);
            Self::lemma_page_word_roundtrip(subj_page, gva.offset());
        }
        // Identify the concrete env step and show the subject's backing word is
        // untouched, so the read value is unchanged.
        let (vmE, op) = choose|vmE: VmId, op: VmMemOp|
            vmE != subject && MachineState::vm_step(s1, s2, vmE, op);
        assert(vmE != subject && MachineState::vm_step(s1, s2, vmE, op));
        assert(s1.all_vms().contains(vmE));
        match op {
            VmMemOp::Read(c, g) => {
                assert(MachineState::vm_read_step(s1, s2, vmE, c, g));
                assert(s2.memory == s1.memory);
                assert(s2.read_observation(cpu, subject, gva) == s1.read_observation(cpu, subject, gva));
            },
            VmMemOp::HyperCall(c, r) => {
                assert(MachineState::vm_hypercall_step(s1, s2, vmE, c, r));
                assert(s2.memory == s1.memory);
                assert(s2.read_observation(cpu, subject, gva) == s1.read_observation(cpu, subject, gva));
            },
            VmMemOp::Write(cE, gE, v) => {
                assert(MachineState::vm_write_step(s1, s2, vmE, cE, gE, v));
                let paddrE = s1.translated_word(cE, vmE, gE)->Some_0;
                assert(s2.memory == s1.memory.insert(paddrE, v));
                // The env write targets an owned-or-shared page of `vmE`, which —
                // since the subject's page is private and `vmE ≠ subject` — differs.
                assert(s1.effective_entry(cE, vmE, gE.page()) is Some);
                let eEp = s1.effective_entry(cE, vmE, gE.page())->Some_0.page;
                Self::lemma_translation_targets_owned(s1, cE, vmE, gE.page());
                Self::lemma_private_excludes_other(s1, subject, vmE, subj_page);
                assert(eEp != subj_page);
                assert(gE.offset() < PAGE_WORDS);
                Self::lemma_page_word_roundtrip(eEp, gE.offset());
                assert(paddrE.page() == eEp);
                assert(paddrE != subj_paddr);
                assert(s2.read_observation(cpu, subject, gva) == s1.read_observation(cpu, subject, gva));
            },
        }
    }
}

} // verus!
