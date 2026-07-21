#![allow(non_snake_case)]

use super::state::MachineState;
use crate::model::types::*;
use vstd::prelude::*;

verus! {

// ───────────────────────────────────────────────────────────────────────────
// Memory isolation (non-interference) on the abstract `MachineState`.
//
// Layering (top-level reading order):
//   §0 threat model                  — `env_reachable`
//   §1 proof helpers                 — translation/ownership/word-arith bridges
//   §2 single-step isolation         — read/write non-interference, one env step
//   §3 maintenance                   — privacy is preserved along a run
//   §4 well-formedness along runs    — `wf` at every reachable state
//   §5 trace-level isolation         — §2 lifted to whole interleaved runs
//   §6 trace isolation from boot     — the "from-boot" corollaries
// Lemma order is irrelevant to verification; it follows the layering for reading.
// ───────────────────────────────────────────────────────────────────────────
impl MachineState {
    /// The `init` configuration (`step.rs`) is `wf`.  In `init` the VM population,
    /// ownership map, sharing graph, stage-2 map, and TLB are all empty,
    /// so every `wf` clause quantifies over an empty domain and holds vacuously.
    /// Base case of `reachable ⇒ wf`.
    pub proof fn lemma_init_wf(s: MachineState)
        requires
            MachineState::init(s),
        ensures
            s.wf(),
    {
        // `vm_owned` and `all_vms` are both empty, so their domains coincide.
        assert(s.vm_owned.dom() =~= s.all_vms());
        assert(s.ownership_wf());
        assert(s.sharing_wf());
        assert(s.translation_wf());
        assert(s.tlb_safe());
    }

    // ─────────────────────────────── §0 threat model ─────────────────────────
    /// `s2` is reachable from `s1` by one step of some VM *other than* `subject`.
    /// The subject-vs-environment split exists only here, to state isolation; it
    /// is not part of the machine state.
    pub open spec fn env_reachable(s1: MachineState, s2: MachineState, subject: VmId) -> bool {
        exists|vm: VmId, op: VmMemOp|
            vm != subject && #[trigger] MachineState::vm_step(s1, s2, vm, op)
    }

    // ─────────────────────────── §1 proof helpers ────────────────────────────
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
                    let e = choose|e: SharedPage| #[trigger]
                        s.shared_pages.contains(e) && e.page == page && (e.left == other || e.right
                            == other);
                    assert(s.shared_pages.contains(e) && e.page == page);
                    assert(false);
                }
            }
        }
    }

    /// **Translation confinement (shared core).** In any `wf` state, an environment
    /// VM (`other ≠ subject`) never holds a translation that resolves to a
    /// subject-private page — for *any* gpa, regardless of read/write intent.
    /// `translation_wf` routes `other`'s translation to a page it is entitled to
    /// (`lemma_translation_targets_owned`), and a subject-private page is owned or
    /// shared by no other VM (`lemma_private_excludes_other`).  This single
    /// access-control fact underlies both read confidentiality and write integrity.
    proof fn lemma_state_translation_confined(
        s: MachineState,
        subject: VmId,
        page: PhysPage,
        other: VmId,
        cpu: CpuId,
        gpa: GuestPage,
    )
        requires
            s.wf(),
            s.all_vms().contains(subject),
            other != subject,
            s.private_page(subject, page),
            s.effective_entry(cpu, other, gpa) is Some,
        ensures
            s.effective_entry(cpu, other, gpa)->Some_0.page != page,
    {
        // `other`'s translation lands on a page it owns or shares...
        Self::lemma_translation_targets_owned(s, cpu, other, gpa);
        // ...which a subject-private page never is.
        Self::lemma_private_excludes_other(s, subject, other, page);
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
            VmMemOp::Read(c, g) => {
                assert(MachineState::vm_read_step(s1, s2, vm, c, g));
            },
            VmMemOp::Write(c, g, v) => {
                assert(MachineState::vm_write_step(s1, s2, vm, c, g, v));
            },
            VmMemOp::HyperCall(c, r) => {
                assert(MachineState::vm_hypercall_step(s1, s2, vm, c, r));
            },
        }
    }

    // ──────────────────── §2 single-step isolation (primitives) ──────────────
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
        // `vm`'s read targets a page it is entitled to, not the subject-private one.
        Self::lemma_state_translation_confined(s2, subject, page, vm, cpu, gpa);
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
                assert(s2.read_observation(cpu, subject, gva) == s1.read_observation(
                    cpu,
                    subject,
                    gva,
                ));
            },
            VmMemOp::HyperCall(c, r) => {
                assert(MachineState::vm_hypercall_step(s1, s2, vmE, c, r));
                assert(s2.memory == s1.memory);
                assert(s2.read_observation(cpu, subject, gva) == s1.read_observation(
                    cpu,
                    subject,
                    gva,
                ));
            },
            VmMemOp::Write(cE, gE, v) => {
                assert(MachineState::vm_write_step(s1, s2, vmE, cE, gE, v));
                let paddrE = s1.translated_word(cE, vmE, gE)->Some_0;
                assert(s2.memory == s1.memory.insert(paddrE, v));
                // The env write targets an owned-or-shared page of `vmE`, which —
                // since the subject's page is private and `vmE ≠ subject` — differs.
                assert(s1.effective_entry(cE, vmE, gE.page()) is Some);
                let eEp = s1.effective_entry(cE, vmE, gE.page())->Some_0.page;
                Self::lemma_state_translation_confined(s1, subject, subj_page, vmE, cE, gE.page());
                assert(eEp != subj_page);
                assert(gE.offset() < PAGE_WORDS);
                Self::lemma_page_word_roundtrip(eEp, gE.offset());
                assert(paddrE.page() == eEp);
                assert(paddrE != subj_paddr);
                assert(s2.read_observation(cpu, subject, gva) == s1.read_observation(
                    cpu,
                    subject,
                    gva,
                ));
            },
        }
    }

    // ───────────── §3 maintenance: privacy is a run invariant (solves (a)) ────
    /// **Declassifying actions.** The actions that may legitimately
    /// strip `page`'s privacy from `subject`: sharing `page` with anyone, reclaiming
    /// `page` from the subject, or removing the subject VM.  Every *other* action —
    /// all guest steps and the remaining hypervisor ops — preserves
    /// `private_page(subject, page)` (see `lemma_step_preserves_private`).  This is
    /// the trusted-policy boundary: a secret stays secret until the hypervisor
    /// deliberately crosses it.
    pub open spec fn declassifies(action: MachineAction, subject: VmId, page: PhysPage) -> bool {
        match action {
            MachineAction::Hypervisor(op) => match op {
                HypervisorOp::SharePage(_l, _r, p) => p == page,
                HypervisorOp::ReclaimPage(vm, p) => vm == subject && p == page,
                HypervisorOp::RemoveVm(vm) => vm == subject,
                _ => false,
            },
            MachineAction::Vm(_vm, _op) => false,
        }
    }

    /// **Maintenance, all step kinds.** Any machine step whose action
    /// is not declassifying for `(subject, page)` preserves the subject's presence
    /// and the page's privacy.  Guest steps and `map`/`unmap`
    /// preserve ownership and the sharing graph outright; `assign` cannot target an
    /// owned page (ownership disjointness, from `wf`); a non-declassifying
    /// `reclaim`/`share`/`unshare`/`add_vm`/`remove_vm` touches only *other*
    /// pages/VMs/edges.
    pub proof fn lemma_step_preserves_private(
        s1: MachineState,
        s2: MachineState,
        action: MachineAction,
        subject: VmId,
        page: PhysPage,
    )
        requires
            MachineState::step(s1, s2, action),
            s1.all_vms().contains(subject),
            s1.private_page(subject, page),
            !MachineState::declassifies(action, subject, page),
        ensures
            s2.all_vms().contains(subject),
            s2.private_page(subject, page),
    {
        assert(s2.all_vms().contains(subject));
        assert(s2.private_page(subject, page));
    }

    /// **(a) solved — privacy is a run invariant.** Along any execution in which no
    /// action declassifies `(subject, page)`, the page is private to the
    /// still-present subject at *every* visited state.  This lifts the per-step
    /// maintenance (`lemma_step_preserves_private`) to whole interleaved runs by
    /// induction on the index — so a boot-time secret survives an arbitrary
    /// interleaving of guest and (non-declassifying) hypervisor steps.
    pub proof fn lemma_trace_preserves_private(
        trace: Seq<MachineState>,
        acts: Seq<MachineAction>,
        subject: VmId,
        page: PhysPage,
        k: int,
    )
        requires
            MachineState::is_execution(trace, acts),
            trace[0].all_vms().contains(subject),
            trace[0].private_page(subject, page),
            forall|i: int|
                0 <= i < acts.len() ==> !(#[trigger] MachineState::declassifies(
                    acts[i],
                    subject,
                    page,
                )),
            0 <= k < trace.len(),
        ensures
            trace[k].all_vms().contains(subject),
            trace[k].private_page(subject, page),
        decreases k,
    {
        if k > 0 {
            Self::lemma_trace_preserves_private(trace, acts, subject, page, k - 1);
            // Edge `i → i+1` with `i = k-1`: name `i` so the `is_execution` step
            // trigger (`step(trace[i], trace[i+1], acts[i])`) matches syntactically.
            let i = k - 1;
            assert(0 <= i < acts.len());
            assert(MachineState::step(trace[i], trace[i + 1], acts[i]));
            assert(trace[i + 1] == trace[k]);
            assert(!MachineState::declassifies(acts[i], subject, page));
            Self::lemma_step_preserves_private(trace[i], trace[k], acts[i], subject, page);
        }
    }

    // ─────────────────────── §4 well-formedness along runs ────────────────────
    /// Every state visited by an execution from a `wf` start is `wf`.
    /// Pointwise: each non-initial state is the post of a `step`, which conjoins
    /// `s2.wf()`; the initial state is `wf` by hypothesis.  (Combined with
    /// `lemma_init_wf`, a run from `init` is `wf` throughout.)
    pub proof fn lemma_execution_wf(trace: Seq<MachineState>, acts: Seq<MachineAction>, k: int)
        requires
            MachineState::is_execution(trace, acts),
            trace[0].wf(),
            0 <= k < trace.len(),
        ensures
            trace[k].wf(),
    {
        assert(trace.len() == acts.len() + 1);
        if k > 0 {
            let i = k - 1;
            assert(0 <= i < acts.len());
            assert(MachineState::step(trace[i], trace[i + 1], acts[i]));
            assert(trace[i + 1].wf());
            assert(trace[i + 1] == trace[k]);
        }
    }

    /// **Reachable ⇒ wf.** Combines `lemma_init_wf` with `lemma_execution_wf`: a
    /// reachable state's witnessing execution starts at
    /// `init` (hence `wf`), and `wf` propagates to its last state.
    pub proof fn lemma_reachable_wf(s: MachineState)
        requires
            MachineState::reachable(s),
        ensures
            s.wf(),
    {
        let (trace, acts) = choose|trace: Seq<MachineState>, acts: Seq<MachineAction>|
            {
                &&& MachineState::is_execution(trace, acts)
                &&& MachineState::init(trace[0])
                &&& trace[trace.len() - 1] == s
            };
        assert(trace.len() == acts.len() + 1);
        Self::lemma_init_wf(trace[0]);
        Self::lemma_execution_wf(trace, acts, trace.len() - 1);
    }

    /// **State-local read confinement.** In any `wf` state, an environment VM's
    /// successful read never resolves to a `subject`-private page.  This is the
    /// single-state core of read isolation — no step is involved — so it holds at
    /// *every* `wf` state in which the page is private, which is exactly what the
    /// run-level theorem instantiates along a trace.
    proof fn lemma_state_read_confined(
        s: MachineState,
        subject: VmId,
        page: PhysPage,
        vm: VmId,
        cpu: CpuId,
        gva: GuestWordAddr,
    )
        requires
            s.wf(),
            s.all_vms().contains(subject),
            s.all_vms().contains(vm),
            vm != subject,
            s.private_page(subject, page),
            s.read_observation(cpu, vm, gva) is Some,
        ensures
            s.translated_word(cpu, vm, gva)->Some_0.page() != page,
    {
        let gpa = gva.page();
        assert(s.translated_word(cpu, vm, gva) is Some);
        assert(s.effective_entry(cpu, vm, gpa) is Some);
        let ep = s.effective_entry(cpu, vm, gpa)->Some_0.page;
        // The read targets a page `vm` is entitled to, not the subject-private one
        // (shared confinement core).
        Self::lemma_state_translation_confined(s, subject, page, vm, cpu, gpa);
        assert(ep != page);
        assert(gva.offset() < PAGE_WORDS);
        Self::lemma_page_word_roundtrip(ep, gva.offset());
    }

    // ─────────────────────────── §5 trace-level isolation ─────────────────────
    /// **Trace confidentiality (read non-interference).** Along any execution
    /// from a `wf` start in which no action declassifies `(subject, page)`, at
    /// *every* visited state no environment VM (`vm ≠ subject`) can read `page`: a
    /// successful read resolves elsewhere.  Composes privacy maintenance
    /// (`lemma_trace_preserves_private`, i.e. the solution to (a)) with state-local
    /// confinement (`lemma_state_read_confined`).  Confidentiality is thus a *run
    /// invariant*, holding after an arbitrary interleaving of guest and
    /// non-declassifying hypervisor steps — not merely across one step.
    pub proof fn lemma_trace_read_isolation(
        trace: Seq<MachineState>,
        acts: Seq<MachineAction>,
        subject: VmId,
        page: PhysPage,
        k: int,
        vm: VmId,
        cpu: CpuId,
        gva: GuestWordAddr,
    )
        requires
            MachineState::is_execution(trace, acts),
            trace[0].wf(),
            trace[0].all_vms().contains(subject),
            trace[0].private_page(subject, page),
            forall|j: int|
                0 <= j < acts.len() ==> !(#[trigger] MachineState::declassifies(
                    acts[j],
                    subject,
                    page,
                )),
            0 <= k < trace.len(),
            trace[k].all_vms().contains(vm),
            vm != subject,
            trace[k].read_observation(cpu, vm, gva) is Some,
        ensures
            trace[k].translated_word(cpu, vm, gva)->Some_0.page() != page,
    {
        Self::lemma_execution_wf(trace, acts, k);
        Self::lemma_trace_preserves_private(trace, acts, subject, page, k);
        Self::lemma_state_read_confined(trace[k], subject, page, vm, cpu, gva);
    }

    /// **Trace integrity (write non-interference).** Along the same kind of
    /// run, at any *environment* edge `i → i+1` where the subject reads `gva` from
    /// the private `page`, the subject reads the *same* value after the edge — the
    /// environment cannot tamper with the subject's private data.  Per-edge by
    /// design: the subject's own and hypervisor steps may legitimately change the
    /// value, so the guarantee is precisely "no environment step changes it".
    pub proof fn lemma_trace_write_isolation(
        trace: Seq<MachineState>,
        acts: Seq<MachineAction>,
        subject: VmId,
        page: PhysPage,
        i: int,
        cpu: CpuId,
        gva: GuestWordAddr,
    )
        requires
            MachineState::is_execution(trace, acts),
            trace[0].wf(),
            trace[0].all_vms().contains(subject),
            trace[0].private_page(subject, page),
            forall|j: int|
                0 <= j < acts.len() ==> !(#[trigger] MachineState::declassifies(
                    acts[j],
                    subject,
                    page,
                )),
            0 <= i < acts.len(),
            MachineState::env_reachable(trace[i], trace[i + 1], subject),
            trace[i].read_observation(cpu, subject, gva) is Some,
            trace[i].effective_entry(cpu, subject, gva.page())->Some_0.page == page,
        ensures
            trace[i + 1].read_observation(cpu, subject, gva) == trace[i].read_observation(
                cpu,
                subject,
                gva,
            ),
    {
        Self::lemma_execution_wf(trace, acts, i);
        Self::lemma_trace_preserves_private(trace, acts, subject, page, i);
        // The subject's backing page is `page`, which the run keeps private, so write
        // isolation applies at this environment edge.
        assert(trace[i].private_page(
            subject,
            trace[i].effective_entry(cpu, subject, gva.page())->Some_0.page,
        ));
        Self::lemma_write_isolation(trace[i], trace[i + 1], subject, cpu, gva);
    }

    /// **Trace integrity across a stretch.** Over a run of *consecutive environment edges*
    /// `[m, n]`, the subject's read of a private backing page is unchanged at `n`
    /// from `m`: the environment cannot tamper with it over the whole stretch.
    /// Environment edges preserve translation (so the backing page stays `page`) and
    /// privacy, so single-edge integrity (`lemma_write_isolation`) chains by
    /// induction on the stretch length.
    pub proof fn lemma_trace_write_isolation_stretch(
        trace: Seq<MachineState>,
        acts: Seq<MachineAction>,
        subject: VmId,
        page: PhysPage,
        m: int,
        n: int,
        cpu: CpuId,
        gva: GuestWordAddr,
    )
        requires
            MachineState::is_execution(trace, acts),
            trace[0].wf(),
            0 <= m <= n,
            n < trace.len(),
            forall|i: int|
                m <= i < n ==> #[trigger] Self::env_reachable(trace[i], trace[i + 1], subject),
            trace[m].all_vms().contains(subject),
            trace[m].private_page(subject, page),
            trace[m].read_observation(cpu, subject, gva) is Some,
            trace[m].effective_entry(cpu, subject, gva.page())->Some_0.page == page,
        ensures
            trace[n].all_vms().contains(subject),
            trace[n].private_page(subject, page),
            trace[n].effective_entry(cpu, subject, gva.page())->Some_0.page == page,
            trace[n].read_observation(cpu, subject, gva) == trace[m].read_observation(
                cpu,
                subject,
                gva,
            ),
        decreases n - m,
    {
        if n > m {
            // Induction hypothesis on the prefix stretch `[m, n-1]`.
            Self::lemma_trace_write_isolation_stretch(
                trace,
                acts,
                subject,
                page,
                m,
                n - 1,
                cpu,
                gva,
            );
            // The edge `(n-1) → n` is an environment edge (bind `i` for the trigger).
            let i = n - 1;
            assert(m <= i < n);
            assert(Self::env_reachable(trace[i], trace[i + 1], subject));
            assert(trace[i + 1] == trace[n]);
            Self::lemma_execution_wf(trace, acts, i);
            // IH gives the backing page is `page` and private at `n-1`, so write
            // isolation preserves the value across this edge.
            assert(trace[i].private_page(
                subject,
                trace[i].effective_entry(cpu, subject, gva.page())->Some_0.page,
            ));
            Self::lemma_write_isolation(trace[i], trace[n], subject, cpu, gva);
            // The env edge preserves translation, so the backing page is still `page`.
            Self::lemma_env_step_facts(trace[i], trace[n], subject);
            assert(trace[n].s2_map == trace[i].s2_map && trace[n].tlb == trace[i].tlb);
            assert(trace[n].effective_entry(cpu, subject, gva.page()) == trace[i].effective_entry(
                cpu,
                subject,
                gva.page(),
            ));
            // ... and preserves the subject's presence and the page's privacy: the
            // env edge is a `step` by a non-subject VM (a `Vm` action never
            // declassifies), so the maintenance lemma applies directly.
            let (evm, eop) = choose|evm: VmId, eop: VmMemOp|
                evm != subject && MachineState::vm_step(trace[i], trace[n], evm, eop);
            assert(MachineState::vm_step(trace[i], trace[n], evm, eop));
            let eaction = MachineAction::Vm(evm, eop);
            assert(MachineState::step(trace[i], trace[n], eaction));
            assert(!MachineState::declassifies(eaction, subject, page));
            Self::lemma_step_preserves_private(trace[i], trace[n], eaction, subject, page);
        }
    }

    // ──────────────── §6 trace isolation anchored at reachable (from-boot) states ──
    /// **Reachable-state read confidentiality.** At any state reachable from `init`,
    /// while `page` is private to `subject`, no environment VM can read it.  This is
    /// the "from boot" form of trace confidentiality — combine with `lemma_trace_preserves_private`
    /// (privacy persists from the classification point) for the whole-run guarantee.
    pub proof fn lemma_reachable_read_isolation(
        s: MachineState,
        subject: VmId,
        page: PhysPage,
        vm: VmId,
        cpu: CpuId,
        gva: GuestWordAddr,
    )
        requires
            MachineState::reachable(s),
            s.all_vms().contains(subject),
            s.private_page(subject, page),
            s.all_vms().contains(vm),
            vm != subject,
            s.read_observation(cpu, vm, gva) is Some,
        ensures
            s.translated_word(cpu, vm, gva)->Some_0.page() != page,
    {
        Self::lemma_reachable_wf(s);
        Self::lemma_state_read_confined(s, subject, page, vm, cpu, gva);
    }

    /// **Reachable-state write integrity.** From any state reachable from `init`, an
    /// environment step cannot change the value the subject reads from a private
    /// backing page.
    pub proof fn lemma_reachable_write_isolation(
        s1: MachineState,
        s2: MachineState,
        subject: VmId,
        cpu: CpuId,
        gva: GuestWordAddr,
    )
        requires
            MachineState::reachable(s1),
            s1.all_vms().contains(subject),
            Self::env_reachable(s1, s2, subject),
            s1.read_observation(cpu, subject, gva) is Some,
            s1.private_page(subject, s1.effective_entry(cpu, subject, gva.page())->Some_0.page),
        ensures
            s2.read_observation(cpu, subject, gva) == s1.read_observation(cpu, subject, gva),
    {
        Self::lemma_reachable_wf(s1);
        Self::lemma_write_isolation(s1, s2, subject, cpu, gva);
    }

    // ───────────────────────── §7 DMA (IOMMU) isolation ───────────────────────
    /// **DMA translation confinement (general).** In any `wf` state, a resolved SMMU
    /// translation for `vm` lands on a page `vm` is entitled to DMA: one of its private
    /// DMA pages (`iommu_owned[vm]`) or a shared page (`iommu_shared`).  The SMMU analog
    /// of [`lemma_translation_targets_owned`](Self::lemma_translation_targets_owned):
    /// `iommu_tlb_safe` + `iommu_sync` route the effective entry to `iommu_s2_map`, and
    /// `iommu_translation_wf` confines its target.  Holds with a non-empty `iommu_shared`
    /// too, so it applies to the implementation projection.
    pub proof fn lemma_dma_translation_confined(
        s: MachineState,
        stream: CpuId,
        vm: VmId,
        gpa: GuestPage,
    )
        requires
            s.wf(),
            s.iommu_effective_entry(stream, vm, gpa) is Some,
        ensures
            s.all_vms().contains(vm),
            s.iommu_owned.contains_key(vm),
            s.iommu_owned[vm].contains(s.iommu_effective_entry(stream, vm, gpa)->Some_0.page)
                || s.iommu_shared.contains(s.iommu_effective_entry(stream, vm, gpa)->Some_0.page),
    {
        let key = TlbKey::new(stream, vm, gpa);
        let sk = VmPageKey::new(vm, gpa);
        // The effective DMA entry's page is the IOMMU stage-2 map's page for `(vm, gpa)`:
        // a cached SMMU-TLB entry agrees with the reachable map (`iommu_tlb_safe`), which
        // equals the software map (`iommu_sync`); otherwise the entry *is* the map entry.
        assert(s.iommu_s2_map.contains_key(sk) && s.iommu_effective_entry(
            stream,
            vm,
            gpa,
        )->Some_0.page == s.iommu_s2_map[sk].page) by {
            assert(s.iommu_sync());
            if s.iommu_tlb.contains_key(key) {
                assert(s.iommu_tlb_safe());
            }
        }
        // `iommu_translation_wf` at `sk` (note `sk.vm == vm`) gives ownership/sharing.
        assert(s.iommu_translation_wf());
    }

    /// **State-local DMA isolation.** In any `wf` state, a device operating for `vm`
    /// never resolves an SMMU translation onto a page that a *different* VM privately
    /// owns — CPU-owned (`vm_owned[subject]`) or DMA-owned (`iommu_owned[subject]`) —
    /// **even when the shared GIC region is present** (`iommu_shared` non-empty).
    ///
    /// Confinement (`lemma_dma_translation_confined`) lands the target in
    /// `iommu_owned[vm] ∪ iommu_shared`, and all four `iommu_ownership_wf` clauses keep
    /// both parts off `subject`'s private pages: a private-DMA target by clauses (1)/(2)
    /// (cross-VM DMA disjoint; DMA never another VM's CPU page), and a shared (GIC)
    /// target by clauses (3)/(4) (the shared region is disjoint from every VM's DMA and
    /// CPU ownership — the GIC is a device region, never a VM's private RAM).
    pub proof fn lemma_state_dma_isolation(
        s: MachineState,
        subject: VmId,
        page: PhysPage,
        vm: VmId,
        stream: CpuId,
        gpa: GuestPage,
    )
        requires
            s.wf(),
            s.all_vms().contains(subject),
            vm != subject,
            s.vm_owned[subject].contains(page) || s.iommu_owned[subject].contains(page),
            s.iommu_effective_entry(stream, vm, gpa) is Some,
        ensures
            s.iommu_effective_entry(stream, vm, gpa)->Some_0.page != page,
    {
        let target = s.iommu_effective_entry(stream, vm, gpa)->Some_0.page;
        Self::lemma_dma_translation_confined(s, stream, vm, gpa);
        assert(s.all_vms().contains(vm));
        assert(s.iommu_ownership_wf());
        // The DMA target is in `iommu_owned[vm] ∪ iommu_shared`; in either case ownership
        // separation keeps it off everything `subject` privately owns.
        assert(!s.iommu_owned[subject].contains(target) && !s.vm_owned[subject].contains(target))
            by {
            if s.iommu_owned[vm].contains(target) {
                // clauses (1) & (2) at `(vm, subject)`.
                assert(!s.iommu_owned[subject].contains(target));
                assert(!s.vm_owned[subject].contains(target));
            } else {
                assert(s.iommu_shared.contains(target));
                // clauses (3) & (4) at `subject` (contrapositive): a shared page is
                // neither `subject`'s DMA nor CPU page.
                if s.iommu_owned[subject].contains(target) {
                    assert(false);
                }
                if s.vm_owned[subject].contains(target) {
                    assert(false);
                }
            }
        }
    }

    /// Every state along an execution from an `iommu_shared`-empty start has an empty
    /// `iommu_shared`: every step frames it unchanged (the DMA-sharing set is static).
    pub proof fn lemma_execution_iommu_shared_empty(
        trace: Seq<MachineState>,
        acts: Seq<MachineAction>,
        k: int,
    )
        requires
            MachineState::is_execution(trace, acts),
            trace[0].iommu_shared == Set::<PhysPage>::empty(),
            0 <= k < trace.len(),
        ensures
            trace[k].iommu_shared == Set::<PhysPage>::empty(),
        decreases k,
    {
        if k > 0 {
            Self::lemma_execution_iommu_shared_empty(trace, acts, k - 1);
            let i = k - 1;
            assert(0 <= i < acts.len());
            assert(MachineState::step(trace[i], trace[i + 1], acts[i]));
            assert(trace[i + 1].iommu_shared == trace[i].iommu_shared);
            assert(trace[i + 1] == trace[k]);
        }
    }

    /// **Reachable ⇒ no IOMMU-shared pages.** `init` starts with an empty `iommu_shared`
    /// and every step frames it, so it is empty at every reachable state.
    pub proof fn lemma_reachable_iommu_shared_empty(s: MachineState)
        requires
            MachineState::reachable(s),
        ensures
            s.iommu_shared == Set::<PhysPage>::empty(),
    {
        let (trace, acts) = choose|trace: Seq<MachineState>, acts: Seq<MachineAction>|
            {
                &&& MachineState::is_execution(trace, acts)
                &&& MachineState::init(trace[0])
                &&& trace[trace.len() - 1] == s
            };
        assert(trace.len() == acts.len() + 1);
        assert(MachineState::init(trace[0]));
        Self::lemma_execution_iommu_shared_empty(trace, acts, trace.len() - 1);
    }

    /// **Reachable-state DMA isolation — the payoff.** From any state reachable from
    /// `init`, a device operating for `vm` cannot DMA into a page that a *different* VM
    /// `subject` privately owns (CPU- or DMA-owned) — with the shared GIC present or not.
    /// `reachable ⇒ wf` plus the state-local DMA isolation.
    pub proof fn lemma_reachable_dma_isolation(
        s: MachineState,
        subject: VmId,
        page: PhysPage,
        vm: VmId,
        stream: CpuId,
        gpa: GuestPage,
    )
        requires
            MachineState::reachable(s),
            s.all_vms().contains(subject),
            vm != subject,
            s.vm_owned[subject].contains(page) || s.iommu_owned[subject].contains(page),
            s.iommu_effective_entry(stream, vm, gpa) is Some,
        ensures
            s.iommu_effective_entry(stream, vm, gpa)->Some_0.page != page,
    {
        Self::lemma_reachable_wf(s);
        Self::lemma_state_dma_isolation(s, subject, page, vm, stream, gpa);
    }
}

} // verus!
