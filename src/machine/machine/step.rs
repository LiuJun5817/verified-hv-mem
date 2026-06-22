use vstd::prelude::*;

use super::state::MachineState;
use crate::machine::types::*;

verus! {

// ---------------------------------------------------------------------------
// High-level machine step functions
//
// These predicates are defined on the combined `MachineState` (produced by
// `assemble(sw, hw)`).  They capture the full observable effect of each
// operation — SW-state changes plus any HW-state side-effects.  TLB management
// is folded synchronously into `hv_map` / `hv_unmap` (a SW–HW cowork): a mapping
// edit flushes the stale TLB entries, so there are no standalone TLB steps and no
// pending-invalidation state.
//
// The refinement proofs in `refine.rs` show that executing a SW step together
// with the matching HW step implies the corresponding predicate here.
// ---------------------------------------------------------------------------
impl MachineState {
    // ------------------------------------------------------------------
    // VM memory operations  (one unified VM step — no subject/environment split)
    // ------------------------------------------------------------------
    pub open spec fn vm_read_step(
        s1: Self,
        s2: Self,
        vm: VmId,
        cpu: CpuId,
        gva: GuestWordAddr,
    ) -> bool {
        &&& s1.wf()
        &&& s1.cpu_runs(cpu, vm)
        &&& s1.read_observation(cpu, vm, gva) is Some
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.same_ownership_as(&s1)
        &&& s2.same_translation_as(&s1)
        &&& s2.same_memory_as(&s1)
    }

    pub open spec fn vm_write_step(
        s1: Self,
        s2: Self,
        vm: VmId,
        cpu: CpuId,
        gva: GuestWordAddr,
        value: DataWord,
    ) -> bool {
        let paddr = s1.translated_word(cpu, vm, gva);
        &&& s1.wf()
        &&& s1.cpu_runs(cpu, vm)
        &&& paddr is Some
        &&& s1.can_write(cpu, vm, gva)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.same_ownership_as(&s1)
        &&& s2.same_translation_as(&s1)
        &&& s2.memory == s1.memory.insert(paddr->Some_0, value)
    }

    /// Guest-originated hypercalls are modelled as requests; their semantic
    /// effect is captured by the subsequent hypervisor transition.
    pub open spec fn vm_hypercall_step(
        s1: Self,
        s2: Self,
        vm: VmId,
        cpu: CpuId,
        _req: HyperCallReq,
    ) -> bool {
        &&& s1.wf()
        &&& s1.cpu_runs(cpu, vm)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.same_ownership_as(&s1)
        &&& s2.same_translation_as(&s1)
        &&& s2.same_memory_as(&s1)
    }

    /// A single guest VM (`vm`) executes a memory operation.
    ///
    /// # Why one multi-cycle op is modelled as one atomic step (reduction)
    ///
    /// A real read/write/hypercall takes many cycles, yet each is one `vm_step`.
    /// This is sound by the single-shared-commit (Lipton) rule: a transition that
    /// touches observable shared state *at most once* is observationally equivalent
    /// to its fine-grained decomposition, because no interleaving can fall between
    /// two shared effects when there is only one.  Each VM step meets this:
    /// `vm_read`/`vm_hypercall` mutate nothing (`same_memory_as`), and `vm_write`
    /// has the single effect `memory.insert(paddr, value)` while holding translation
    /// fixed (`same_translation_as`), so it does not straddle two structural commits.
    /// Operations that *would* have several commits are already split: a multi-word
    /// or unaligned access is several `vm_step`s, and a hypercall is a request step
    /// (no effect) plus a separate hypervisor service step.  The atomicity of a
    /// single aligned word is the underlying hardware guarantee.
    ///
    /// # This is an access-control abstraction, not a memory-consistency model
    ///
    /// A `vm_step` is one **single-word, single-copy-atomic** access, and the
    /// machine evolves by the *nondeterministic interleaving* of such steps
    /// (`MachineState::step` fires exactly one action per tick).  Two facts about
    /// what that does and does not model:
    ///
    /// * **Faithful — inter-CPU coherence on one location.**  Two CPUs writing the
    ///   same address become two sequential `memory.insert`s in *some* order; the
    ///   relation admits both, and nothing prefers either.  That undetermined order
    ///   *is* Arm's coherence order for a single location, so the model is exact
    ///   here.  A `DataWord`-granular insert matches single-copy atomicity of an
    ///   aligned word (no tearing).
    /// * **Over-approximation — program order and cross-location weak memory.**  The
    ///   model has no program counter or per-CPU instruction stream, so a single
    ///   CPU's same-location accesses are *not* ordered (Arm orders them), and
    ///   cross-location relaxations (store buffering, non-multi-copy-atomicity,
    ///   reordering) are not modelled at all.  This forgets order, i.e. admits a
    ///   *superset* of hardware behaviours — sound for a reachability/safety
    ///   property, but it means no program-order- or data-flow-dependent guest
    ///   property may be stated against this model.
    ///
    /// The isolation theorems (`security::lemma_read_isolation`/`lemma_write_isolation`)
    /// are per-state access-right invariants over a *single* step, so they are
    /// order-agnostic by construction and need none of the dropped guarantees.
    /// Capturing program order would require adding per-CPU sequencing — a genuine
    /// memory-model refinement, out of scope for this access-control proof.
    pub open spec fn vm_step(s1: Self, s2: Self, vm: VmId, op: VmMemOp) -> bool {
        &&& s1.all_vms().contains(vm)
        &&& match op {
            VmMemOp::Read(cpu, gva) => Self::vm_read_step(s1, s2, vm, cpu, gva),
            VmMemOp::Write(cpu, gva, value) => Self::vm_write_step(s1, s2, vm, cpu, gva, value),
            VmMemOp::HyperCall(cpu, req) => Self::vm_hypercall_step(s1, s2, vm, cpu, req),
        }
    }

    // ------------------------------------------------------------------
    // Hypervisor operations
    // ------------------------------------------------------------------
    pub open spec fn hv_map_step(
        s1: Self,
        s2: Self,
        vm: VmId,
        gpa: GuestPage,
        entry: S2Entry,
    ) -> bool {
        let key = VmPageKey::new(vm, gpa);
        &&& s1.wf()
        &&& s1.all_vms().contains(vm)
        &&& s1.owned_or_shared(vm, entry.page)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.same_ownership_as(&s1)
        &&& s2.same_memory_as(&s1)
        &&& s2.active_vm == s1.active_vm
        &&& s2.s2_map == s1.s2_map.insert(
            key,
            entry,
        )
        // synchronous TLB invalidation of the edited mapping
        &&& s2.tlb == s1.tlb.remove_keys(s1.invalidation_targets(vm, gpa))
    }

    /// # TLB invalidation is modelled as atomic and global
    ///
    /// The same step edits `s2_map` and flushes *every* CPU's stale entry for
    /// `(vm, gpa)` via `invalidation_targets`.  So no reachable state holds a stale
    /// entry (`tlb_safe` is part of `wf` and is preserved), and a CPU sees the
    /// page-table and TLB updates simultaneously — there is no "being-invalidated"
    /// window in the model.
    ///
    /// Real hardware has an asynchronous shootdown window (invalidate, wait for all
    /// CPUs to acknowledge, only then free the page).  That window is not modelled as
    /// stale state; it is discharged by two ordering facts instead: this synchronous
    /// flush, and `page_is_quiescent` gating `hv_reclaim_page_step` (a page is freed
    /// only when no `s2_map`/TLB/sharing reference to it remains).  Soundness of the
    /// abstraction therefore pushes a *break-before-make* obligation onto the
    /// implementation: the abstract atomic step corresponds to "all CPUs have acked
    /// the invalidation", not to instantaneous wall-clock invalidation.  A faithful
    /// async model would reuse `HwView::pending_invalidations` — split the flush into
    /// a broadcast step plus per-CPU acks, weaken `tlb_safe` to "coherent except for
    /// pending keys", and require `pending` empty for the page at reclaim — a
    /// memory-model refinement reserved for future work.
    pub open spec fn hv_unmap_step(s1: Self, s2: Self, vm: VmId, gpa: GuestPage) -> bool {
        let key = VmPageKey::new(vm, gpa);
        &&& s1.wf()
        &&& s1.s2_map.contains_key(key)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.same_ownership_as(&s1)
        &&& s2.same_memory_as(&s1)
        &&& s2.active_vm == s1.active_vm
        &&& s2.s2_map == s1.s2_map.remove(key)
        &&& s2.tlb == s1.tlb.remove_keys(s1.invalidation_targets(vm, gpa))
    }

    pub open spec fn hv_assign_page_step(s1: Self, s2: Self, vm: VmId, page: PhysPage) -> bool {
        &&& s1.wf()
        &&& s1.all_vms().contains(vm)
        &&& s1.hypervisor_owned.contains(page)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.same_translation_as(&s1)
        &&& s2.same_memory_as(&s1)
        &&& s2.hypervisor_owned == s1.hypervisor_owned.remove(page)
        &&& s2.shared_pages == s1.shared_pages
        &&& s2.vm_owned == s1.vm_owned.insert(vm, s1.vm_owned[vm].insert(page))
    }

    pub open spec fn hv_reclaim_page_step(s1: Self, s2: Self, vm: VmId, page: PhysPage) -> bool {
        &&& s1.wf()
        &&& s1.all_vms().contains(vm)
        &&& s1.vm_owned[vm].contains(page)
        &&& s1.page_is_quiescent(page)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.same_translation_as(&s1)
        &&& s2.same_memory_as(&s1)
        &&& s2.shared_pages == s1.shared_pages
        &&& s2.hypervisor_owned == s1.hypervisor_owned.insert(page)
        &&& s2.vm_owned == s1.vm_owned.insert(vm, s1.vm_owned[vm].remove(page))
    }

    pub open spec fn hv_share_page_step(
        s1: Self,
        s2: Self,
        left: VmId,
        right: VmId,
        page: PhysPage,
    ) -> bool {
        let edge = SharedPage { left, right, page };
        let rev = edge.reverse();
        &&& s1.wf()
        &&& left != right
        &&& s1.all_vms().contains(left)
        &&& s1.all_vms().contains(right)
        &&& s1.vm_owned[left].contains(page)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.hypervisor_owned == s1.hypervisor_owned
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.same_translation_as(&s1)
        &&& s2.same_memory_as(&s1)
        &&& s2.shared_pages == s1.shared_pages.insert(edge).insert(rev)
    }

    pub open spec fn hv_unshare_page_step(
        s1: Self,
        s2: Self,
        left: VmId,
        right: VmId,
        page: PhysPage,
    ) -> bool {
        let edge = SharedPage { left, right, page };
        let rev = edge.reverse();
        &&& s1.wf()
        &&& s1.shared_pages.contains(edge)
        &&& s1.shared_pages.contains(
            rev,
        )
        // No dangling translation: if an endpoint of the edge maps `page`, it must
        // *own* it, so dropping the share strands nothing (cf. `reclaim`'s quiescence).
        &&& forall|k: VmPageKey| #[trigger]
            s1.s2_map.contains_key(k) && (k.vm == left || k.vm == right) && s1.s2_map[k].page
                == page ==> s1.vm_owned[k.vm].contains(page)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.hypervisor_owned == s1.hypervisor_owned
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.same_translation_as(&s1)
        &&& s2.same_memory_as(&s1)
        &&& s2.shared_pages == s1.shared_pages.remove(edge).remove(rev)
    }

    pub open spec fn hv_context_switch_step(s1: Self, s2: Self, cpu: CpuId, vm: VmId) -> bool {
        &&& s1.wf()
        &&& s1.all_vms().contains(vm)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.same_ownership_as(&s1)
        &&& s2.same_memory_as(&s1)
        &&& s2.s2_map == s1.s2_map
        &&& s2.tlb == s1.tlb
        &&& s2.active_vm == s1.active_vm.insert(cpu, vm)
    }

    /// Register a fresh, empty VM (dynamic VM set).
    pub open spec fn hv_add_vm_step(s1: Self, s2: Self, vm: VmId) -> bool {
        &&& s1.wf()
        &&& !s1.all_vms().contains(vm)
        &&& s2.wf()
        &&& s2.all_vms == s1.all_vms.insert(vm)
        &&& s2.hypervisor_owned == s1.hypervisor_owned
        &&& s2.vm_owned == s1.vm_owned.insert(vm, Set::empty())
        &&& s2.shared_pages == s1.shared_pages
        &&& s2.same_translation_as(&s1)
        &&& s2.same_memory_as(&s1)
    }

    /// Deregister a VM that owns nothing, maps nothing, shares nothing, and runs
    /// on no CPU.
    pub open spec fn hv_remove_vm_step(s1: Self, s2: Self, vm: VmId) -> bool {
        &&& s1.wf()
        &&& s1.all_vms().contains(vm)
        &&& s1.vm_owned[vm] == Set::<PhysPage>::empty()
        &&& (forall|k: VmPageKey| #[trigger] s1.s2_map.contains_key(k) ==> k.vm != vm)
        &&& (forall|k: TlbKey| #[trigger] s1.tlb.contains_key(k) ==> k.vm != vm)
        &&& (forall|e: SharedPage| #[trigger]
            s1.shared_pages.contains(e) ==> e.left != vm && e.right != vm)
        &&& (forall|cpu: CpuId| #[trigger]
            s1.active_vm.contains_key(cpu) ==> s1.active_vm[cpu] != vm)
        &&& s2.wf()
        &&& s2.all_vms == s1.all_vms.remove(vm)
        &&& s2.hypervisor_owned == s1.hypervisor_owned
        &&& s2.vm_owned == s1.vm_owned.remove(vm)
        &&& s2.shared_pages == s1.shared_pages
        &&& s2.same_translation_as(&s1)
        &&& s2.same_memory_as(&s1)
    }

    pub open spec fn hypervisor_step(s1: Self, s2: Self, op: HypervisorOp) -> bool {
        match op {
            HypervisorOp::Map(vm, gpa, entry) => Self::hv_map_step(s1, s2, vm, gpa, entry),
            HypervisorOp::Unmap(vm, gpa) => Self::hv_unmap_step(s1, s2, vm, gpa),
            HypervisorOp::AssignPage(vm, page) => Self::hv_assign_page_step(s1, s2, vm, page),
            HypervisorOp::ReclaimPage(vm, page) => Self::hv_reclaim_page_step(s1, s2, vm, page),
            HypervisorOp::SharePage(left, right, page) => {
                Self::hv_share_page_step(s1, s2, left, right, page)
            },
            HypervisorOp::UnsharePage(left, right, page) => {
                Self::hv_unshare_page_step(s1, s2, left, right, page)
            },
            HypervisorOp::ContextSwitch(cpu, vm) => Self::hv_context_switch_step(s1, s2, cpu, vm),
            HypervisorOp::AddVm(vm) => Self::hv_add_vm_step(s1, s2, vm),
            HypervisorOp::RemoveVm(vm) => Self::hv_remove_vm_step(s1, s2, vm),
        }
    }

    // ------------------------------------------------------------------
    // Initial state  (the special "boot" step: a post-state with no pre-state)
    // ------------------------------------------------------------------
    /// The initial machine configuration — the base case of `reachable`, and the
    /// state-machine `Init` to `step`'s `Next`.
    ///
    /// Unlike the `*_step` predicates this is *post-only*: it constrains a single
    /// state rather than a transition.  At boot no guest exists yet, so the VM
    /// population, ownership map, sharing graph, stage-2 map, TLB and CPU schedule
    /// are all empty; every `wf` clause is then a `forall` over an empty domain and
    /// holds vacuously (see `lemma_init_wf` in `refine.rs`).  `hypervisor_owned`
    /// (the free pool) and `memory` (initial DRAM) are left unconstrained — they are
    /// platform data irrelevant to `wf`.  Guests and mappings are subsequently
    /// created by `hv_add_vm` / `hv_assign_page` / `hv_map`.
    pub open spec fn init(s: Self) -> bool {
        &&& s.all_vms == Set::<VmId>::empty()
        &&& s.vm_owned == Map::<VmId, Set<PhysPage>>::empty()
        &&& s.shared_pages == Set::<SharedPage>::empty()
        &&& s.s2_map == Map::<VmPageKey, S2Entry>::empty()
        &&& s.tlb == Map::<TlbKey, TlbEntry>::empty()
        &&& s.active_vm == Map::<CpuId, VmId>::empty()
    }

    // ------------------------------------------------------------------
    // Top-level step dispatch
    // ------------------------------------------------------------------
    pub open spec fn step(s1: Self, s2: Self, action: MachineAction) -> bool {
        match action {
            MachineAction::Vm(vm, op) => Self::vm_step(s1, s2, vm, op),
            MachineAction::Hypervisor(op) => Self::hypervisor_step(s1, s2, op),
        }
    }

    /// A finite execution: `trace` are the visited states and `acts[i]` drives the
    /// edge `trace[i] → trace[i+1]`.  The `init` base state is not required here — a
    /// caller wanting a run from boot additionally conjoins `init(trace[0])`.
    pub open spec fn is_execution(trace: Seq<MachineState>, acts: Seq<MachineAction>) -> bool {
        &&& trace.len() == acts.len() + 1
        &&& forall|i: int| 0 <= i < acts.len() ==> #[trigger] MachineState::step(
            trace[i],
            trace[i + 1],
            acts[i],
        )
    }

    /// A state is **reachable** if some execution starting from an `init` state ends
    /// in it.  (`lemma_reachable_wf`: every reachable state is `wf`.)
    pub open spec fn reachable(s: MachineState) -> bool {
        exists|trace: Seq<MachineState>, acts: Seq<MachineAction>|
            {
                &&& MachineState::is_execution(trace, acts)
                &&& MachineState::init(trace[0])
                &&& trace[trace.len() - 1] == s
            }
    }
}

} // verus!
