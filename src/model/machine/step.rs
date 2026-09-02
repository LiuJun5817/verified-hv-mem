use vstd::prelude::*;

use super::state::MachineState;
use crate::model::types::{
    CpuId, DataWord, GuestPage, GuestWordAddr, HypervisorOp, MachineAction, PhysPage, S2Entry,
    TlbEntry, TlbKey, VmId, VmMemOp, VmPageKey,
};

verus! {

// ---------------------------------------------------------------------------
// High-level machine step functions
//
// These predicates are defined on the combined `MachineState` (produced by
// `assemble(sw, hw)`).  They capture the full observable effect of each
// operation — SW-state changes plus any HW-state side-effects.  TLB management
// is folded synchronously into each mapping operation (a SW–HW cowork): a mapping
// edit flushes the stale TLB entries, so there are no standalone TLB steps and no
// pending-invalidation state.
//
// The refinement proofs in `crate::refinement` show that executing a SW step together
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
        &&& paddr is Some
        &&& s1.can_write(cpu, vm, gva)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.same_ownership_as(&s1)
        &&& s2.same_translation_as(&s1)
        &&& s2.memory == s1.memory.insert(paddr->Some_0, value)
    }

    /// A single guest VM (`vm`) executes a memory operation.
    ///
    /// # Why one multi-cycle op is modelled as one atomic step (reduction)
    ///
    /// A real read/write takes many cycles, yet each is one `vm_step`.
    /// This is sound by the single-shared-commit (Lipton) rule: a transition that
    /// touches observable shared state *at most once* is observationally equivalent
    /// to its fine-grained decomposition, because no interleaving can fall between
    /// two shared effects when there is only one.  Each VM step meets this:
    /// `vm_read` mutates nothing (`same_memory_as`), and `vm_write`
    /// has the single effect `memory.insert(paddr, value)` while holding translation
    /// fixed (`same_translation_as`), so it does not straddle two structural commits.
    /// Operations that *would* have several commits are already split: a multi-word
    /// or unaligned access is several `vm_step`s. The atomicity of a single aligned
    /// word is the underlying hardware guarantee.
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
        }
    }

    // ------------------------------------------------------------------
    // Hypervisor operations
    // ------------------------------------------------------------------
    /// Atomically classify one physical page as VM-private and install its CPU
    /// stage-2 mapping. The same VM may already classify the page as IOMMU-private,
    /// but no CPU-private or shared projection may already contain it.
    pub open spec fn hv_map_vm_private_step(
        s1: Self,
        s2: Self,
        vm: VmId,
        gpa: GuestPage,
        entry: S2Entry,
    ) -> bool {
        let key = VmPageKey::new(vm, gpa);
        &&& s1.wf()
        &&& s1.all_vms().contains(vm)
        &&& !s1.s2_map.contains_key(key)
        &&& (forall|v: VmId| #[trigger]
            s1.all_vms().contains(v) ==> !s1.vm_owned[v].contains(entry.page))
        &&& !s1.vm_shared.contains(entry.page)
        &&& (forall|v: VmId| #[trigger]
            s1.all_vms().contains(v) && v != vm ==> !s1.iommu_owned[v].contains(entry.page))
        &&& !s1.iommu_shared.contains(entry.page)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.same_memory_as(&s1)
        &&& s2.vm_owned == s1.vm_owned.insert(vm, s1.vm_owned[vm].insert(entry.page))
        &&& s2.vm_shared == s1.vm_shared
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared
        &&& s2.s2_map == s1.s2_map.insert(key, entry)
        // the hardware-reachable map catches up in the same atomic step (sync preserved)
        &&& s2.hw_s2map == s1.hw_s2map.insert(key, entry)
        // synchronous TLB invalidation of the edited mapping
        &&& s2.tlb == s1.tlb.remove_keys(s1.invalidation_targets(vm, gpa))
        // CPU stage-2 maintenance leaves IOMMU translation state untouched.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_hw_s2map == s1.iommu_hw_s2map
        &&& s2.iommu_tlb == s1.iommu_tlb
    }

    /// # TLB invalidation is modelled as atomic and global
    ///
    /// The same step removes the VM-private classification and `s2_map` entry,
    /// then flushes *every* CPU's stale entry for `(vm, gpa)` via
    /// `invalidation_targets`. Thus a CPU sees the ownership, page-table, and TLB
    /// updates simultaneously; there is no "being-invalidated" window in the model.
    ///
    /// Real hardware has an asynchronous shootdown window (invalidate, wait for all
    /// CPUs to acknowledge, only then release the page). The atomic step represents
    /// completion of that sequence. A faithful asynchronous model would add pending
    /// invalidations and per-CPU acknowledgements; that memory-model refinement is
    /// reserved for future work.
    pub open spec fn hv_unmap_vm_private_step(
        s1: Self,
        s2: Self,
        vm: VmId,
        gpa: GuestPage,
        page: PhysPage,
    ) -> bool {
        let key = VmPageKey::new(vm, gpa);
        let post_map = s1.s2_map.remove(key);
        &&& s1.wf()
        &&& s1.all_vms().contains(vm)
        &&& s1.s2_map.contains_key(key)
        &&& s1.s2_map[key].page == page
        &&& s1.vm_owned[vm].contains(page)
        &&& !s1.vm_shared.contains(page)
        &&& (forall|k: VmPageKey| #[trigger]
            post_map.contains_key(k) ==> post_map[k].page != page)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.same_memory_as(&s1)
        &&& s2.vm_owned == s1.vm_owned.insert(vm, s1.vm_owned[vm].remove(page))
        &&& s2.vm_shared == s1.vm_shared
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared
        &&& s2.s2_map == post_map
        &&& s2.hw_s2map == s1.hw_s2map.remove(key)
        &&& s2.tlb == s1.tlb.remove_keys(s1.invalidation_targets(vm, gpa))
        // CPU stage-2 maintenance leaves IOMMU translation state untouched.
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_hw_s2map == s1.iommu_hw_s2map
        &&& s2.iommu_tlb == s1.iommu_tlb
    }

    /// Atomically install a CPU mapping to global-shared memory and record its
    /// target in the dynamic `vm_shared` projection. Physical aliases are
    /// idempotent because the projection is a set.
    pub open spec fn hv_map_global_shared_step(
        s1: Self,
        s2: Self,
        vm: VmId,
        gpa: GuestPage,
        entry: S2Entry,
    ) -> bool {
        let key = VmPageKey::new(vm, gpa);
        &&& s1.wf()
        &&& s1.all_vms().contains(vm)
        &&& (forall|v: VmId| #[trigger]
            s1.all_vms().contains(v) ==> !s1.vm_owned[v].contains(entry.page)
                && !s1.iommu_owned[v].contains(entry.page))
        &&& !s1.s2_map.contains_key(key)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.same_memory_as(&s1)
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.vm_shared == s1.vm_shared.insert(entry.page)
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared
        &&& s2.s2_map == s1.s2_map.insert(key, entry)
        &&& s2.hw_s2map == s1.hw_s2map.insert(key, entry)
        &&& s2.tlb == s1.tlb.remove_keys(s1.invalidation_targets(vm, gpa))
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_hw_s2map == s1.iommu_hw_s2map
        &&& s2.iommu_tlb == s1.iommu_tlb
    }

    /// Atomically remove a CPU global-shared mapping and drop its physical page
    /// from `vm_shared` only when no surviving CPU mapping targets that page.
    pub open spec fn hv_unmap_global_shared_step(
        s1: Self,
        s2: Self,
        vm: VmId,
        gpa: GuestPage,
    ) -> bool {
        let key = VmPageKey::new(vm, gpa);
        let page = s1.s2_map[key].page;
        let post_map = s1.s2_map.remove(key);
        let aliased = exists|k: VmPageKey| #[trigger]
            post_map.contains_key(k) && post_map[k].page == page;
        &&& s1.wf()
        &&& s1.s2_map.contains_key(key)
        &&& s1.vm_shared.contains(page)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.same_memory_as(&s1)
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.vm_shared == if aliased { s1.vm_shared } else { s1.vm_shared.remove(page) }
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared
        &&& s2.s2_map == post_map
        &&& s2.hw_s2map == s1.hw_s2map.remove(key)
        &&& s2.tlb == s1.tlb.remove_keys(s1.invalidation_targets(vm, gpa))
        &&& s2.iommu_s2_map == s1.iommu_s2_map
        &&& s2.iommu_hw_s2map == s1.iommu_hw_s2map
        &&& s2.iommu_tlb == s1.iommu_tlb
    }

    /// Atomically classify one physical page as VM-private for DMA and install
    /// its IOMMU mapping. The same VM may already classify the page CPU-private.
    pub open spec fn hv_iommu_map_vm_private_step(
        s1: Self,
        s2: Self,
        vm: VmId,
        gpa: GuestPage,
        entry: S2Entry,
    ) -> bool {
        let key = VmPageKey::new(vm, gpa);
        &&& s1.wf()
        &&& s1.all_vms().contains(vm)
        &&& !s1.iommu_s2_map.contains_key(key)
        &&& (forall|v: VmId| #[trigger]
            s1.all_vms().contains(v) ==> !s1.iommu_owned[v].contains(entry.page))
        &&& (forall|v: VmId| #[trigger]
            s1.all_vms().contains(v) && v != vm ==> !s1.vm_owned[v].contains(entry.page))
        &&& !s1.vm_shared.contains(entry.page)
        &&& !s1.iommu_shared.contains(entry.page)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.same_memory_as(&s1)
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.vm_shared == s1.vm_shared
        &&& s2.iommu_owned
            == s1.iommu_owned.insert(vm, s1.iommu_owned[vm].insert(entry.page))
        &&& s2.iommu_shared == s1.iommu_shared
        &&& s2.s2_map == s1.s2_map
        &&& s2.hw_s2map == s1.hw_s2map
        &&& s2.tlb == s1.tlb
        &&& s2.iommu_s2_map == s1.iommu_s2_map.insert(key, entry)
        &&& s2.iommu_hw_s2map == s1.iommu_hw_s2map.insert(key, entry)
        &&& s2.iommu_tlb == s1.iommu_tlb.remove_keys(s1.iommu_invalidation_targets(vm, gpa))
    }

    /// Atomically remove one VM-private IOMMU mapping and release its DMA-private
    /// classification. No other IOMMU mapping may target the released page.
    pub open spec fn hv_iommu_unmap_vm_private_step(
        s1: Self,
        s2: Self,
        vm: VmId,
        gpa: GuestPage,
        page: PhysPage,
    ) -> bool {
        let key = VmPageKey::new(vm, gpa);
        let post_map = s1.iommu_s2_map.remove(key);
        &&& s1.wf()
        &&& s1.all_vms().contains(vm)
        &&& s1.iommu_s2_map.contains_key(key)
        &&& s1.iommu_s2_map[key].page == page
        &&& s1.iommu_owned[vm].contains(page)
        &&& !s1.iommu_shared.contains(page)
        &&& (forall|k: VmPageKey| #[trigger]
            post_map.contains_key(k) ==> post_map[k].page != page)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.same_memory_as(&s1)
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.vm_shared == s1.vm_shared
        &&& s2.iommu_owned
            == s1.iommu_owned.insert(vm, s1.iommu_owned[vm].remove(page))
        &&& s2.iommu_shared == s1.iommu_shared
        &&& s2.s2_map == s1.s2_map
        &&& s2.hw_s2map == s1.hw_s2map
        &&& s2.tlb == s1.tlb
        &&& s2.iommu_s2_map == post_map
        &&& s2.iommu_hw_s2map == s1.iommu_hw_s2map.remove(key)
        &&& s2.iommu_tlb == s1.iommu_tlb.remove_keys(s1.iommu_invalidation_targets(vm, gpa))
    }

    /// Atomically install an IOMMU mapping to global-shared memory and record
    /// its target in the dynamic `iommu_shared` projection.
    pub open spec fn hv_iommu_map_global_shared_step(
        s1: Self,
        s2: Self,
        vm: VmId,
        gpa: GuestPage,
        entry: S2Entry,
    ) -> bool {
        let key = VmPageKey::new(vm, gpa);
        &&& s1.wf()
        &&& s1.all_vms().contains(vm)
        &&& (forall|v: VmId| #[trigger]
            s1.all_vms().contains(v) ==> !s1.vm_owned[v].contains(entry.page)
                && !s1.iommu_owned[v].contains(entry.page))
        &&& !s1.iommu_s2_map.contains_key(key)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.same_memory_as(&s1)
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.vm_shared == s1.vm_shared
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == s1.iommu_shared.insert(entry.page)
        &&& s2.s2_map == s1.s2_map
        &&& s2.hw_s2map == s1.hw_s2map
        &&& s2.tlb == s1.tlb
        &&& s2.iommu_s2_map == s1.iommu_s2_map.insert(key, entry)
        &&& s2.iommu_hw_s2map == s1.iommu_hw_s2map.insert(key, entry)
        &&& s2.iommu_tlb == s1.iommu_tlb.remove_keys(s1.iommu_invalidation_targets(vm, gpa))
    }

    /// Atomically remove an IOMMU global-shared mapping and drop its physical
    /// page only when no surviving IOMMU mapping aliases it.
    pub open spec fn hv_iommu_unmap_global_shared_step(
        s1: Self,
        s2: Self,
        vm: VmId,
        gpa: GuestPage,
    ) -> bool {
        let key = VmPageKey::new(vm, gpa);
        let page = s1.iommu_s2_map[key].page;
        let post_map = s1.iommu_s2_map.remove(key);
        let aliased = exists|k: VmPageKey| #[trigger]
            post_map.contains_key(k) && post_map[k].page == page;
        &&& s1.wf()
        &&& s1.iommu_s2_map.contains_key(key)
        &&& s1.iommu_shared.contains(page)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.same_memory_as(&s1)
        &&& s2.vm_owned == s1.vm_owned
        &&& s2.vm_shared == s1.vm_shared
        &&& s2.iommu_owned == s1.iommu_owned
        &&& s2.iommu_shared == if aliased {
            s1.iommu_shared
        } else {
            s1.iommu_shared.remove(page)
        }
        &&& s2.s2_map == s1.s2_map
        &&& s2.hw_s2map == s1.hw_s2map
        &&& s2.tlb == s1.tlb
        &&& s2.iommu_s2_map == post_map
        &&& s2.iommu_hw_s2map == s1.iommu_hw_s2map.remove(key)
        &&& s2.iommu_tlb == s1.iommu_tlb.remove_keys(s1.iommu_invalidation_targets(vm, gpa))
    }

    /// Register a fresh, empty VM (dynamic VM set).
    pub open spec fn hv_add_vm_step(s1: Self, s2: Self, vm: VmId) -> bool {
        &&& s1.wf()
        &&& !s1.all_vms().contains(vm)
        &&& s2.wf()
        &&& s2.all_vms == s1.all_vms.insert(vm)
        &&& s2.vm_owned == s1.vm_owned.insert(vm, Set::empty())
        &&& s2.iommu_owned == s1.iommu_owned.insert(vm, Set::empty())
        &&& s2.iommu_shared == s1.iommu_shared
        &&& s2.vm_shared == s1.vm_shared
        &&& s2.same_translation_as(&s1)
        &&& s2.same_memory_as(&s1)
    }

    /// Deregister a VM that owns and maps nothing.
    pub open spec fn hv_remove_vm_step(s1: Self, s2: Self, vm: VmId) -> bool {
        &&& s1.wf()
        &&& s1.all_vms().contains(vm)
        &&& s1.vm_owned[vm] == Set::<PhysPage>::empty()
        &&& s1.iommu_owned[vm] == Set::<PhysPage>::empty()
        &&& (forall|k: VmPageKey| #[trigger] s1.s2_map.contains_key(k) ==> k.vm != vm)
        &&& (forall|k: VmPageKey| #[trigger] s1.iommu_s2_map.contains_key(k) ==> k.vm != vm)
        &&& (forall|k: TlbKey| #[trigger] s1.tlb.contains_key(k) ==> k.vm != vm)
        &&& (forall|k: TlbKey| #[trigger] s1.iommu_tlb.contains_key(k) ==> k.vm != vm)
        &&& s2.wf()
        &&& s2.all_vms == s1.all_vms.remove(vm)
        &&& s2.vm_owned == s1.vm_owned.remove(vm)
        &&& s2.iommu_owned == s1.iommu_owned.remove(vm)
        &&& s2.iommu_shared == s1.iommu_shared
        &&& s2.vm_shared == s1.vm_shared
        &&& s2.same_translation_as(&s1)
        &&& s2.same_memory_as(&s1)
    }

    pub open spec fn hypervisor_step(s1: Self, s2: Self, op: HypervisorOp) -> bool {
        match op {
            HypervisorOp::MapVmPrivate(vm, gpa, entry) => {
                Self::hv_map_vm_private_step(s1, s2, vm, gpa, entry)
            },
            HypervisorOp::UnmapVmPrivate(vm, gpa, page) => {
                Self::hv_unmap_vm_private_step(s1, s2, vm, gpa, page)
            },
            HypervisorOp::MapGlobalShared(vm, gpa, entry) => {
                Self::hv_map_global_shared_step(s1, s2, vm, gpa, entry)
            },
            HypervisorOp::UnmapGlobalShared(vm, gpa) => {
                Self::hv_unmap_global_shared_step(s1, s2, vm, gpa)
            },
            HypervisorOp::AddVm(vm) => Self::hv_add_vm_step(s1, s2, vm),
            HypervisorOp::RemoveVm(vm) => Self::hv_remove_vm_step(s1, s2, vm),
            HypervisorOp::IommuMapVmPrivate(vm, gpa, entry) => {
                Self::hv_iommu_map_vm_private_step(s1, s2, vm, gpa, entry)
            },
            HypervisorOp::IommuUnmapVmPrivate(vm, gpa, page) => {
                Self::hv_iommu_unmap_vm_private_step(s1, s2, vm, gpa, page)
            },
            HypervisorOp::IommuMapGlobalShared(vm, gpa, entry) => {
                Self::hv_iommu_map_global_shared_step(s1, s2, vm, gpa, entry)
            },
            HypervisorOp::IommuUnmapGlobalShared(vm, gpa) => {
                Self::hv_iommu_unmap_global_shared_step(s1, s2, vm, gpa)
            },
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
    /// population, ownership maps, shared sets, stage-2 maps, and TLBs
    /// are all empty; every `wf` clause is then a `forall` over an empty domain and
    /// holds vacuously (see `lemma_init_wf` in `security.rs`). `memory` (initial DRAM)
    /// is left unconstrained as platform data irrelevant to `wf`. Guests and mappings are subsequently
    /// created by `hv_add_vm` and the combined VM-private/shared mapping steps.
    pub open spec fn init(s: Self) -> bool {
        &&& s.all_vms == Set::<VmId>::empty()
        &&& s.vm_owned == Map::<VmId, Set<PhysPage>>::empty()
        &&& s.vm_shared == Set::<PhysPage>::empty()
        &&& s.s2_map == Map::<VmPageKey, S2Entry>::empty()
        &&& s.hw_s2map == Map::<VmPageKey, S2Entry>::empty()
        &&& s.tlb == Map::<TlbKey, TlbEntry>::empty()
        &&& s.iommu_s2_map == Map::<VmPageKey, S2Entry>::empty()
        &&& s.iommu_owned == Map::<VmId, Set<PhysPage>>::empty()
        &&& s.iommu_shared == Set::<PhysPage>::empty()
        &&& s.iommu_hw_s2map == Map::<VmPageKey, S2Entry>::empty()
        &&& s.iommu_tlb == Map::<TlbKey, TlbEntry>::empty()
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
        &&& forall|i: int|
            0 <= i < acts.len() ==> #[trigger] MachineState::step(trace[i], trace[i + 1], acts[i])
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
