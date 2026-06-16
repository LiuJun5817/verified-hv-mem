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
        &&& s2.s2_map == s1.s2_map.insert(key, entry)
        // synchronous TLB invalidation of the edited mapping
        &&& s2.tlb == s1.tlb.remove_keys(s1.invalidation_targets(vm, gpa))
    }

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
        &&& s1.shared_pages.contains(rev)
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
    // Top-level step dispatch
    // ------------------------------------------------------------------
    pub open spec fn step(s1: Self, s2: Self, action: MachineAction) -> bool {
        match action {
            MachineAction::Vm(vm, op) => Self::vm_step(s1, s2, vm, op),
            MachineAction::Hypervisor(op) => Self::hypervisor_step(s1, s2, op),
        }
    }
}

} // verus!
