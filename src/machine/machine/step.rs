use vstd::prelude::*;

use super::state::MachineState;
use crate::machine::types::*;

verus! {

// ---------------------------------------------------------------------------
// High-level machine step functions
//
// These predicates are defined on the combined `MachineState` (produced by
// `assemble(sw, hw)`).  They capture the full observable effect of each
// operation — SW-state changes plus any HW-state side-effects.
//
// The refinement proofs in `refine.rs` show that executing a SW step (from
// `software::step`) together with the matching HW step (from `hardware::step`)
// implies the corresponding predicate here.
// ---------------------------------------------------------------------------
impl MachineState {
    // ------------------------------------------------------------------
    // VM memory operations
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

    pub open spec fn subject_vm_step(s1: Self, s2: Self, op: VmMemOp) -> bool {
        let subject = s1.subject;
        match op {
            VmMemOp::Read(cpu, gva) => Self::vm_read_step(s1, s2, subject, cpu, gva),
            VmMemOp::Write(cpu, gva, value) => Self::vm_write_step(
                s1,
                s2,
                subject,
                cpu,
                gva,
                value,
            ),
            VmMemOp::HyperCall(cpu, req) => Self::vm_hypercall_step(s1, s2, subject, cpu, req),
        }
    }

    pub open spec fn environment_vm_step(s1: Self, s2: Self, vm: VmId, op: VmMemOp) -> bool {
        &&& s1.environment_vms.contains(vm)
        &&& match op {
            VmMemOp::Read(cpu, gva) => Self::vm_read_step(s1, s2, vm, cpu, gva),
            VmMemOp::Write(cpu, gva, value) => Self::vm_write_step(s1, s2, vm, cpu, gva, value),
            VmMemOp::HyperCall(cpu, req) => Self::vm_hypercall_step(s1, s2, vm, cpu, req),
        }
    }

    /// Returns true iff `s2` is reachable from `s1` in a single
    /// environment-VM step.  Used as the reachability hypothesis in the
    /// integrity and confidentiality lemmas.
    pub open spec fn env_reachable(s1: Self, s2: Self) -> bool {
        exists|vm: VmId, op: VmMemOp| Self::environment_vm_step(s1, s2, vm, op)
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
        let pending = s1.pending_invalidations.union(s1.invalidation_targets(vm, gpa));
        &&& s1.wf()
        &&& s1.all_vms().contains(vm)
        &&& s1.owned_or_shared(vm, entry.page)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.same_ownership_as(&s1)
        &&& s2.memory == s1.memory
        &&& s2.active_vm == s1.active_vm
        &&& s2.tlb == s1.tlb
        &&& s2.s2_map == s1.s2_map.insert(key, entry)
        &&& s2.pending_invalidations == pending
    }

    pub open spec fn hv_unmap_step(s1: Self, s2: Self, vm: VmId, gpa: GuestPage) -> bool {
        let key = VmPageKey::new(vm, gpa);
        let pending = s1.pending_invalidations.union(s1.invalidation_targets(vm, gpa));
        &&& s1.wf()
        &&& s1.s2_map.contains_key(key)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.same_ownership_as(&s1)
        &&& s2.memory == s1.memory
        &&& s2.active_vm == s1.active_vm
        &&& s2.tlb == s1.tlb
        &&& s2.s2_map == s1.s2_map.remove(key)
        &&& s2.pending_invalidations == pending
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
        &&& s2.pending_invalidations == s1.pending_invalidations
        &&& s2.active_vm == s1.active_vm.insert(cpu, vm)
    }

    pub open spec fn hv_issue_invalidation_step(
        s1: Self,
        s2: Self,
        vm: VmId,
        gpa: GuestPage,
    ) -> bool {
        let pending = s1.pending_invalidations.union(s1.invalidation_targets(vm, gpa));
        &&& s1.wf()
        &&& s1.all_vms().contains(vm)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.same_ownership_as(&s1)
        &&& s2.same_memory_as(&s1)
        &&& s2.s2_map == s1.s2_map
        &&& s2.tlb == s1.tlb
        &&& s2.active_vm == s1.active_vm
        &&& s2.pending_invalidations == pending
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
            HypervisorOp::IssueTlbInvalidation(vm, gpa) => {
                Self::hv_issue_invalidation_step(s1, s2, vm, gpa)
            },
        }
    }

    // ------------------------------------------------------------------
    // Hardware MMU operations
    // ------------------------------------------------------------------
    pub open spec fn hw_tlb_fill_step(
        s1: Self,
        s2: Self,
        cpu: CpuId,
        vm: VmId,
        gpa: GuestPage,
    ) -> bool {
        let tkey = TlbKey::new(cpu, vm, gpa);
        let skey = VmPageKey::new(vm, gpa);
        &&& s1.wf()
        &&& s1.cpu_runs(cpu, vm)
        &&& s1.s2_map.contains_key(skey)
        &&& !s1.pending_invalidations.contains(tkey)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.same_ownership_as(&s1)
        &&& s2.same_memory_as(&s1)
        &&& s2.s2_map == s1.s2_map
        &&& s2.active_vm == s1.active_vm
        &&& s2.pending_invalidations == s1.pending_invalidations
        &&& s2.tlb == s1.tlb.insert(
            tkey,
            TlbEntry {
                page: s1.s2_map[skey].page,
                access: s1.s2_map[skey].access,
                generation: s1.s2_map[skey].generation,
            },
        )
    }

    pub open spec fn hw_tlb_invalidate_step(
        s1: Self,
        s2: Self,
        cpu: CpuId,
        vm: VmId,
        gpa: GuestPage,
    ) -> bool {
        let tkey = TlbKey::new(cpu, vm, gpa);
        &&& s1.wf()
        &&& s1.active_vm.contains_key(cpu)
        &&& s2.wf()
        &&& s2.same_identity_as(&s1)
        &&& s2.same_ownership_as(&s1)
        &&& s2.same_memory_as(&s1)
        &&& s2.s2_map == s1.s2_map
        &&& s2.active_vm == s1.active_vm
        &&& s2.tlb == s1.tlb.remove(tkey)
        &&& s2.pending_invalidations == s1.pending_invalidations.remove(tkey)
    }

    pub open spec fn hardware_mmu_step(s1: Self, s2: Self, op: HardwareMmuOp) -> bool {
        match op {
            HardwareMmuOp::TlbFill(cpu, vm, gpa) => Self::hw_tlb_fill_step(s1, s2, cpu, vm, gpa),
            HardwareMmuOp::TlbInvalidate(cpu, vm, gpa) => {
                Self::hw_tlb_invalidate_step(s1, s2, cpu, vm, gpa)
            },
            HardwareMmuOp::ShootdownAck(cpu, vm, gpa) => {
                Self::hw_tlb_invalidate_step(s1, s2, cpu, vm, gpa)
            },
        }
    }

    // ------------------------------------------------------------------
    // Top-level step dispatch
    // ------------------------------------------------------------------
    pub open spec fn step(s1: Self, s2: Self, action: MachineAction) -> bool {
        match action {
            MachineAction::SubjectVm(op) => Self::subject_vm_step(s1, s2, op),
            MachineAction::EnvironmentVm(vm, op) => Self::environment_vm_step(s1, s2, vm, op),
            MachineAction::Hypervisor(op) => Self::hypervisor_step(s1, s2, op),
            MachineAction::HardwareMmu(op) => Self::hardware_mmu_step(s1, s2, op),
        }
    }
}

} // verus!
