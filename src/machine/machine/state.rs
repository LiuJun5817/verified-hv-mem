use vstd::prelude::*;

use crate::machine::hardware::HwView;
use crate::machine::software::SwView;
use crate::machine::types::*;

verus! {

/// Pure ghost machine state for the high-level isolation proof.
///
/// `MachineState` is the combined view produced by [`MachineState::assemble`].  It is the
/// canonical state on which machine-level step functions and security lemmas
/// are expressed.  SW-only and HW-only concerns are separated into
/// [`crate::machine::software`] and [`crate::machine::hardware`] respectively.
pub ghost struct MachineState {
    pub subject: VmId,
    pub environment_vms: Set<VmId>,
    pub hypervisor_owned: Set<PhysPage>,
    pub vm_owned: Map<VmId, Set<PhysPage>>,
    pub shared_pages: Set<SharedPage>,
    pub s2_map: Map<VmPageKey, S2Entry>,
    pub tlb: Map<TlbKey, TlbEntry>,
    pub pending_invalidations: Set<TlbKey>,
    pub active_vm: Map<CpuId, VmId>,
    pub memory: Map<PhysWordAddr, DataWord>,
}

impl MachineState {
    // -----------------------------------------------------------------------
    // Assembly function
    //
    // `assemble` is the bridge between the two sub-states and the abstract
    // machine model.  The `subject` is chosen existentially; the refinement
    // proof in `machine::machine::refine` shows that every valid
    // (SwView, HwView) pair produces a well-formed MachineState.
    // -----------------------------------------------------------------------
    /// Combine a software view and a hardware view into a high-level machine
    /// state.
    ///
    /// The `subject` VM is chosen existentially from `sw.all_vms`; the
    /// `environment_vms` are the remainder.  Because `choose` is
    /// non-deterministic in Verus spec, refinement proofs must quantify over
    /// all possible subjects (or constrain `sw.all_vms` to a singleton).
    pub open spec fn assemble(sw: SwView, hw: HwView) -> MachineState {
        let subject = choose|vmid: VmId| sw.all_vms.contains(vmid);
        let environment_vms = sw.all_vms.remove(subject);
        MachineState {
            subject,
            environment_vms,
            hypervisor_owned: sw.hypervisor_owned,
            vm_owned: sw.vm_owned,
            shared_pages: sw.shared_pages,
            s2_map: sw.s2_map,
            tlb: hw.tlb,
            pending_invalidations: hw.pending_invalidations,
            memory: hw.memory,
            active_vm: hw.active_vm,
        }
    }

    pub open spec fn all_vms(&self) -> Set<VmId> {
        self.environment_vms.insert(self.subject)
    }

    /// A subject-private page is owned by the subject VM and not exposed through
    /// the explicit sharing relation.
    pub open spec fn subject_private_page(&self, page: PhysPage) -> bool {
        self.vm_owned[self.subject].contains(page) && !self.shared_with(self.subject, page)
    }

    pub open spec fn cpu_runs(&self, cpu: CpuId, vm: VmId) -> bool {
        self.active_vm.contains_key(cpu) && self.active_vm[cpu] == vm
    }

    pub open spec fn shared_with(&self, vm: VmId, page: PhysPage) -> bool {
        exists|edge: SharedPage| #[trigger]
            self.shared_pages.contains(edge) && edge.page == page && (edge.left == vm || edge.right
                == vm)
    }

    pub open spec fn owned_or_shared(&self, vm: VmId, page: PhysPage) -> bool {
        (self.vm_owned.contains_key(vm) && self.vm_owned[vm].contains(page)) || self.shared_with(
            vm,
            page,
        )
    }

    /// Returns all TLB keys whose cached translation would be stale after a
    /// change to `(vm, gpa)` in the S2 map.
    pub open spec fn invalidation_targets(&self, vm: VmId, gpa: GuestPage) -> Set<TlbKey> {
        Set::new(|key: TlbKey| key.vm == vm && key.gpa == gpa && self.tlb.contains_key(key))
    }

    pub open spec fn page_is_quiescent(&self, page: PhysPage) -> bool {
        &&& forall|key: VmPageKey| #[trigger]
            self.s2_map.contains_key(key) ==> self.s2_map[key].page != page
        &&& forall|key: TlbKey| #[trigger] self.tlb.contains_key(key) ==> self.tlb[key].page != page
        &&& forall|edge: SharedPage| #[trigger]
            self.shared_pages.contains(edge) ==> edge.page != page
    }

    pub open spec fn same_identity_as(&self, other: &Self) -> bool {
        &&& self.subject == other.subject
        &&& self.environment_vms == other.environment_vms
    }

    pub open spec fn same_ownership_as(&self, other: &Self) -> bool {
        &&& self.hypervisor_owned == other.hypervisor_owned
        &&& self.vm_owned == other.vm_owned
        &&& self.shared_pages == other.shared_pages
    }

    pub open spec fn same_translation_as(&self, other: &Self) -> bool {
        &&& self.s2_map == other.s2_map
        &&& self.tlb == other.tlb
        &&& self.pending_invalidations == other.pending_invalidations
        &&& self.active_vm == other.active_vm
    }

    pub open spec fn same_memory_as(&self, other: &Self) -> bool {
        self.memory == other.memory
    }

    pub open spec fn effective_entry(&self, cpu: CpuId, vm: VmId, gpa: GuestPage) -> Option<
        S2Entry,
    > {
        let key = TlbKey::new(cpu, vm, gpa);
        let s2_key = VmPageKey::new(vm, gpa);
        if self.tlb.contains_key(key) && !self.pending_invalidations.contains(key) {
            Option::Some(self.tlb[key].as_s2_entry())
        } else if self.s2_map.contains_key(s2_key) {
            Option::Some(self.s2_map[s2_key])
        } else {
            Option::None
        }
    }

    pub open spec fn translated_word(&self, cpu: CpuId, vm: VmId, gva: GuestWordAddr) -> Option<
        PhysWordAddr,
    > {
        let entry = self.effective_entry(cpu, vm, gva.page());
        if entry is Some {
            Option::Some(entry->Some_0.page.word(gva.offset()))
        } else {
            Option::None
        }
    }

    pub open spec fn can_read(&self, cpu: CpuId, vm: VmId, gva: GuestWordAddr) -> bool {
        let entry = self.effective_entry(cpu, vm, gva.page());
        entry is Some && entry->Some_0.access.read
    }

    pub open spec fn can_write(&self, cpu: CpuId, vm: VmId, gva: GuestWordAddr) -> bool {
        let entry = self.effective_entry(cpu, vm, gva.page());
        entry is Some && entry->Some_0.access.write
    }

    pub open spec fn read_observation(&self, cpu: CpuId, vm: VmId, gva: GuestWordAddr) -> Option<
        DataWord,
    > {
        let paddr = self.translated_word(cpu, vm, gva);
        if paddr is Some && self.can_read(cpu, vm, gva) && self.memory.contains_key(paddr->Some_0) {
            Option::Some(self.memory[paddr->Some_0])
        } else {
            Option::None
        }
    }

    pub open spec fn tlb_safe(&self) -> bool {
        forall|key: TlbKey| #[trigger]
            self.tlb.contains_key(key) ==> self.pending_invalidations.contains(key) || {
                let s2_key = VmPageKey::new(key.vm, key.gpa);
                &&& self.s2_map.contains_key(s2_key)
                &&& self.tlb[key].as_s2_entry() == self.s2_map[s2_key]
            }
    }

    pub open spec fn ownership_wf(&self) -> bool {
        &&& self.vm_owned.dom() == self.all_vms()
        &&& forall|vm1: VmId, vm2: VmId| #[trigger]
            self.all_vms().contains(vm1) && #[trigger] self.all_vms().contains(vm2) && vm1 != vm2
                ==> forall|page: PhysPage| #[trigger]
                self.vm_owned[vm1].contains(page) ==> !self.vm_owned[vm2].contains(page)
        &&& forall|vm: VmId| #[trigger]
            self.all_vms().contains(vm) ==> forall|page: PhysPage| #[trigger]
                self.vm_owned[vm].contains(page) ==> !self.hypervisor_owned.contains(page)
    }

    pub open spec fn sharing_wf(&self) -> bool {
        forall|edge: SharedPage| #[trigger]
            self.shared_pages.contains(edge) ==> {
                &&& edge.left != edge.right
                &&& self.all_vms().contains(edge.left)
                &&& self.all_vms().contains(edge.right)
                &&& self.shared_pages.contains(edge.reverse())
            }
    }

    pub open spec fn translation_wf(&self) -> bool {
        forall|key: VmPageKey| #[trigger]
            self.s2_map.contains_key(key) ==> {
                &&& self.all_vms().contains(key.vm)
                &&& self.owned_or_shared(key.vm, self.s2_map[key].page)
            }
    }

    pub open spec fn execution_wf(&self) -> bool {
        &&& forall|cpu: CpuId| #[trigger]
            self.active_vm.contains_key(cpu) ==> self.all_vms().contains(self.active_vm[cpu])
        &&& forall|key: TlbKey| #[trigger]
            self.pending_invalidations.contains(key) ==> self.active_vm.contains_key(key.cpu)
                && self.all_vms().contains(key.vm)
    }

    pub open spec fn wf(&self) -> bool {
        &&& !self.environment_vms.contains(self.subject)
        &&& self.ownership_wf()
        &&& self.sharing_wf()
        &&& self.translation_wf()
        &&& self.execution_wf()
        &&& self.tlb_safe()
    }

    pub open spec fn subject_private_pa(&self, pa: PhysWordAddr) -> bool {
        self.subject_private_page(pa.page())
    }
}

} // verus!
