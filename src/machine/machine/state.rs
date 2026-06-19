use vstd::prelude::*;

use crate::machine::hardware::HwView;
use crate::machine::software::SwView;
use crate::machine::types::*;

verus! {

/// Pure ghost machine state for the high-level isolation proof.
///
/// `MachineState` is the combined view produced by [`MachineState::assemble`] — the
/// canonical state on which machine-level steps and security lemmas are expressed.
/// The VM population is a single dynamic set (`all_vms`); the subject-vs-environment
/// split used only to *state* isolation lives in
/// [`crate::machine::machine::security`], not here.
pub ghost struct MachineState {
    pub all_vms: Set<VmId>,
    pub hypervisor_owned: Set<PhysPage>,
    pub vm_owned: Map<VmId, Set<PhysPage>>,
    pub shared_pages: Set<SharedPage>,
    pub s2_map: Map<VmPageKey, S2Entry>,
    pub tlb: Map<TlbKey, TlbEntry>,
    pub active_vm: Map<CpuId, VmId>,
    pub memory: Map<PhysWordAddr, DataWord>,
}

impl MachineState {
    /// Combine a software view and a hardware view into a high-level machine state.
    pub open spec fn assemble(sw: SwView, hw: HwView) -> MachineState {
        MachineState {
            all_vms: sw.all_vms,
            hypervisor_owned: sw.hypervisor_owned,
            vm_owned: sw.vm_owned,
            shared_pages: sw.shared_pages,
            s2_map: sw.s2_map,
            tlb: hw.tlb,
            active_vm: hw.active_vm,
            memory: hw.memory,
        }
    }

    pub open spec fn all_vms(&self) -> Set<VmId> {
        self.all_vms
    }

    /// `page` is private to `vm`: owned by it and exposed through *no* sharing edge.
    ///
    /// Note this is "globally unshared", not merely "not shared *with* `vm`".  The
    /// weaker `!shared_with(vm, page)` would admit a page that `vm` owns yet that is
    /// shared between two *other* VMs — a configuration `wf` alone does not rule out
    /// (sharing edges are not tied to ownership in `wf`).  Requiring the page to lie
    /// in no edge at all is the sound notion of private for the isolation theorems,
    /// and on reachable states it coincides with `!shared_with(vm, page)` (a share is
    /// only ever created by the page's owner, and ownership is disjoint).
    pub open spec fn private_page(&self, vm: VmId, page: PhysPage) -> bool {
        &&& self.vm_owned[vm].contains(page)
        &&& forall|edge: SharedPage| #[trigger]
            self.shared_pages.contains(edge) ==> edge.page != page
    }

    pub open spec fn private_pa(&self, vm: VmId, pa: PhysWordAddr) -> bool {
        self.private_page(vm, pa.page())
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

    /// TLB keys whose cached translation would be stale after a change to
    /// `(vm, gpa)` in the stage-2 map — flushed synchronously by a mapping edit.
    pub open spec fn invalidation_targets(&self, vm: VmId, gpa: GuestPage) -> Set<TlbKey> {
        Set::new(|key: TlbKey| key.vm == vm && key.gpa == gpa && self.tlb.contains_key(key))
    }

    /// `page` is referenced by no `s2_map` entry, no TLB entry, and no sharing edge.
    ///
    /// This is the model's *flush-before-free* gate: `hv_reclaim_page_step` requires
    /// it, so a page cannot be returned to the pool while any CPU's TLB still caches
    /// it.  Together with the synchronous flush in `hv_unmap_step`, it discharges the
    /// real asynchronous TLB-shootdown window without modelling stale state (see the
    /// note on `hv_unmap_step`).
    pub open spec fn page_is_quiescent(&self, page: PhysPage) -> bool {
        &&& forall|key: VmPageKey| #[trigger]
            self.s2_map.contains_key(key) ==> self.s2_map[key].page != page
        &&& forall|key: TlbKey| #[trigger] self.tlb.contains_key(key) ==> self.tlb[key].page != page
        &&& forall|edge: SharedPage| #[trigger]
            self.shared_pages.contains(edge) ==> edge.page != page
    }

    pub open spec fn same_identity_as(&self, other: &Self) -> bool {
        self.all_vms == other.all_vms
    }

    pub open spec fn same_ownership_as(&self, other: &Self) -> bool {
        &&& self.hypervisor_owned == other.hypervisor_owned
        &&& self.vm_owned == other.vm_owned
        &&& self.shared_pages == other.shared_pages
    }

    pub open spec fn same_translation_as(&self, other: &Self) -> bool {
        &&& self.s2_map == other.s2_map
        &&& self.tlb == other.tlb
        &&& self.active_vm == other.active_vm
    }

    pub open spec fn same_memory_as(&self, other: &Self) -> bool {
        self.memory == other.memory
    }

    /// Effective translation: a coherent cached TLB entry, else the stage-2 map.
    /// (Under synchronous invalidation `tlb_safe` holds, so a cached entry always
    /// agrees with the stage-2 map.)
    pub open spec fn effective_entry(&self, cpu: CpuId, vm: VmId, gpa: GuestPage) -> Option<
        S2Entry,
    > {
        let key = TlbKey::new(cpu, vm, gpa);
        let s2_key = VmPageKey::new(vm, gpa);
        if self.tlb.contains_key(key) {
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

    /// Every cached TLB entry agrees with the stage-2 map (synchronous coherence —
    /// mapping edits flush stale entries, so there is no pending state).
    pub open spec fn tlb_safe(&self) -> bool {
        forall|key: TlbKey| #[trigger]
            self.tlb.contains_key(key) ==> {
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
        forall|cpu: CpuId| #[trigger]
            self.active_vm.contains_key(cpu) ==> self.all_vms().contains(self.active_vm[cpu])
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.ownership_wf()
        &&& self.sharing_wf()
        &&& self.translation_wf()
        &&& self.execution_wf()
        &&& self.tlb_safe()
    }
}

} // verus!
