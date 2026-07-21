use vstd::prelude::*;

use crate::model::hardware::HardwareView;
use crate::model::software::SoftwareView;
use crate::model::types::{
    CpuId, DataWord, GuestPage, GuestWordAddr, PhysPage, PhysWordAddr, S2Entry, SharedPage,
    TlbEntry, TlbKey, VmId, VmPageKey,
};

verus! {

/// Pure ghost machine state for the high-level isolation proof.
///
/// `MachineState` is the combined view produced by [`MachineState::assemble`] — the
/// canonical state on which machine-level steps and security lemmas are expressed.
/// The VM population is a single dynamic set (`all_vms`); the subject-vs-environment
/// split used only to *state* isolation lives in
/// [`crate::model::machine::security`], not here.
pub ghost struct MachineState {
    pub all_vms: Set<VmId>,
    pub hypervisor_owned: Set<PhysPage>,
    pub vm_owned: Map<VmId, Set<PhysPage>>,
    pub shared_pages: Set<SharedPage>,
    /// The **software-maintained** stage-2 map (page-table bytes; from `SoftwareView`).
    pub s2_map: Map<VmPageKey, S2Entry>,
    /// The **software-maintained IOMMU** stage-2 map (SMMU page-table bytes; from
    /// `SoftwareView`).
    pub iommu_s2_map: Map<VmPageKey, S2Entry>,
    /// Per-VM private DMA ownership, copied from `SoftwareView`.
    pub iommu_owned: Map<VmId, Set<PhysPage>>,
    /// VM-independent IOMMU-shared pages, copied from `SoftwareView`.
    pub iommu_shared: Set<PhysPage>,
    /// The **hardware-reachable** stage-2 map (walker view; from `HardwareView`).  Equal to
    /// `s2_map` at well-formed states (the [`sync`](MachineState::sync) invariant);
    /// the TLB caches *this* map, and translation resolves through it.
    pub hw_s2map: Map<VmPageKey, S2Entry>,
    /// The **IOMMU hardware-reachable** stage-2 map (SMMU walker view; from
    /// `HardwareView`).  Equal to `iommu_s2_map` at well-formed states.
    pub iommu_hw_s2map: Map<VmPageKey, S2Entry>,
    pub tlb: Map<TlbKey, TlbEntry>,
    pub iommu_tlb: Map<TlbKey, TlbEntry>,
    pub active_vm: Map<CpuId, VmId>,
    pub memory: Map<PhysWordAddr, DataWord>,
}

impl MachineState {
    /// Combine a software view and a hardware view into a high-level machine state.
    pub open spec fn assemble(sw: SoftwareView, hw: HardwareView) -> MachineState {
        MachineState {
            all_vms: sw.all_vms,
            hypervisor_owned: sw.hypervisor_owned,
            vm_owned: sw.vm_owned,
            shared_pages: sw.shared_pages,
            s2_map: sw.s2_map,
            iommu_s2_map: sw.iommu_s2_map,
            iommu_owned: sw.iommu_owned,
            iommu_shared: sw.iommu_shared,
            hw_s2map: hw.s2map,
            iommu_hw_s2map: hw.iommu_s2map,
            tlb: hw.tlb,
            iommu_tlb: hw.iommu_tlb,
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

    /// IOMMU TLB keys invalidated by an SMMU page edit.
    pub open spec fn iommu_invalidation_targets(&self, vm: VmId, gpa: GuestPage) -> Set<TlbKey> {
        Set::new(|key: TlbKey| key.vm == vm && key.gpa == gpa && self.iommu_tlb.contains_key(key))
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

    /// IOMMU flush-before-free gate: `page` is referenced by no IOMMU stage-2 entry and
    /// no SMMU TLB entry.  Required by `hv_iommu_reclaim_page_step` so a page cannot lose
    /// its DMA ownership while an SMMU translation to it still resolves (which would
    /// strand a mapping targeting neither `iommu_owned` nor `iommu_shared`).
    pub open spec fn iommu_page_is_quiescent(&self, page: PhysPage) -> bool {
        &&& forall|key: VmPageKey| #[trigger]
            self.iommu_s2_map.contains_key(key) ==> self.iommu_s2_map[key].page != page
        &&& forall|key: TlbKey| #[trigger]
            self.iommu_tlb.contains_key(key) ==> self.iommu_tlb[key].page != page
    }

    pub open spec fn same_identity_as(&self, other: &Self) -> bool {
        self.all_vms == other.all_vms
    }

    pub open spec fn same_ownership_as(&self, other: &Self) -> bool {
        &&& self.hypervisor_owned == other.hypervisor_owned
        &&& self.vm_owned == other.vm_owned
        &&& self.shared_pages == other.shared_pages
        &&& self.iommu_owned == other.iommu_owned
        &&& self.iommu_shared == other.iommu_shared
    }

    pub open spec fn same_translation_as(&self, other: &Self) -> bool {
        &&& self.s2_map == other.s2_map
        &&& self.hw_s2map == other.hw_s2map
        &&& self.tlb == other.tlb
        &&& self.iommu_s2_map == other.iommu_s2_map
        &&& self.iommu_hw_s2map == other.iommu_hw_s2map
        &&& self.iommu_tlb == other.iommu_tlb
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
        } else if self.hw_s2map.contains_key(s2_key) {
            Option::Some(self.hw_s2map[s2_key])
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

    /// Effective IOMMU translation.  The `stream` parameter reuses `CpuId` as the
    /// regime-neutral TLB-index component from `MmuSpec`; it represents the SMMU
    /// context that owns the cached translation.
    pub open spec fn iommu_effective_entry(
        &self,
        stream: CpuId,
        vm: VmId,
        gpa: GuestPage,
    ) -> Option<S2Entry> {
        let key = TlbKey::new(stream, vm, gpa);
        let s2_key = VmPageKey::new(vm, gpa);
        if self.iommu_tlb.contains_key(key) {
            Option::Some(self.iommu_tlb[key].as_s2_entry())
        } else if self.iommu_hw_s2map.contains_key(s2_key) {
            Option::Some(self.iommu_hw_s2map[s2_key])
        } else {
            Option::None
        }
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

    /// Every cached TLB entry agrees with the **hardware-reachable** map (the TLB
    /// caches that map; synchronous coherence — mapping edits flush stale entries).
    pub open spec fn tlb_safe(&self) -> bool {
        forall|key: TlbKey| #[trigger]
            self.tlb.contains_key(key) ==> {
                let s2_key = VmPageKey::new(key.vm, key.gpa);
                &&& self.hw_s2map.contains_key(s2_key)
                &&& self.tlb[key].as_s2_entry() == self.hw_s2map[s2_key]
            }
    }

    /// SMMU TLB entries agree with the IOMMU hardware-reachable map.
    pub open spec fn iommu_tlb_safe(&self) -> bool {
        forall|key: TlbKey| #[trigger]
            self.iommu_tlb.contains_key(key) ==> {
                let s2_key = VmPageKey::new(key.vm, key.gpa);
                &&& self.iommu_hw_s2map.contains_key(s2_key)
                &&& self.iommu_tlb[key].as_s2_entry() == self.iommu_hw_s2map[s2_key]
            }
    }

    /// **Sync — the cross-layer well-formedness clause.** The hardware-reachable map
    /// equals the software-maintained map.  Holds at every well-formed state; the
    /// break-before-make window where they diverge lives below this abstraction (at
    /// the `MmuSpec`/`BudgetSpec` token level), not here.
    pub open spec fn sync(&self) -> bool {
        self.hw_s2map == self.s2_map
    }

    /// IOMMU sync: the SMMU walker-reachable map equals the software-maintained
    /// IOMMU page-table view.
    pub open spec fn iommu_sync(&self) -> bool {
        self.iommu_hw_s2map == self.iommu_s2_map
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

    pub open spec fn iommu_ownership_wf(&self) -> bool {
        &&& self.iommu_owned.dom() == self.all_vms()
        &&& forall|vm1: VmId, vm2: VmId| #[trigger]
            self.all_vms().contains(vm1) && #[trigger] self.all_vms().contains(vm2) && vm1 != vm2
                ==> forall|page: PhysPage| #[trigger]
                self.iommu_owned[vm1].contains(page) ==> !self.iommu_owned[vm2].contains(page)
        &&& forall|vm1: VmId, vm2: VmId| #[trigger]
            self.all_vms().contains(vm1) && #[trigger] self.all_vms().contains(vm2) && vm1 != vm2
                ==> forall|page: PhysPage| #[trigger]
                self.iommu_owned[vm1].contains(page) ==> !self.vm_owned[vm2].contains(page)
        &&& forall|vm: VmId| #[trigger]
            self.all_vms().contains(vm) ==> forall|page: PhysPage| #[trigger]
                self.iommu_owned[vm].contains(page) ==> !self.iommu_shared.contains(
                    page,
                )
                // (4) The shared region is disjoint from every VM's CPU ownership: a device DMA to
                // a shared page can never land on another VM's CPU-private page.
        &&& forall|vm: VmId| #[trigger]
            self.all_vms().contains(vm) ==> forall|page: PhysPage| #[trigger]
                self.vm_owned[vm].contains(page) ==> !self.iommu_shared.contains(page)
    }

    pub open spec fn iommu_translation_wf(&self) -> bool {
        forall|key: VmPageKey| #[trigger]
            self.iommu_s2_map.contains_key(key) ==> {
                &&& self.all_vms().contains(key.vm)
                &&& self.iommu_owned.contains_key(key.vm)
                &&& (self.iommu_owned[key.vm].contains(self.iommu_s2_map[key].page)
                    || self.iommu_shared.contains(self.iommu_s2_map[key].page))
            }
    }

    pub open spec fn iommu_wf(&self) -> bool {
        &&& self.iommu_ownership_wf()
        &&& self.iommu_translation_wf()
    }

    pub open spec fn active_vm_wf(&self) -> bool {
        forall|cpu: CpuId| #[trigger]
            self.active_vm.contains_key(cpu) ==> self.all_vms().contains(self.active_vm[cpu])
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.ownership_wf()
        &&& self.sharing_wf()
        &&& self.translation_wf()
        &&& self.iommu_wf()
        &&& self.active_vm_wf()
        &&& self.tlb_safe()
        &&& self.iommu_tlb_safe()
        &&& self.sync()
        &&& self.iommu_sync()
    }
}

} // verus!
