use vstd::prelude::*;

use crate::model::hardware::HardwareView;
use crate::model::software::SoftwareView;
use crate::model::types::{
    CpuId, DataWord, GuestPage, GuestWordAddr, PhysPage, PhysWordAddr, S2Entry, TlbEntry, TlbKey,
    VmId, VmPageKey,
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
    /// Per-VM pages protected by the CPU isolation theorem.
    pub s2_private_pages: Map<VmId, Set<PhysPage>>,
    /// Pages explicitly outside the S2-Private guarantee. Actual access still
    /// requires an installed translation.
    pub s2_shared_pages: Set<PhysPage>,
    /// The **software-maintained** stage-2 map (page-table bytes; from `SoftwareView`).
    pub s2_map: Map<VmPageKey, S2Entry>,
    /// The **software-maintained IOMMU** stage-2 map (SMMU page-table bytes; from
    /// `SoftwareView`).
    pub iommu_s2_map: Map<VmPageKey, S2Entry>,
    /// Per-VM pages protected by the DMA isolation theorem.
    pub iommu_private_pages: Map<VmId, Set<PhysPage>>,
    /// Pages explicitly outside the IOMMU-Private guarantee.
    pub iommu_shared_pages: Set<PhysPage>,
    /// The **hardware-reachable** stage-2 map (walker view; from `HardwareView`).  Equal to
    /// `s2_map` at well-formed states (the [`sync`](MachineState::sync) invariant);
    /// the TLB caches *this* map, and translation resolves through it.
    pub hw_s2map: Map<VmPageKey, S2Entry>,
    /// The **IOMMU hardware-reachable** stage-2 map (SMMU walker view; from
    /// `HardwareView`).  Equal to `iommu_s2_map` at well-formed states.
    pub iommu_hw_s2map: Map<VmPageKey, S2Entry>,
    pub tlb: Map<TlbKey, TlbEntry>,
    pub iommu_tlb: Map<TlbKey, TlbEntry>,
    pub memory: Map<PhysWordAddr, DataWord>,
}

impl MachineState {
    /// Combine a software view and a hardware view into a high-level machine state.
    pub open spec fn assemble(sw: SoftwareView, hw: HardwareView) -> MachineState {
        MachineState {
            all_vms: sw.all_vms,
            s2_private_pages: sw.s2_private_pages,
            s2_shared_pages: sw.s2_shared_pages,
            s2_map: sw.s2_map,
            iommu_s2_map: sw.iommu_s2_map,
            iommu_private_pages: sw.iommu_private_pages,
            iommu_shared_pages: sw.iommu_shared_pages,
            hw_s2map: hw.s2map,
            iommu_hw_s2map: hw.iommu_s2map,
            tlb: hw.tlb,
            iommu_tlb: hw.iommu_tlb,
            memory: hw.memory,
        }
    }

    pub open spec fn all_vms(&self) -> Set<VmId> {
        self.all_vms
    }

    /// Paper-level `S2Private(self, vm, page)`: `vm` is live and `page` belongs to
    /// its S2-Private projection, not to the dynamic S2-Shared projection.
    pub open spec fn s2_private(&self, vm: VmId, page: PhysPage) -> bool {
        &&& self.all_vms().contains(vm)
        &&& self.s2_private_pages[vm].contains(page)
        &&& !self.s2_shared_pages.contains(page)
    }

    /// Paper-level `S2Shared(self, page)`. This is the dynamic projection of
    /// installed Shared CPU mappings. It does not imply universal access; the
    /// installed S2 map records which VMs can translate to the page. A policy's
    /// static Shared eligibility set, if any, is a separate concept.
    pub open spec fn s2_shared(&self, page: PhysPage) -> bool {
        self.s2_shared_pages.contains(page)
    }

    /// Paper-level `IOMMUPrivate(self, vm, page)`: `vm` is live and `page` belongs
    /// to its IOMMU-Private projection, not to the dynamic IOMMU-Shared
    /// projection.
    pub open spec fn iommu_private(&self, vm: VmId, page: PhysPage) -> bool {
        &&& self.all_vms().contains(vm)
        &&& self.iommu_private_pages[vm].contains(page)
        &&& !self.iommu_shared_pages.contains(page)
    }

    /// Paper-level `IOMMUShared(self, page)`, using the dynamic projection of
    /// installed Shared IOMMU mappings.
    pub open spec fn iommu_shared(&self, page: PhysPage) -> bool {
        self.iommu_shared_pages.contains(page)
    }

    /// `page` has an S2 classification compatible with a mapping by `vm`.
    /// Classification alone does not create access.
    pub open spec fn s2_private_or_shared(&self, vm: VmId, page: PhysPage) -> bool {
        (self.s2_private_pages.contains_key(vm) && self.s2_private_pages[vm].contains(page))
            || self.s2_shared_pages.contains(page)
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

    pub open spec fn same_identity_as(&self, other: &Self) -> bool {
        self.all_vms == other.all_vms
    }

    pub open spec fn same_classification_as(&self, other: &Self) -> bool {
        &&& self.s2_private_pages == other.s2_private_pages
        &&& self.s2_shared_pages == other.s2_shared_pages
        &&& self.iommu_private_pages == other.iommu_private_pages
        &&& self.iommu_shared_pages == other.iommu_shared_pages
    }

    pub open spec fn same_translation_as(&self, other: &Self) -> bool {
        &&& self.s2_map == other.s2_map
        &&& self.hw_s2map == other.hw_s2map
        &&& self.tlb == other.tlb
        &&& self.iommu_s2_map == other.iommu_s2_map
        &&& self.iommu_hw_s2map == other.iommu_hw_s2map
        &&& self.iommu_tlb == other.iommu_tlb
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

    /// Paper-level successful CPU translation `CPU(self, vm, gpa) = page`.
    /// `cpu` makes the model's per-CPU TLB index explicit; the isolation theorem
    /// quantifies over it.
    pub open spec fn cpu_translates_to(
        &self,
        cpu: CpuId,
        vm: VmId,
        gpa: GuestPage,
        page: PhysPage,
    ) -> bool {
        let entry = self.effective_entry(cpu, vm, gpa);
        entry is Some && entry->Some_0.page == page
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

    /// Paper-level successful DMA translation `DMA(self, vm, iova) = page`.
    /// `stream` makes the model's per-stream SMMU-TLB index explicit; the theorem
    /// quantifies over it. `GuestPage` is reused as the regime-neutral IOVA-page
    /// representation.
    pub open spec fn dma_translates_to(
        &self,
        stream: CpuId,
        vm: VmId,
        iova: GuestPage,
        page: PhysPage,
    ) -> bool {
        let entry = self.iommu_effective_entry(stream, vm, iova);
        entry is Some && entry->Some_0.page == page
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

    pub open spec fn s2_classification_wf(&self) -> bool {
        &&& self.s2_private_pages.dom() == self.all_vms()
        &&& forall|vm1: VmId, vm2: VmId| #[trigger]
            self.all_vms().contains(vm1) && #[trigger] self.all_vms().contains(vm2) && vm1 != vm2
                ==> forall|page: PhysPage| #[trigger]
                self.s2_private_pages[vm1].contains(page) ==> !self.s2_private_pages[vm2].contains(page)
        &&& forall|vm: VmId| #[trigger]
            self.all_vms().contains(vm) ==> forall|page: PhysPage| #[trigger]
                self.s2_private_pages[vm].contains(page) ==> !self.s2_shared_pages.contains(page)
    }

    pub open spec fn translation_wf(&self) -> bool {
        forall|key: VmPageKey| #[trigger]
            self.s2_map.contains_key(key) ==> {
                &&& self.all_vms().contains(key.vm)
                &&& self.s2_private_or_shared(key.vm, self.s2_map[key].page)
            }
    }

    pub open spec fn iommu_classification_wf(&self) -> bool {
        &&& self.iommu_private_pages.dom() == self.all_vms()
        &&& forall|vm1: VmId, vm2: VmId| #[trigger]
            self.all_vms().contains(vm1) && #[trigger] self.all_vms().contains(vm2) && vm1 != vm2
                ==> forall|page: PhysPage| #[trigger]
                self.iommu_private_pages[vm1].contains(page) ==> !self.iommu_private_pages[vm2].contains(page)
        &&& forall|vm1: VmId, vm2: VmId| #[trigger]
            self.all_vms().contains(vm1) && #[trigger] self.all_vms().contains(vm2) && vm1 != vm2
                ==> forall|page: PhysPage| #[trigger]
                self.iommu_private_pages[vm1].contains(page) ==> !self.s2_private_pages[vm2].contains(page)
        &&& forall|vm: VmId| #[trigger]
            self.all_vms().contains(vm) ==> forall|page: PhysPage| #[trigger]
                self.iommu_private_pages[vm].contains(page) ==> !self.iommu_shared_pages.contains(page)
                // IOMMU-Private pages may be S2-Shared: these sets classify
                // different access paths. S2-Private pages remain disjoint
                // from IOMMU-Shared pages.
        &&& forall|vm: VmId| #[trigger]
            self.all_vms().contains(vm) ==> forall|page: PhysPage| #[trigger]
                self.s2_private_pages[vm].contains(page) ==> !self.iommu_shared_pages.contains(page)
    }

    pub open spec fn iommu_translation_wf(&self) -> bool {
        forall|key: VmPageKey| #[trigger]
            self.iommu_s2_map.contains_key(key) ==> {
                &&& self.all_vms().contains(key.vm)
                &&& self.iommu_private_pages.contains_key(key.vm)
                &&& (self.iommu_private_pages[key.vm].contains(self.iommu_s2_map[key].page)
                    || self.iommu_shared_pages.contains(self.iommu_s2_map[key].page))
            }
    }

    pub open spec fn iommu_wf(&self) -> bool {
        &&& self.iommu_classification_wf()
        &&& self.iommu_translation_wf()
    }

    pub open spec fn wf(&self) -> bool {
        &&& self.s2_classification_wf()
        &&& self.translation_wf()
        &&& self.iommu_wf()
        &&& self.tlb_safe()
        &&& self.iommu_tlb_safe()
        &&& self.sync()
        &&& self.iommu_sync()
    }
}

} // verus!
