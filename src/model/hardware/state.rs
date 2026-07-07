use vstd::prelude::*;

use crate::model::types::*;

verus! {

/// The concrete, execution-visible substrate of running guests.
///
/// `HardwareView` holds the part of the machine a VM — or the security property —
/// can *observe or perturb*: the **hardware-reachable** stage-2 map, the TLB that
/// caches translations and may lag a mapping edit, the data memory reachable
/// through translation, and the per-CPU VM schedule.  Everything *authoritative*
/// (ownership, the intended mapping `SoftwareView::s2_map`, the memory partition) is
/// policy and lives in [`crate::model::software::SoftwareView`].
///
/// # Two stage-2 maps: hardware-reachable here, software-maintained in `SoftwareView`
///
/// `HardwareView::s2map` is what a page-table walk currently **reaches** (the walker
/// view); [`SoftwareView::s2_map`](crate::model::software::SoftwareView) is what the page
/// table **bytes say** (the software-maintained view).  They are the same kind of
/// distinction as `MmuSpec` vs `BudgetSpec`: between a `pt.unmap` (which drops the
/// page from the byte view immediately) and the following `DSB` (which drops it
/// from the walker view), the two diverge — that is the break-before-make window.
/// Their agreement, [`MachineState::sync`](crate::model::machine::MachineState),
/// is a machine-level well-formedness clause, *not* a hardware invariant.
///
/// # `tlb_safe` is a hardware invariant
///
/// The TLB caches the *hardware-reachable* map, so coherence — every cached entry
/// agrees with `s2map` — is expressible purely over `HardwareView` and holds at every
/// hardware state ([`tlb_safe`](HardwareView::tlb_safe)).  Invalidation is modelled
/// atomically (the `DSB`+`TLBI` of an unmap drop the page from `s2map` and flush
/// its cached entries together), so there is no state in which a cached entry
/// outlives its mapping; hence `tlb_safe` is inductive here.  There is therefore no
/// "being-invalidated" window and no pending-invalidation state to track.
///
/// These fields are never stored in exec variables; callers supply them as
/// `Ghost<HardwareView>` witnesses that are erased at compile time.
pub ghost struct HardwareView {
    /// Current TLB contents, keyed by `(cpu, vm, gpa)`.
    pub tlb: Map<TlbKey, TlbEntry>,
    /// The **hardware-reachable** stage-2 map (the walker view): what a page-table
    /// walk resolves right now.  Lags the page-table bytes (`SoftwareView::s2_map`) until
    /// the completing `DSB` of a mapping edit.
    pub s2map: Map<VmPageKey, S2Entry>,
    /// Current SMMU/IOMMU TLB contents.  This uses the same regime-neutral TLB key as
    /// `MmuSpec`; the IOMMU instance is separate from the CPU MMU instance.
    pub iommu_tlb: Map<TlbKey, TlbEntry>,
    /// The **IOMMU hardware-reachable** stage-2 map.  This is the SMMU walker view,
    /// synchronized against `SoftwareView::iommu_s2_map` at machine sync points.
    pub iommu_s2map: Map<VmPageKey, S2Entry>,
    /// The VM-observable **data plane**: physical memory values at addresses that
    /// translations resolve to (VM-owned ∪ shared pages).  This is *not* a model
    /// of all DRAM — page-table bytes and hypervisor-internal memory are
    /// abstracted into `SoftwareView` (`s2_map`, ownership) and realized only in the
    /// implementation, tied back by the refinement layers.
    pub memory: Map<PhysWordAddr, DataWord>,
    /// Which VM is currently scheduled on each CPU.
    pub active_vm: Map<CpuId, VmId>,
}

impl HardwareView {
    /// **TLB coherence — the load-bearing hardware invariant.** Every cached entry's
    /// page is still hardware-reachable (`s2map` contains it) and the cached value
    /// agrees with `s2map`.  Purely over `HardwareView`: the TLB caches the
    /// hardware-reachable map, so no software reference is needed.
    pub open spec fn tlb_safe(&self) -> bool {
        forall|key: TlbKey| #[trigger]
            self.tlb.contains_key(key) ==> {
                let sk = VmPageKey::new(key.vm, key.gpa);
                &&& self.s2map.contains_key(sk)
                &&& self.tlb[key].as_s2_entry() == self.s2map[sk]
            }
    }

    /// IOMMU TLB coherence, mirroring [`tlb_safe`](Self::tlb_safe) for the SMMU
    /// walker-reachable map.
    pub open spec fn iommu_tlb_safe(&self) -> bool {
        forall|key: TlbKey| #[trigger]
            self.iommu_tlb.contains_key(key) ==> {
                let sk = VmPageKey::new(key.vm, key.gpa);
                &&& self.iommu_s2map.contains_key(sk)
                &&& self.iommu_tlb[key].as_s2_entry() == self.iommu_s2map[sk]
            }
    }

    /// Hardware well-formedness: TLB coherence (invalidation is atomic, so this is
    /// the whole hardware invariant).
    pub open spec fn wf(&self) -> bool {
        &&& self.tlb_safe()
        &&& self.iommu_tlb_safe()
    }
}

} // verus!
