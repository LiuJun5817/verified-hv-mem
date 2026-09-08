use crate::constants::*;
use vstd::prelude::*;

verus! {

pub type DataWord = nat;

#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub struct VmId(pub nat);

#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub struct CpuId(pub nat);

#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub struct GuestPage(pub nat);

#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub struct PhysPage(pub nat);

#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub struct GuestWordAddr(pub nat);

#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub struct PhysWordAddr(pub nat);

#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub struct AccessPerms {
    pub read: bool,
    pub write: bool,
    pub execute: bool,
}

#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub struct S2Entry {
    pub page: PhysPage,
    pub access: AccessPerms,
    /// Generation numbers let the model distinguish current translations from
    /// stale TLB entries that still await invalidation.
    pub generation: nat,
}

#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub struct TlbEntry {
    pub page: PhysPage,
    pub access: AccessPerms,
    pub generation: nat,
}

#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub struct VmPageKey {
    pub vm: VmId,
    pub gpa: GuestPage,
}

#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub struct TlbKey {
    pub cpu: CpuId,
    pub vm: VmId,
    pub gpa: GuestPage,
}

#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub enum VmMemOp {
    Read(CpuId, GuestWordAddr),
    Write(CpuId, GuestWordAddr, DataWord),
}

#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub enum HypervisorOp {
    /// Add a new VM to the system, with no CPU or IOMMU mappings.
    AddVm(VmId),
    /// Remove a VM from the system.
    RemoveVm(VmId),
    /// Install one CPU mapping and classify its target as S2-Private.
    MapS2Private(VmId, GuestPage, S2Entry),
    /// Remove one CPU mapping and its matching S2-Private classification.
    UnmapS2Private(VmId, GuestPage, PhysPage),
    /// Install one CPU mapping and classify its target as S2-Shared.
    MapS2Shared(VmId, GuestPage, S2Entry),
    /// Remove one CPU mapping and update the dynamic S2-Shared projection.
    UnmapS2Shared(VmId, GuestPage),
    /// Install one IOMMU mapping and classify its target as IOMMU-Private.
    MapIommuPrivate(VmId, GuestPage, S2Entry),
    /// Remove one IOMMU mapping and its IOMMU-Private classification.
    UnmapIommuPrivate(VmId, GuestPage, PhysPage),
    /// Install one IOMMU mapping and classify its target as IOMMU-Shared.
    MapIommuShared(VmId, GuestPage, S2Entry),
    /// Remove one IOMMU mapping and update the dynamic IOMMU-Shared projection.
    UnmapIommuShared(VmId, GuestPage),
}

/// A guest VM step and a hypervisor step are the two machine actions.  TLB
/// management is folded into the hypervisor mapping steps (a SW–HW cowork),
/// so there is no standalone hardware-MMU action.
#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub enum MachineAction {
    Vm(VmId, VmMemOp),
    Hypervisor(HypervisorOp),
}

impl GuestWordAddr {
    pub open spec fn page(self) -> GuestPage {
        GuestPage(self.0 / PAGE_WORDS)
    }

    pub open spec fn offset(self) -> nat {
        self.0 % PAGE_WORDS
    }
}

impl PhysWordAddr {
    pub open spec fn page(self) -> PhysPage {
        PhysPage(self.0 / PAGE_WORDS)
    }

    pub open spec fn offset(self) -> nat {
        self.0 % PAGE_WORDS
    }
}

impl GuestPage {
    pub open spec fn word(self, offset: nat) -> GuestWordAddr
        recommends
            offset < PAGE_WORDS,
    {
        GuestWordAddr(self.0 * PAGE_WORDS + offset)
    }
}

impl PhysPage {
    pub open spec fn word(self, offset: nat) -> PhysWordAddr
        recommends
            offset < PAGE_WORDS,
    {
        PhysWordAddr(self.0 * PAGE_WORDS + offset)
    }
}

impl VmPageKey {
    pub open spec fn new(vm: VmId, gpa: GuestPage) -> Self {
        Self { vm, gpa }
    }
}

impl TlbKey {
    pub open spec fn new(cpu: CpuId, vm: VmId, gpa: GuestPage) -> Self {
        Self { cpu, vm, gpa }
    }
}

impl TlbEntry {
    pub open spec fn as_s2_entry(self) -> S2Entry {
        S2Entry { page: self.page, access: self.access, generation: self.generation }
    }
}

} // verus!
