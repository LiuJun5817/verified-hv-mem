use vstd::prelude::*;

verus! {

pub type DataWord = nat;

/// Fixed page granularity for the sketch. A higher-fidelity model can later
/// replace this with byte- or architecture-specific constants.
pub spec const PAGE_WORDS: nat = 512;

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
pub struct SharedPage {
    pub left: VmId,
    pub right: VmId,
    pub page: PhysPage,
}

/// The four entities in the model.
#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub enum Entity {
    SubjectVm,
    EnvironmentVm(VmId),
    Hypervisor,
    HardwareMmu,
}

/// Guest-originated requests that the hypervisor may later service.
#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub enum HyperCallReq {
    RequestMap(GuestPage, PhysPage, AccessPerms),
    RequestUnmap(GuestPage),
    RequestShare(PhysPage, VmId),
    RequestReclaim(PhysPage),
    RequestFlush(GuestPage),
}

#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub enum VmMemOp {
    Read(CpuId, GuestWordAddr),
    Write(CpuId, GuestWordAddr, DataWord),
    HyperCall(CpuId, HyperCallReq),
}

#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub enum HypervisorOp {
    Map(VmId, GuestPage, S2Entry),
    Unmap(VmId, GuestPage),
    AssignPage(VmId, PhysPage),
    ReclaimPage(VmId, PhysPage),
    SharePage(VmId, VmId, PhysPage),
    UnsharePage(VmId, VmId, PhysPage),
    ContextSwitch(CpuId, VmId),
    IssueTlbInvalidation(VmId, GuestPage),
}

#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub enum HardwareMmuOp {
    TlbFill(CpuId, VmId, GuestPage),
    TlbInvalidate(CpuId, VmId, GuestPage),
    ShootdownAck(CpuId, VmId, GuestPage),
}

#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub enum MachineAction {
    SubjectVm(VmMemOp),
    EnvironmentVm(VmId, VmMemOp),
    Hypervisor(HypervisorOp),
    HardwareMmu(HardwareMmuOp),
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

impl SharedPage {
    pub open spec fn reverse(self) -> SharedPage {
        SharedPage { left: self.right, right: self.left, page: self.page }
    }
}

impl TlbEntry {
    pub open spec fn as_s2_entry(self) -> S2Entry {
        S2Entry { page: self.page, access: self.access, generation: self.generation }
    }
}

impl MachineAction {
    pub open spec fn entity(self) -> Entity {
        match self {
            MachineAction::SubjectVm(_) => Entity::SubjectVm,
            MachineAction::EnvironmentVm(vm, _) => Entity::EnvironmentVm(vm),
            MachineAction::Hypervisor(_) => Entity::Hypervisor,
            MachineAction::HardwareMmu(_) => Entity::HardwareMmu,
        }
    }
}

} // verus!
