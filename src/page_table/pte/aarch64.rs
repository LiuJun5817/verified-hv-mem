use vstd::prelude::*;
use crate::address::{
    addr::{PAddr, PAddrExec},
    frame::{FrameSize, MemAttr}
};
use super::{GhostPTE, ExecPTE};
use crate::page_table::pt_arch::{PTArchExec, PTArchLevelExec};

verus! {

/// Aarch64 ghost PTE. TODO: proof not completed.
///
/// |addr: 63-12||padding: 11-7||attr: 6-2||huge: 1||valid: 0|
pub struct Aarch64GhostPTE {
    pub addr: PAddr,
    pub attr: MemAttr,
    pub huge: bool,
    pub valid: bool,
}

impl GhostPTE for Aarch64GhostPTE {
    open spec fn new(addr: PAddr, attr: MemAttr, huge: bool) -> Self {
        Self { addr, attr, huge, valid: true }
    }

    open spec fn empty() -> Self {
        Self { addr: PAddr(0nat), attr: MemAttr::spec_default(), huge: false, valid: false }
    }

    open spec fn addr(self) -> PAddr {
        self.addr
    }

    open spec fn attr(self) -> MemAttr {
        self.attr
    }

    open spec fn valid(self) -> bool {
        self.valid
    }

    open spec fn huge(self) -> bool {
        self.huge
    }

    open spec fn from_u64(val: u64) -> Self {
        let addr = PAddr((val >> 12 << 12) as nat);
        let readable = val & 0b100 != 0;
        let writable = val & 0b1000 != 0;
        let executable = val & 0b10000 != 0;
        let user_accessible = val & 0b100000 != 0;
        let device = val & 0b1000000 != 0;
        let huge = val & 0b10 != 0;
        let valid = val & 0b1 != 0;
        Self {
            addr,
            attr: MemAttr { readable, writable, executable, user_accessible, device },
            huge,
            valid,
        }
    }

    open spec fn to_u64(self) -> u64 {
        let a = self.addr.0 as u64 >> 12 << 12;
        let b = if self.attr.readable {
            0b100
        } else {
            0
        };
        let c = if self.attr.writable {
            0b1000
        } else {
            0
        };
        let d = if self.attr.executable {
            0b10000
        } else {
            0
        };
        let e = if self.attr.user_accessible {
            0b100000
        } else {
            0
        };
        let f = if self.attr.device {
            0b1000000
        } else {
            0
        };
        let g = if self.huge {
            0b10
        } else {
            0
        };
        let h = if self.valid {
            0b1
        } else {
            0
        };
        a | b | c | d | e | f | g | h
    }

    proof fn lemma_empty_invalid() {
    }

    proof fn lemma_from_0_invalid() {
        admit()
    }

    proof fn lemma_from_to_u64_inverse(val: u64) {
        admit()
    }

    proof fn lemma_new_keeps_value(addr: PAddr, attr: MemAttr, huge: bool) {
    }

    proof fn lemma_eq_by_u64(pte1: Self, pte2: Self) {
        admit()
    }
}

} // verus!

bitflags::bitflags! {
    /// Memory attribute fields in the VMSAv8-64 translation table format descriptors.
    #[derive(Clone, Copy, Debug)]
    pub struct DescriptorFlags: u64 {
        // Attribute fields in stage 2 VMSAv8-64 Block and Page descriptors:

        /// Whether the descriptor is valid.
        const VALID =       1 << 0;
        /// The descriptor gives the address of the next level of translation table or 4KB page.
        /// (not a 2M, 1G block)
        const NON_BLOCK =   1 << 1;
        /// Memory attributes index field.
        const ATTR      =   0b1111 << 2;
        /// Access permission: accessable at EL0/1, Read / Write.
        const S2AP_R      =   1 << 6;
        /// Access permission: accessable at EL0/1, Write.
        const S2AP_W      =   1 << 7;
        /// Shareability: Inner Shareable (otherwise Outer Shareable).
        const INNER     =   1 << 8;
        /// Shareability: Inner or Outer Shareable (otherwise Non-shareable).
        const SHAREABLE =   1 << 9;
        /// The Access flag.
        const AF =          1 << 10;
    }
}

#[repr(u64)]
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum MemType {
    Device = 1,
    Normal = 15,
}

impl DescriptorFlags {
    const ATTR_INDEX_MASK: u64 = 0b1111_00;

    fn from_mem_type(mem_type: MemType) -> Self {
        let mut bits = (mem_type as u64) << 2;
        match mem_type {
            MemType::Normal => bits |= Self::INNER.bits() | Self::SHAREABLE.bits(),
            _ => (),
        }
        Self::from_bits_truncate(bits)
    }

    fn mem_type(&self) -> MemType {
        let idx = (self.bits() & Self::ATTR_INDEX_MASK) >> 2;
        match idx {
            1 => MemType::Device,
            15 => MemType::Normal,
            _ => panic!("Invalid memory attribute index"),
        }
    }

    fn valid(&self) -> bool {
        self.contains(Self::VALID)
    }

    fn huge(&self) -> bool {
        !self.contains(Self::NON_BLOCK)
    }

    fn from_mem_attr(attr: MemAttr, huge: bool) -> Self {
        let mut flags = if attr.device {
            Self::from_mem_type(MemType::Device)
        } else {
            Self::from_mem_type(MemType::Normal)
        };
        flags |= Self::VALID | Self::AF;
        if attr.readable {
            flags |= Self::S2AP_R;
        }
        if attr.writable {
            flags |= Self::S2AP_W;
        }
        if huge {
            flags &= !Self::NON_BLOCK;
        } else {
            flags |= Self::NON_BLOCK;
        }
        flags
    }

    fn to_mem_attr(&self) -> MemAttr {
        MemAttr {
            readable: self.contains(Self::S2AP_R),
            writable: self.contains(Self::S2AP_W),
            executable: false,
            user_accessible: true,
            device: self.mem_type() == MemType::Device,
        }
    }
}

verus! {

/// Aarch64 exec PTE. TODO: proof not completed.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Aarch64PTE(u64);

impl Aarch64PTE {
    const PHYS_ADDR_MASK: usize = 0xffff_ffff_ffff & !(4096 - 1);

    pub const fn empty() -> Self {
        Self(0)
    }

    fn descriptor_flags(&self) -> DescriptorFlags {
        DescriptorFlags::from_bits_truncate(self.0)
    }

    fn set_addr(&mut self, paddr: u64) {
        self.0 = (self.0 & !Self::PHYS_ADDR_MASK as u64) | (paddr & Self::PHYS_ADDR_MASK as u64);
    }

    fn set_flags(&mut self, flags: DescriptorFlags) {
        self.0 = (flags.bits() & !Self::PHYS_ADDR_MASK as u64) | (self.0 as u64
            & Self::PHYS_ADDR_MASK as u64);
    }
}

impl ExecPTE<Aarch64GhostPTE> for Aarch64PTE {
    open spec fn view(self) -> Aarch64GhostPTE {
        // TODO: this is a fake implementation
        Aarch64GhostPTE { addr: PAddr(0), attr: MemAttr::default(), huge: false, valid: true }
    }

    fn new(addr: PAddrExec, attr: MemAttr, huge: bool) -> Self {
        let mut pte = Self::empty();
        pte.set_addr(addr.0 as u64);
        pte.set_flags(DescriptorFlags::from_mem_attr(attr, huge));
        pte
    }

    fn empty() -> Self {
        Self::empty()
    }

    fn addr(&self) -> (res: PAddrExec) {
        PAddrExec((self.0 as usize) & Self::PHYS_ADDR_MASK)
    }

    fn attr(&self) -> (res: MemAttr) {
        self.descriptor_flags().to_mem_attr()
    }

    fn huge(&self) -> (res: bool) {
        self.descriptor_flags().huge()
    }

    fn valid(&self) -> (res: bool) {
        self.descriptor_flags().valid()
    }

    fn from_u64(val: u64) -> (pte: Self) {
        Self(val)
    }

    fn to_u64(&self) -> (res: u64) {
        self.0
    }
}

/// For VMSAv8-64 using 4K granule. The 4-level architecture is specified as follows:
///
/// | Level | Index into PT | Entry Num |  Entry Type  | Frame Size |
/// |-------|---------------|-----------|--------------|------------|
/// | 0     | 47:39         | 512       | Table        | 512G       |
/// | 1     | 38:30         | 512       | Table/Block  | 1G         |
/// | 2     | 29:21         | 512       | Table/Block  | 2M         |
/// | 3     | 20:12         | 512       | Page         | 4K         |
///
/// If effective value of TCR_ELx.DS is 0, level 0 allows Table descriptor only.
pub fn vmsav8_4k_4level_arch() -> PTArchExec {
    PTArchExec(
        [
            PTArchLevelExec { entry_count: 512, frame_size: FrameSize::Size512G },
            PTArchLevelExec { entry_count: 512, frame_size: FrameSize::Size1G },
            PTArchLevelExec { entry_count: 512, frame_size: FrameSize::Size2M },
            PTArchLevelExec { entry_count: 512, frame_size: FrameSize::Size4K },
        ].to_vec(),
    )
}

/// For VMSAv8-64 using 4K granule. The 3-level architecture is specified as follows:
///
/// | Level | Index into PT | Entry Num |  Entry Type  | Frame Size |
/// |-------|---------------|-----------|--------------|------------|
/// | 1     | 38:30         | 512       | Table/Block  | 1G         |
/// | 2     | 29:21         | 512       | Table/Block  | 2M         |
/// | 3     | 20:12         | 512       | Page         | 4K         |
pub fn vmsav8_4k_3level_arch() -> PTArchExec {
    PTArchExec(
        [
            PTArchLevelExec { entry_count: 512, frame_size: FrameSize::Size1G },
            PTArchLevelExec { entry_count: 512, frame_size: FrameSize::Size2M },
            PTArchLevelExec { entry_count: 512, frame_size: FrameSize::Size4K },
        ].to_vec(),
    )
}

} // verus!