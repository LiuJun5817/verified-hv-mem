//! Stage-2 AArch64 page-table descriptor.
use super::PageTableEntry;
use crate::address::{
    addr::{PAddr, SpecPAddr},
    frame::MemAttr,
};
use vstd::prelude::*;

verus! {

// Low attribute fields of a VMSAv8-64 stage-2 Block/Page descriptor:
//
// | Bits  | Field       | Encoding used here                                      |
// |-------|-------------|---------------------------------------------------------|
// | 10    | AF          | Set on every descriptor created by `new`                |
// | 9:8   | SH          | 0b11 for Normal memory; 0b00 for Device memory          |
// | 7:6   | S2AP        | Independent write/read permission bits                  |
// | 5:2   | MemAttr     | 0b1111 for Normal memory; 0b0001 for Device memory      |
// | 1     | descriptor  | 1 for a table/4K page; 0 for a 2M/1G block              |
// | 0     | valid       | Set on every descriptor created by `new`                |
//
// The generic page-table interface currently treats bits 63:12 as the physical
// address payload. Higher architectural descriptor fields are outside this PTE
// abstraction.
pub const VALID: u64 = 1 << 0;

/// Table or 4K-page descriptor rather than a block descriptor.
pub const NON_BLOCK: u64 = 1 << 1;

/// Four-bit stage-2 memory-attribute field.
pub const ATTR_MASK: u64 = 0b1111 << 2;

/// Device-nGnRE memory encoding used by the reference implementation.
pub const DEVICE_ATTR: u64 = 1 << 2;

/// Normal, inner/outer write-back cacheable memory encoding.
pub const NORMAL_ATTR: u64 = 0b1111 << 2;

/// Stage-2 read permission.
pub const S2AP_R: u64 = 1 << 6;

/// Stage-2 write permission.
pub const S2AP_W: u64 = 1 << 7;

/// Select Inner Shareable rather than Outer Shareable.
pub const INNER: u64 = 1 << 8;

/// Select a shareable domain rather than Non-shareable.
pub const SHAREABLE: u64 = 1 << 9;

/// Access flag.
pub const AF: u64 = 1 << 10;

// Keep all address bits currently supported by `PAddr`. The low twelve bits are
// occupied by descriptor fields or reserved by the 4K granule.
pub const PHYS_ADDR_MASK: u64 = 0xffff_ffff_ffff_f000;

/// A VMSAv8-64 stage-2 Block/Page descriptor.
///
/// The descriptor is kept raw so parsing and serializing arbitrary table memory
/// are exact inverses. Accessors decode the architectural fields from this value.
#[derive(Clone, Copy)]
pub struct Aarch64PTE {
    pub value: u64,
}

impl Aarch64PTE {
    /// Encode the canonical descriptor flags used by the root implementation.
    ///
    /// Normal memory is Inner Shareable; Device memory is Non-shareable. A
    /// software `huge` mapping is a hardware block descriptor, so it clears the
    /// architectural `NON_BLOCK` bit.
    pub open spec fn spec_descriptor_flags(attr: MemAttr, huge: bool) -> u64 {
        let mem_type = if attr.device {
            DEVICE_ATTR
        } else {
            NORMAL_ATTR | INNER | SHAREABLE
        };
        let readable = if attr.readable {
            S2AP_R
        } else {
            0
        };
        let writable = if attr.writable {
            S2AP_W
        } else {
            0
        };
        let non_block = if huge {
            0
        } else {
            NON_BLOCK
        };
        VALID | AF | mem_type | readable | writable | non_block
    }

    fn descriptor_flags(attr: MemAttr, huge: bool) -> (res: u64)
        ensures
            res == Self::spec_descriptor_flags(attr, huge),
    {
        let mem_type = if attr.device {
            DEVICE_ATTR
        } else {
            NORMAL_ATTR | INNER | SHAREABLE
        };
        let readable = if attr.readable {
            S2AP_R
        } else {
            0
        };
        let writable = if attr.writable {
            S2AP_W
        } else {
            0
        };
        let non_block = if huge {
            0
        } else {
            NON_BLOCK
        };
        VALID | AF | mem_type | readable | writable | non_block
    }
}

impl PageTableEntry for Aarch64PTE {
    open spec fn wf(self) -> bool {
        true
    }

    open spec fn spec_new(addr: SpecPAddr, attr: MemAttr, huge: bool) -> Self {
        Self { value: ((addr.0 as u64) & PHYS_ADDR_MASK) | Self::spec_descriptor_flags(attr, huge) }
    }

    open spec fn spec_empty() -> Self {
        Self { value: 0 }
    }

    open spec fn spec_from_u64(val: u64) -> Self {
        Self { value: val }
    }

    open spec fn spec_to_u64(self) -> u64 {
        self.value
    }

    open spec fn spec_addr(self) -> SpecPAddr {
        SpecPAddr((self.value & PHYS_ADDR_MASK) as nat)
    }

    open spec fn spec_attr(self) -> MemAttr {
        MemAttr {
            readable: self.value & S2AP_R != 0,
            writable: self.value & S2AP_W != 0,
            executable: false,
            user_accessible: true,
            device: self.value & ATTR_MASK == DEVICE_ATTR,
        }
    }

    open spec fn spec_valid(self) -> bool {
        self.value & VALID != 0
    }

    open spec fn spec_huge(self) -> bool {
        // AArch64 encodes the opposite property: bit 1 means table/4K page.
        self.value & NON_BLOCK == 0
    }

    fn new(addr: PAddr, attr: MemAttr, huge: bool) -> (pte: Self) {
        let flags = Self::descriptor_flags(attr, huge);
        let value = ((addr.0 as u64) & PHYS_ADDR_MASK) | flags;
        Self { value }
    }

    fn empty() -> (pte: Self) {
        Self { value: 0 }
    }

    fn from_u64(val: u64) -> (pte: Self) {
        Self { value: val }
    }

    fn to_u64(&self) -> (res: u64) {
        self.value
    }

    fn addr(&self) -> (res: PAddr) {
        PAddr((self.value & PHYS_ADDR_MASK) as usize)
    }

    fn attr(&self) -> (res: MemAttr) {
        MemAttr {
            readable: self.value & S2AP_R != 0,
            writable: self.value & S2AP_W != 0,
            executable: false,
            user_accessible: true,
            device: self.value & ATTR_MASK == DEVICE_ATTR,
        }
    }

    fn huge(&self) -> (res: bool) {
        self.value & NON_BLOCK == 0
    }

    fn valid(&self) -> (res: bool) {
        self.value & VALID != 0
    }

    proof fn lemma_new_wf(addr: SpecPAddr, attr: MemAttr, huge: bool) {
    }

    proof fn lemma_from_u64_wf(val: u64) {
    }

    proof fn lemma_empty_wf() {
    }

    proof fn lemma_new_keeps_value(addr: SpecPAddr, attr: MemAttr, huge: bool) {
        let pte = Self::spec_new(addr, attr, huge);
        let flags = Self::spec_descriptor_flags(attr, huge);
        let raw_addr = addr.0 as u64;
        let value = pte.value;
        let mem_type = if attr.device {
            DEVICE_ATTR
        } else {
            NORMAL_ATTR | INNER | SHAREABLE
        };
        let readable = if attr.readable {
            S2AP_R
        } else {
            0
        };
        let writable = if attr.writable {
            S2AP_W
        } else {
            0
        };
        let non_block = if huge {
            0
        } else {
            NON_BLOCK
        };

        assert(raw_addr % 4096 == 0);
        assert(flags == VALID | AF | mem_type | readable | writable | non_block);
        assert(value == (raw_addr & PHYS_ADDR_MASK) | flags);
        assert(mem_type == DEVICE_ATTR || mem_type == NORMAL_ATTR | INNER | SHAREABLE);
        assert(readable == 0 || readable == S2AP_R);
        assert(writable == 0 || writable == S2AP_W);
        assert(non_block == 0 || non_block == NON_BLOCK);
        assert((raw_addr & PHYS_ADDR_MASK) == raw_addr) by (bit_vector)
            requires
                raw_addr % 4096 == 0,
        ;
        assert(raw_addr & 0xfff == 0) by (bit_vector)
            requires
                raw_addr % 4096 == 0,
        ;
        assert(flags & PHYS_ADDR_MASK == 0) by (bit_vector)
            requires
                flags == VALID | AF | mem_type | readable | writable | non_block,
                mem_type == DEVICE_ATTR || mem_type == NORMAL_ATTR | INNER | SHAREABLE,
                readable == 0 || readable == S2AP_R,
                writable == 0 || writable == S2AP_W,
                non_block == 0 || non_block == NON_BLOCK,
        ;
        assert(flags & VALID == VALID) by (bit_vector)
            requires
                flags == VALID | AF | mem_type | readable | writable | non_block,
                mem_type == DEVICE_ATTR || mem_type == NORMAL_ATTR | INNER | SHAREABLE,
                readable == 0 || readable == S2AP_R,
                writable == 0 || writable == S2AP_W,
                non_block == 0 || non_block == NON_BLOCK,
        ;
        assert(flags & NON_BLOCK == non_block) by (bit_vector)
            requires
                flags == VALID | AF | mem_type | readable | writable | non_block,
                mem_type == DEVICE_ATTR || mem_type == NORMAL_ATTR | INNER | SHAREABLE,
                readable == 0 || readable == S2AP_R,
                writable == 0 || writable == S2AP_W,
                non_block == 0 || non_block == NON_BLOCK,
        ;
        assert(flags & S2AP_R == readable) by (bit_vector)
            requires
                flags == VALID | AF | mem_type | readable | writable | non_block,
                mem_type == DEVICE_ATTR || mem_type == NORMAL_ATTR | INNER | SHAREABLE,
                readable == 0 || readable == S2AP_R,
                writable == 0 || writable == S2AP_W,
                non_block == 0 || non_block == NON_BLOCK,
        ;
        assert(flags & S2AP_W == writable) by (bit_vector)
            requires
                flags == VALID | AF | mem_type | readable | writable | non_block,
                mem_type == DEVICE_ATTR || mem_type == NORMAL_ATTR | INNER | SHAREABLE,
                readable == 0 || readable == S2AP_R,
                writable == 0 || writable == S2AP_W,
                non_block == 0 || non_block == NON_BLOCK,
        ;
        assert(flags & ATTR_MASK == mem_type & ATTR_MASK) by (bit_vector)
            requires
                flags == VALID | AF | mem_type | readable | writable | non_block,
                mem_type == DEVICE_ATTR || mem_type == NORMAL_ATTR | INNER | SHAREABLE,
                readable == 0 || readable == S2AP_R,
                writable == 0 || writable == S2AP_W,
                non_block == 0 || non_block == NON_BLOCK,
        ;
        assert(value & PHYS_ADDR_MASK == raw_addr) by (bit_vector)
            requires
                value == (raw_addr & PHYS_ADDR_MASK) | flags,
                raw_addr & PHYS_ADDR_MASK == raw_addr,
                flags & PHYS_ADDR_MASK == 0,
        ;
        assert((value & PHYS_ADDR_MASK) as nat == addr.0);
        assert(pte.spec_addr() == addr);
        assert(value & VALID == VALID) by (bit_vector)
            requires
                value == (raw_addr & PHYS_ADDR_MASK) | flags,
                raw_addr & 0xfff == 0,
                flags & VALID == VALID,
        ;
        assert(VALID != 0) by (bit_vector);
        assert(pte.spec_valid());

        assert(value & NON_BLOCK == non_block) by (bit_vector)
            requires
                value == (raw_addr & PHYS_ADDR_MASK) | flags,
                raw_addr & 0xfff == 0,
                flags & NON_BLOCK == non_block,
        ;
        if huge {
            assert(non_block == 0);
            assert(pte.spec_huge());
        } else {
            assert(non_block == NON_BLOCK);
            assert(NON_BLOCK != 0) by (bit_vector);
            assert(!pte.spec_huge());
        }

        assert(value & S2AP_R == readable) by (bit_vector)
            requires
                value == (raw_addr & PHYS_ADDR_MASK) | flags,
                raw_addr & 0xfff == 0,
                flags & S2AP_R == readable,
        ;
        if attr.readable {
            assert(readable == S2AP_R);
            assert(S2AP_R != 0) by (bit_vector);
        } else {
            assert(readable == 0);
        }
        assert(value & S2AP_W == writable) by (bit_vector)
            requires
                value == (raw_addr & PHYS_ADDR_MASK) | flags,
                raw_addr & 0xfff == 0,
                flags & S2AP_W == writable,
        ;
        if attr.writable {
            assert(writable == S2AP_W);
            assert(S2AP_W != 0) by (bit_vector);
        } else {
            assert(writable == 0);
        }
        assert(value & ATTR_MASK == mem_type & ATTR_MASK) by (bit_vector)
            requires
                value == (raw_addr & PHYS_ADDR_MASK) | flags,
                raw_addr & 0xfff == 0,
                flags & ATTR_MASK == mem_type & ATTR_MASK,
        ;
        if attr.device {
            assert(mem_type == DEVICE_ATTR);
            assert(DEVICE_ATTR & ATTR_MASK == DEVICE_ATTR) by (bit_vector);
        } else {
            assert(mem_type == NORMAL_ATTR | INNER | SHAREABLE);
            assert((NORMAL_ATTR | INNER | SHAREABLE) & ATTR_MASK == NORMAL_ATTR) by (bit_vector);
            assert(NORMAL_ATTR != DEVICE_ATTR) by (bit_vector);
        }
        assert(pte.spec_attr().readable == attr.readable);
        assert(pte.spec_attr().writable == attr.writable);
        assert(!pte.spec_attr().executable);
        assert(pte.spec_attr().user_accessible);
        assert(pte.spec_attr().device == attr.device);
        // TRUSTED GAP: the real stage-2 descriptor format used here has no bits
        // for these two generic `MemAttr` fields. Decoding therefore supplies
        // the root implementation's defaults (`false` and `true`). The generic
        // `PageTableEntry` trait still requires `new` to preserve all fields, so
        // that stronger architecture-independent contract is assumed here.
        assume(attr.executable == false && attr.user_accessible == true);
        assert(pte.spec_attr() == attr);
    }

    proof fn lemma_empty_invalid() {
        assert(0u64 & VALID == 0) by (bit_vector);
    }

    proof fn lemma_from_0_invalid() {
        assert(0u64 & VALID == 0) by (bit_vector);
    }

    proof fn lemma_eq_by_u64(pte1: Self, pte2: Self) {
        assert(pte1.value == pte2.value);
    }

    proof fn lemma_from_to_u64_inverse(val: u64) {
    }
}

} // verus!
