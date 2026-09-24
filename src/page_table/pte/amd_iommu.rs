//! AMD IOMMU page-table entry.
use super::PageTableEntry;
use crate::address::{
    addr::{PAddr, SpecPAddr},
    frame::MemAttr,
};
use vstd::prelude::*;

verus! {

// Fields used by an AMD IOMMU page-table entry:
//
// | Bits  | Field            | Encoding used here                              |
// |-------|------------------|-------------------------------------------------|
// | 62    | IW               | DMA write permission                            |
// | 61    | IR               | DMA read permission                             |
// | 51:12 | physical address | Host physical frame or next-level table         |
// | 11:9  | next level       | Zero marks a leaf; nonzero selects another table|
// | 0     | valid            | Set on every constructed leaf and table entry   |

/// Valid entry.
pub const AMD_IOMMU_VALID: u64 = 1 << 0;
/// Next-level field used by AMD IOMMU page-table entries.
pub const AMD_IOMMU_NEXT_LEVEL_MASK: u64 = 0b111 << 9;
/// Physical-address bits used by the AMD IOMMU implementation.
pub const AMD_IOMMU_PHYS_ADDR_MASK: u64 = 0x000f_ffff_ffff_f000;
/// DMA read permission.
pub const AMD_IOMMU_IR: u64 = 1 << 61;
/// DMA write permission.
pub const AMD_IOMMU_IW: u64 = 1 << 62;

/// AMD IOMMU translation entry.
#[derive(Clone, Copy)]
pub struct AmdIommuPTE {
    pub value: u64,
}

impl AmdIommuPTE {
    pub open spec fn spec_leaf_flags(attr: MemAttr) -> u64 {
        let readable = if attr.readable { AMD_IOMMU_IR } else { 0 };
        let writable = if attr.writable { AMD_IOMMU_IW } else { 0 };
        AMD_IOMMU_VALID | readable | writable
    }

    fn leaf_flags(attr: MemAttr) -> (res: u64)
        ensures
            res == Self::spec_leaf_flags(attr),
    {
        let readable = if attr.readable { AMD_IOMMU_IR } else { 0 };
        let writable = if attr.writable { AMD_IOMMU_IW } else { 0 };
        AMD_IOMMU_VALID | readable | writable
    }
}

impl PageTableEntry for AmdIommuPTE {
    open spec fn wf(self) -> bool {
        true
    }

    open spec fn spec_supports_attr(attr: MemAttr) -> bool {
        attr.readable && !attr.executable && !attr.device
    }

    open spec fn spec_new(addr: SpecPAddr, attr: MemAttr, _huge: bool) -> Self {
        Self {
            value: ((addr.0 as u64) & AMD_IOMMU_PHYS_ADDR_MASK) | Self::spec_leaf_flags(attr),
        }
    }

    open spec fn spec_new_table(addr: SpecPAddr, next_level: nat) -> Self {
        let encoded_level = if 0 < next_level < 8 { next_level as u64 } else { 1u64 };
        Self {
            value: ((addr.0 as u64) & AMD_IOMMU_PHYS_ADDR_MASK)
                | AMD_IOMMU_VALID
                | AMD_IOMMU_IR
                | AMD_IOMMU_IW
                | (encoded_level << 9),
        }
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
        SpecPAddr((self.value & AMD_IOMMU_PHYS_ADDR_MASK) as nat)
    }

    open spec fn spec_attr(self) -> MemAttr {
        MemAttr {
            readable: self.value & AMD_IOMMU_IR != 0,
            writable: self.value & AMD_IOMMU_IW != 0,
            executable: false,
            device: false,
        }
    }

    open spec fn spec_valid(self) -> bool {
        self.value & AMD_IOMMU_VALID != 0
    }

    open spec fn spec_huge(self) -> bool {
        self.value & AMD_IOMMU_NEXT_LEVEL_MASK == 0
    }

    fn new(addr: PAddr, attr: MemAttr, _huge: bool) -> (pte: Self) {
        let flags = Self::leaf_flags(attr);
        Self { value: ((addr.0 as u64) & AMD_IOMMU_PHYS_ADDR_MASK) | flags }
    }

    fn new_table(addr: PAddr, next_level: usize) -> (pte: Self) {
        let encoded_level = if 0 < next_level && next_level < 8 { next_level } else { 1 };
        Self {
            value: ((addr.0 as u64) & AMD_IOMMU_PHYS_ADDR_MASK)
                | AMD_IOMMU_VALID
                | AMD_IOMMU_IR
                | AMD_IOMMU_IW
                | ((encoded_level as u64) << 9),
        }
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
        PAddr((self.value & AMD_IOMMU_PHYS_ADDR_MASK) as usize)
    }

    fn attr(&self) -> (res: MemAttr) {
        MemAttr {
            readable: self.value & AMD_IOMMU_IR != 0,
            writable: self.value & AMD_IOMMU_IW != 0,
            executable: false,
            device: false,
        }
    }

    fn valid(&self) -> (res: bool) {
        self.value & AMD_IOMMU_VALID != 0
    }

    fn huge(&self) -> (res: bool) {
        self.value & AMD_IOMMU_NEXT_LEVEL_MASK == 0
    }

    proof fn lemma_new_wf(addr: SpecPAddr, attr: MemAttr, huge: bool) {
    }

    proof fn lemma_new_table_wf(addr: SpecPAddr, next_level: nat) {
    }

    proof fn lemma_from_u64_wf(val: u64) {
    }

    proof fn lemma_empty_wf() {
    }

    proof fn lemma_new_keeps_value(addr: SpecPAddr, attr: MemAttr, huge: bool) {
        let pte = Self::spec_new(addr, attr, huge);
        let raw_addr = addr.0 as u64;
        let readable = if attr.readable { AMD_IOMMU_IR } else { 0 };
        let writable = if attr.writable { AMD_IOMMU_IW } else { 0 };
        let flags = AMD_IOMMU_VALID | readable | writable;
        let value = pte.value;

        assert(raw_addr % 4096 == 0);
        assert(raw_addr < 0x1_0000_0000_0000u64);
        assert((raw_addr & AMD_IOMMU_PHYS_ADDR_MASK) == raw_addr) by (bit_vector)
            requires
                raw_addr % 4096 == 0,
                raw_addr < 0x1_0000_0000_0000u64;
        assert(raw_addr & 0xfff == 0) by (bit_vector)
            requires raw_addr % 4096 == 0;
        assert(value == raw_addr | flags);
        assert(value & AMD_IOMMU_PHYS_ADDR_MASK == raw_addr) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr & AMD_IOMMU_PHYS_ADDR_MASK == raw_addr,
                flags == AMD_IOMMU_VALID | readable | writable,
                readable == 0 || readable == AMD_IOMMU_IR,
                writable == 0 || writable == AMD_IOMMU_IW;
        assert(pte.spec_addr() == addr);

        assert(value & AMD_IOMMU_VALID == AMD_IOMMU_VALID) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr & 0xfff == 0,
                flags == AMD_IOMMU_VALID | readable | writable;
        assert(AMD_IOMMU_VALID != 0) by (bit_vector);
        assert(pte.spec_valid());
        assert(value & AMD_IOMMU_IR == readable) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr < 0x1_0000_0000_0000u64,
                flags == AMD_IOMMU_VALID | readable | writable,
                readable == 0 || readable == AMD_IOMMU_IR,
                writable == 0 || writable == AMD_IOMMU_IW;
        assert(readable == AMD_IOMMU_IR);
        assert(AMD_IOMMU_IR != 0) by (bit_vector);
        assert(value & AMD_IOMMU_IW == writable) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr < 0x1_0000_0000_0000u64,
                flags == AMD_IOMMU_VALID | readable | writable,
                readable == 0 || readable == AMD_IOMMU_IR,
                writable == 0 || writable == AMD_IOMMU_IW;
        if attr.writable {
            assert(writable == AMD_IOMMU_IW);
            assert(AMD_IOMMU_IW != 0) by (bit_vector);
        } else {
            assert(writable == 0);
        }
        assert(value & AMD_IOMMU_NEXT_LEVEL_MASK == 0) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr & 0xfff == 0,
                flags == AMD_IOMMU_VALID | readable | writable,
                readable == 0 || readable == AMD_IOMMU_IR,
                writable == 0 || writable == AMD_IOMMU_IW;
        assert(pte.spec_huge());
        assert(pte.spec_attr().readable == attr.readable);
        assert(pte.spec_attr().writable == attr.writable);
        assert(pte.spec_attr().executable == attr.executable);
        assert(pte.spec_attr().device == attr.device);
        assert(pte.spec_attr() == attr);
    }

    proof fn lemma_new_table_keeps_value(addr: SpecPAddr, next_level: nat) {
        let pte = Self::spec_new_table(addr, next_level);
        let raw_addr = addr.0 as u64;
        let raw_level = if 0 < next_level < 8 { next_level as u64 } else { 1u64 };
        let encoded_level = raw_level << 9;
        let flags = AMD_IOMMU_VALID | AMD_IOMMU_IR | AMD_IOMMU_IW | encoded_level;
        let value = pte.value;

        assert(raw_addr % 4096 == 0);
        assert(raw_addr < 0x1_0000_0000_0000u64);
        assert((raw_addr & AMD_IOMMU_PHYS_ADDR_MASK) == raw_addr) by (bit_vector)
            requires
                raw_addr % 4096 == 0,
                raw_addr < 0x1_0000_0000_0000u64;
        assert(raw_addr & 0xfff == 0) by (bit_vector)
            requires raw_addr % 4096 == 0;
        assert(0 < raw_level < 8);
        assert(encoded_level & AMD_IOMMU_NEXT_LEVEL_MASK == encoded_level) by (bit_vector)
            requires
                raw_level < 8,
                encoded_level == raw_level << 9;
        assert(encoded_level != 0) by (bit_vector)
            requires
                raw_level != 0,
                raw_level < 8,
                encoded_level == raw_level << 9;
        assert(value
            == (raw_addr & AMD_IOMMU_PHYS_ADDR_MASK)
                | AMD_IOMMU_VALID
                | AMD_IOMMU_IR
                | AMD_IOMMU_IW
                | encoded_level);
        assert(value == raw_addr | flags) by (bit_vector)
            requires
                value
                    == (raw_addr & AMD_IOMMU_PHYS_ADDR_MASK)
                        | AMD_IOMMU_VALID
                        | AMD_IOMMU_IR
                        | AMD_IOMMU_IW
                        | encoded_level,
                raw_addr & AMD_IOMMU_PHYS_ADDR_MASK == raw_addr,
                flags == AMD_IOMMU_VALID | AMD_IOMMU_IR | AMD_IOMMU_IW | encoded_level;
        assert(value & AMD_IOMMU_PHYS_ADDR_MASK == raw_addr) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr & AMD_IOMMU_PHYS_ADDR_MASK == raw_addr,
                raw_addr & 0xfff == 0,
                flags == AMD_IOMMU_VALID | AMD_IOMMU_IR | AMD_IOMMU_IW | encoded_level,
                encoded_level & AMD_IOMMU_NEXT_LEVEL_MASK == encoded_level;
        assert(pte.spec_addr() == addr);
        assert(value & AMD_IOMMU_VALID == AMD_IOMMU_VALID) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr & 0xfff == 0,
                flags == AMD_IOMMU_VALID | AMD_IOMMU_IR | AMD_IOMMU_IW | encoded_level;
        assert(AMD_IOMMU_VALID != 0) by (bit_vector);
        assert(pte.spec_valid());
        assert(value & AMD_IOMMU_NEXT_LEVEL_MASK == encoded_level) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr & 0xfff == 0,
                flags == AMD_IOMMU_VALID | AMD_IOMMU_IR | AMD_IOMMU_IW | encoded_level,
                encoded_level & AMD_IOMMU_NEXT_LEVEL_MASK == encoded_level;
        assert(!pte.spec_huge());
    }

    proof fn lemma_empty_invalid() {
        assert(0u64 & AMD_IOMMU_VALID == 0) by (bit_vector);
    }

    proof fn lemma_from_0_invalid() {
        assert(0u64 & AMD_IOMMU_VALID == 0) by (bit_vector);
    }

    proof fn lemma_eq_by_u64(pte1: Self, pte2: Self) {
        assert(pte1.value == pte2.value);
    }

    proof fn lemma_from_to_u64_inverse(val: u64) {
    }
}

} // verus!
