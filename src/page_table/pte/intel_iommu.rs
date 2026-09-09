//! Intel VT-d second-level page-table entry.
use super::PageTableEntry;
use crate::address::{
    addr::{PAddr, SpecPAddr},
    frame::MemAttr,
};
use vstd::prelude::*;

verus! {

// Fields used by an Intel VT-d second-level entry:
//
// | Bits  | Field            | Encoding used here                        |
// |-------|------------------|-------------------------------------------|
// | 51:12 | physical address | Host physical frame or next-level table   |
// | 7     | large page       | Set for a 2 MiB/1 GiB mapping             |
// | 1     | write            | DMA write permission                      |
// | 0     | read             | DMA read permission and present indicator |

/// DMA read permission. This backend treats the bit as the present marker.
pub const VTD_R: u64 = 1 << 0;
/// DMA write permission.
pub const VTD_W: u64 = 1 << 1;
/// Large-page marker for a second-level PDE or PDPTE.
pub const VTD_HUGE: u64 = 1 << 7;
/// Physical-address bits used by the VT-d implementation.
pub const VTD_PHYS_ADDR_MASK: u64 = 0x000f_ffff_ffff_f000;

/// Intel VT-d second-level translation entry.
#[derive(Clone, Copy)]
pub struct IntelVtdPTE {
    pub value: u64,
}

impl IntelVtdPTE {
    pub open spec fn spec_descriptor_flags(attr: MemAttr, huge: bool) -> u64 {
        let readable = if attr.readable { VTD_R } else { 0 };
        let writable = if attr.writable { VTD_W } else { 0 };
        let large_page = if huge { VTD_HUGE } else { 0 };
        readable | writable | large_page
    }

    fn descriptor_flags(attr: MemAttr, huge: bool) -> (res: u64)
        ensures
            res == Self::spec_descriptor_flags(attr, huge),
    {
        let readable = if attr.readable { VTD_R } else { 0 };
        let writable = if attr.writable { VTD_W } else { 0 };
        let large_page = if huge { VTD_HUGE } else { 0 };
        readable | writable | large_page
    }
}

impl PageTableEntry for IntelVtdPTE {
    open spec fn wf(self) -> bool {
        true
    }

    open spec fn spec_supports_attr(attr: MemAttr) -> bool {
        attr.readable && !attr.executable && !attr.device
    }

    open spec fn spec_new(addr: SpecPAddr, attr: MemAttr, huge: bool) -> Self {
        Self {
            value: ((addr.0 as u64) & VTD_PHYS_ADDR_MASK)
                | Self::spec_descriptor_flags(attr, huge),
        }
    }

    open spec fn spec_new_table(addr: SpecPAddr, _next_level: nat) -> Self {
        Self { value: ((addr.0 as u64) & VTD_PHYS_ADDR_MASK) | VTD_R | VTD_W }
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
        SpecPAddr((self.value & VTD_PHYS_ADDR_MASK) as nat)
    }

    open spec fn spec_attr(self) -> MemAttr {
        MemAttr {
            readable: self.value & VTD_R != 0,
            writable: self.value & VTD_W != 0,
            executable: false,
            device: false,
        }
    }

    open spec fn spec_valid(self) -> bool {
        self.value & VTD_R != 0
    }

    open spec fn spec_huge(self) -> bool {
        self.value & VTD_HUGE != 0
    }

    fn new(addr: PAddr, attr: MemAttr, huge: bool) -> (pte: Self) {
        let flags = Self::descriptor_flags(attr, huge);
        Self { value: ((addr.0 as u64) & VTD_PHYS_ADDR_MASK) | flags }
    }

    fn new_table(addr: PAddr, _next_level: usize) -> (pte: Self) {
        Self { value: ((addr.0 as u64) & VTD_PHYS_ADDR_MASK) | VTD_R | VTD_W }
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
        PAddr((self.value & VTD_PHYS_ADDR_MASK) as usize)
    }

    fn attr(&self) -> (res: MemAttr) {
        MemAttr {
            readable: self.value & VTD_R != 0,
            writable: self.value & VTD_W != 0,
            executable: false,
            device: false,
        }
    }

    fn valid(&self) -> (res: bool) {
        self.value & VTD_R != 0
    }

    fn huge(&self) -> (res: bool) {
        self.value & VTD_HUGE != 0
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
        let readable = if attr.readable { VTD_R } else { 0 };
        let writable = if attr.writable { VTD_W } else { 0 };
        let large_page = if huge { VTD_HUGE } else { 0 };
        let flags = readable | writable | large_page;
        let value = pte.value;

        assert(raw_addr % 4096 == 0);
        assert(raw_addr < 0x1_0000_0000_0000u64);
        assert((raw_addr & VTD_PHYS_ADDR_MASK) == raw_addr) by (bit_vector)
            requires
                raw_addr % 4096 == 0,
                raw_addr < 0x1_0000_0000_0000u64;
        assert(raw_addr & 0xfff == 0) by (bit_vector)
            requires raw_addr % 4096 == 0;
        assert(value == raw_addr | flags);
        assert(value & VTD_PHYS_ADDR_MASK == raw_addr) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr & VTD_PHYS_ADDR_MASK == raw_addr,
                raw_addr & 0xfff == 0,
                flags == readable | writable | large_page,
                readable == 0 || readable == VTD_R,
                writable == 0 || writable == VTD_W,
                large_page == 0 || large_page == VTD_HUGE;
        assert(pte.spec_addr() == addr);

        assert(value & VTD_R == readable) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr & 0xfff == 0,
                flags == readable | writable | large_page,
                readable == 0 || readable == VTD_R,
                writable == 0 || writable == VTD_W,
                large_page == 0 || large_page == VTD_HUGE;
        assert(readable == VTD_R);
        assert(VTD_R != 0) by (bit_vector);
        assert(pte.spec_valid());

        assert(value & VTD_W == writable) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr & 0xfff == 0,
                flags == readable | writable | large_page,
                readable == 0 || readable == VTD_R,
                writable == 0 || writable == VTD_W,
                large_page == 0 || large_page == VTD_HUGE;
        if attr.writable {
            assert(writable == VTD_W);
            assert(VTD_W != 0) by (bit_vector);
        } else {
            assert(writable == 0);
        }
        assert(value & VTD_HUGE == large_page) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr & 0xfff == 0,
                flags == readable | writable | large_page,
                readable == 0 || readable == VTD_R,
                writable == 0 || writable == VTD_W,
                large_page == 0 || large_page == VTD_HUGE;
        if huge {
            assert(large_page == VTD_HUGE);
            assert(VTD_HUGE != 0) by (bit_vector);
            assert(pte.spec_huge());
        }
        assert(pte.spec_attr().readable == attr.readable);
        assert(pte.spec_attr().writable == attr.writable);
        assert(pte.spec_attr().executable == attr.executable);
        assert(pte.spec_attr().device == attr.device);
        assert(pte.spec_attr() == attr);
    }

    proof fn lemma_new_table_keeps_value(addr: SpecPAddr, next_level: nat) {
        let pte = Self::spec_new_table(addr, next_level);
        let raw_addr = addr.0 as u64;
        let flags = VTD_R | VTD_W;
        let value = pte.value;

        assert(raw_addr % 4096 == 0);
        assert(raw_addr < 0x1_0000_0000_0000u64);
        assert((raw_addr & VTD_PHYS_ADDR_MASK) == raw_addr) by (bit_vector)
            requires
                raw_addr % 4096 == 0,
                raw_addr < 0x1_0000_0000_0000u64;
        assert(raw_addr & 0xfff == 0) by (bit_vector)
            requires raw_addr % 4096 == 0;
        assert(value == (raw_addr & VTD_PHYS_ADDR_MASK) | VTD_R | VTD_W);
        assert(value == raw_addr | flags) by (bit_vector)
            requires
                value == (raw_addr & VTD_PHYS_ADDR_MASK) | VTD_R | VTD_W,
                raw_addr & VTD_PHYS_ADDR_MASK == raw_addr,
                flags == VTD_R | VTD_W;
        assert(value & VTD_PHYS_ADDR_MASK == raw_addr) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr & VTD_PHYS_ADDR_MASK == raw_addr,
                raw_addr & 0xfff == 0,
                flags == VTD_R | VTD_W;
        assert(pte.spec_addr() == addr);
        assert(value & VTD_R == VTD_R) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr & 0xfff == 0,
                flags == VTD_R | VTD_W;
        assert(VTD_R != 0) by (bit_vector);
        assert(pte.spec_valid());
        assert(value & VTD_HUGE == 0) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr & 0xfff == 0,
                flags == VTD_R | VTD_W;
        assert(!pte.spec_huge());
    }

    proof fn lemma_empty_invalid() {
        assert(0u64 & VTD_R == 0) by (bit_vector);
    }

    proof fn lemma_from_0_invalid() {
        assert(0u64 & VTD_R == 0) by (bit_vector);
    }

    proof fn lemma_eq_by_u64(pte1: Self, pte2: Self) {
        assert(pte1.value == pte2.value);
    }

    proof fn lemma_from_to_u64_inverse(val: u64) {
    }
}

} // verus!
