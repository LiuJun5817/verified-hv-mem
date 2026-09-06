//! AMD x86 Nested Page Table (NPT) entry.
use super::PageTableEntry;
use crate::address::{
    addr::{PAddr, SpecPAddr},
    frame::MemAttr,
};
use vstd::prelude::*;

verus! {

// Fields of an AMD NPT entry:
//
// | Bits  | Field            | Encoding used here                              |
// |-------|------------------|-------------------------------------------------|
// | 63    | execute disable  | Set when the mapping is not executable          |
// | 51:12 | physical address | Host address, including the optional SME C-bit  |
// | 7     | large page       | Set for a 2 MiB/1 GiB mapping                   |
// | 4     | cache disable    | Set for device memory                           |
// | 3     | write through    | Set for device memory                           |
// | 2     | user             | Set for every constructed leaf and table entry  |
// | 1     | write            | Write permission                                |
// | 0     | present          | Read/present permission                         |

/// Present/readable bit.
pub const NPT_PRESENT: u64 = 1 << 0;
/// Writable bit.
pub const NPT_WRITABLE: u64 = 1 << 1;
/// Guest page-table walks are always user accesses at the NPT level.
pub const NPT_USER: u64 = 1 << 2;
/// Write-through caching bit used for device mappings.
pub const NPT_PWT: u64 = 1 << 3;
/// Cache-disable bit used for device mappings.
pub const NPT_PCD: u64 = 1 << 4;
/// Large-page bit in an NPT PDPTE/PDE.
pub const NPT_HUGE: u64 = 1 << 7;
/// Execute-disable bit.
pub const NPT_NX: u64 = 1 << 63;
/// Physical-address bits, including HyperEnclave's possible SME C-bit.
pub const NPT_PHYS_ADDR_MASK: u64 = 0x000f_ffff_ffff_f000;
/// Fields which make an entry occupied in the software page-table model.
pub const NPT_VALID_MASK: u64 =
    NPT_PRESENT | NPT_WRITABLE | NPT_USER | NPT_PWT | NPT_PCD | NPT_HUGE | NPT_NX;

/// An AMD nested-page-table entry.
///
/// `NPT_USER` is set on every constructed leaf because AMD treats the guest
/// page-table walk as a user access at the nested level. Non-present entries
/// remain occupied in the software model through their attribute bits.
#[derive(Clone, Copy)]
pub struct AmdNptPTE {
    pub value: u64,
}

impl AmdNptPTE {
    pub open spec fn spec_descriptor_flags(attr: MemAttr, huge: bool) -> u64 {
        let present = if attr.readable { NPT_PRESENT } else { 0 };
        let writable = if attr.writable { NPT_WRITABLE } else { 0 };
        let device = if attr.device { NPT_PWT | NPT_PCD } else { 0 };
        let execute_never = if attr.executable { 0 } else { NPT_NX };
        let large_page = if huge { NPT_HUGE } else { 0 };
        present | writable | NPT_USER | device | execute_never | large_page
    }

    fn descriptor_flags(attr: MemAttr, huge: bool) -> (res: u64)
        ensures
            res == Self::spec_descriptor_flags(attr, huge),
    {
        let present = if attr.readable { NPT_PRESENT } else { 0 };
        let writable = if attr.writable { NPT_WRITABLE } else { 0 };
        let device = if attr.device { NPT_PWT | NPT_PCD } else { 0 };
        let execute_never = if attr.executable { 0 } else { NPT_NX };
        let large_page = if huge { NPT_HUGE } else { 0 };
        present | writable | NPT_USER | device | execute_never | large_page
    }
}

impl PageTableEntry for AmdNptPTE {
    open spec fn wf(self) -> bool {
        true
    }

    open spec fn spec_new(addr: SpecPAddr, attr: MemAttr, huge: bool) -> Self {
        Self {
            value: ((addr.0 as u64) & NPT_PHYS_ADDR_MASK)
                | Self::spec_descriptor_flags(attr, huge),
        }
    }

    open spec fn spec_new_table(addr: SpecPAddr) -> Self {
        Self {
            value: ((addr.0 as u64) & NPT_PHYS_ADDR_MASK)
                | NPT_PRESENT
                | NPT_WRITABLE
                | NPT_USER,
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
        SpecPAddr((self.value & NPT_PHYS_ADDR_MASK) as nat)
    }

    open spec fn spec_attr(self) -> MemAttr {
        MemAttr {
            readable: self.value & NPT_PRESENT != 0,
            writable: self.value & NPT_WRITABLE != 0,
            executable: self.value & NPT_NX == 0,
            device: self.value & NPT_PCD != 0,
        }
    }

    open spec fn spec_valid(self) -> bool {
        self.value & NPT_VALID_MASK != 0
    }

    open spec fn spec_huge(self) -> bool {
        self.value & NPT_HUGE != 0
    }

    fn new(addr: PAddr, attr: MemAttr, huge: bool) -> (pte: Self) {
        let flags = Self::descriptor_flags(attr, huge);
        Self { value: ((addr.0 as u64) & NPT_PHYS_ADDR_MASK) | flags }
    }

    fn new_table(addr: PAddr) -> (pte: Self) {
        Self {
            value: ((addr.0 as u64) & NPT_PHYS_ADDR_MASK)
                | NPT_PRESENT
                | NPT_WRITABLE
                | NPT_USER,
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
        PAddr((self.value & NPT_PHYS_ADDR_MASK) as usize)
    }

    fn attr(&self) -> (res: MemAttr) {
        MemAttr {
            readable: self.value & NPT_PRESENT != 0,
            writable: self.value & NPT_WRITABLE != 0,
            executable: self.value & NPT_NX == 0,
            device: self.value & NPT_PCD != 0,
        }
    }

    fn huge(&self) -> (res: bool) {
        self.value & NPT_HUGE != 0
    }

    fn valid(&self) -> (res: bool) {
        self.value & NPT_VALID_MASK != 0
    }

    proof fn lemma_new_wf(addr: SpecPAddr, attr: MemAttr, huge: bool) {
    }

    proof fn lemma_new_table_wf(addr: SpecPAddr) {
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
        let present = if attr.readable { NPT_PRESENT } else { 0 };
        let writable = if attr.writable { NPT_WRITABLE } else { 0 };
        let device = if attr.device { NPT_PWT | NPT_PCD } else { 0 };
        let execute_never = if attr.executable { 0 } else { NPT_NX };
        let large_page = if huge { NPT_HUGE } else { 0 };

        assert(raw_addr % 4096 == 0);
        assert(raw_addr < 0x1_0000_0000_0000u64);
        assert(flags
            == present | writable | NPT_USER | device | execute_never | large_page);
        assert(value == (raw_addr & NPT_PHYS_ADDR_MASK) | flags);
        assert((raw_addr & NPT_PHYS_ADDR_MASK) == raw_addr) by (bit_vector)
            requires
                raw_addr % 4096 == 0,
                raw_addr < 0x1_0000_0000_0000u64,
        ;
        assert(raw_addr & 0xfff == 0) by (bit_vector)
            requires
                raw_addr % 4096 == 0,
        ;
        assert(value == raw_addr | flags) by (bit_vector)
            requires
                value == (raw_addr & NPT_PHYS_ADDR_MASK) | flags,
                raw_addr & NPT_PHYS_ADDR_MASK == raw_addr,
        ;
        assert(flags & NPT_PHYS_ADDR_MASK == 0) by (bit_vector)
            requires
                flags
                    == present | writable | NPT_USER | device | execute_never | large_page,
                present == 0 || present == NPT_PRESENT,
                writable == 0 || writable == NPT_WRITABLE,
                device == 0 || device == NPT_PWT | NPT_PCD,
                execute_never == 0 || execute_never == NPT_NX,
                large_page == 0 || large_page == NPT_HUGE,
        ;
        assert(value & NPT_PHYS_ADDR_MASK == raw_addr) by (bit_vector)
            requires
                value == (raw_addr & NPT_PHYS_ADDR_MASK) | flags,
                raw_addr & NPT_PHYS_ADDR_MASK == raw_addr,
                flags & NPT_PHYS_ADDR_MASK == 0,
        ;
        assert((value & NPT_PHYS_ADDR_MASK) as nat == addr.0);
        assert(pte.spec_addr() == addr);

        assert(value & NPT_VALID_MASK != 0) by (bit_vector)
            requires
                value == raw_addr | flags,
                flags
                    == present | writable | NPT_USER | device | execute_never | large_page,
        ;
        assert(pte.spec_valid());

        assert(value & NPT_PRESENT == present) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr & 0xfff == 0,
                flags
                    == present | writable | NPT_USER | device | execute_never | large_page,
                present == 0 || present == NPT_PRESENT,
                writable == 0 || writable == NPT_WRITABLE,
                device == 0 || device == NPT_PWT | NPT_PCD,
                execute_never == 0 || execute_never == NPT_NX,
                large_page == 0 || large_page == NPT_HUGE,
        ;
        assert(value & NPT_WRITABLE == writable) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr & 0xfff == 0,
                flags
                    == present | writable | NPT_USER | device | execute_never | large_page,
                present == 0 || present == NPT_PRESENT,
                writable == 0 || writable == NPT_WRITABLE,
                device == 0 || device == NPT_PWT | NPT_PCD,
                execute_never == 0 || execute_never == NPT_NX,
                large_page == 0 || large_page == NPT_HUGE,
        ;
        assert(value & NPT_PCD == (device & NPT_PCD)) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr & 0xfff == 0,
                flags
                    == present | writable | NPT_USER | device | execute_never | large_page,
                present == 0 || present == NPT_PRESENT,
                writable == 0 || writable == NPT_WRITABLE,
                device == 0 || device == NPT_PWT | NPT_PCD,
                execute_never == 0 || execute_never == NPT_NX,
                large_page == 0 || large_page == NPT_HUGE,
        ;
        assert(value & NPT_NX == execute_never) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr < 0x1_0000_0000_0000u64,
                flags
                    == present | writable | NPT_USER | device | execute_never | large_page,
                present == 0 || present == NPT_PRESENT,
                writable == 0 || writable == NPT_WRITABLE,
                device == 0 || device == NPT_PWT | NPT_PCD,
                execute_never == 0 || execute_never == NPT_NX,
                large_page == 0 || large_page == NPT_HUGE,
        ;
        assert(value & NPT_HUGE == large_page) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr & 0xfff == 0,
                flags
                    == present | writable | NPT_USER | device | execute_never | large_page,
                present == 0 || present == NPT_PRESENT,
                writable == 0 || writable == NPT_WRITABLE,
                device == 0 || device == NPT_PWT | NPT_PCD,
                execute_never == 0 || execute_never == NPT_NX,
                large_page == 0 || large_page == NPT_HUGE,
        ;

        if attr.readable {
            assert(present == NPT_PRESENT);
            assert(NPT_PRESENT != 0) by (bit_vector);
        } else {
            assert(present == 0);
        }
        assert(pte.spec_attr().readable == attr.readable);
        if attr.writable {
            assert(writable == NPT_WRITABLE);
            assert(NPT_WRITABLE != 0) by (bit_vector);
        } else {
            assert(writable == 0);
        }
        assert(pte.spec_attr().writable == attr.writable);
        if attr.executable {
            assert(execute_never == 0);
        } else {
            assert(execute_never == NPT_NX);
            assert(NPT_NX != 0) by (bit_vector);
        }
        assert(pte.spec_attr().executable == attr.executable);
        if attr.device {
            assert(device & NPT_PCD != 0) by (bit_vector)
                requires device == NPT_PWT | NPT_PCD,
            ;
        } else {
            assert(device == 0);
        }
        assert(pte.spec_attr().device == attr.device);
        if huge {
            assert(large_page == NPT_HUGE);
            assert(NPT_HUGE != 0) by (bit_vector);
        } else {
            assert(large_page == 0);
        }
        assert(pte.spec_huge() == huge);
        assert(pte.spec_attr() == attr);
    }

    proof fn lemma_new_table_keeps_value(addr: SpecPAddr) {
        let pte = Self::spec_new_table(addr);
        let raw_addr = addr.0 as u64;
        let flags = NPT_PRESENT | NPT_WRITABLE | NPT_USER;
        let value = pte.value;

        assert(raw_addr % 4096 == 0);
        assert(raw_addr < 0x1_0000_0000_0000u64);
        assert((raw_addr & NPT_PHYS_ADDR_MASK) == raw_addr) by (bit_vector)
            requires
                raw_addr % 4096 == 0,
                raw_addr < 0x1_0000_0000_0000u64,
        ;
        assert(raw_addr & 0xfff == 0) by (bit_vector)
            requires raw_addr % 4096 == 0,
        ;
        assert(value == raw_addr | flags) by (bit_vector)
            requires
                value
                    == (raw_addr & NPT_PHYS_ADDR_MASK)
                        | NPT_PRESENT
                        | NPT_WRITABLE
                        | NPT_USER,
                raw_addr & NPT_PHYS_ADDR_MASK == raw_addr,
                flags == NPT_PRESENT | NPT_WRITABLE | NPT_USER,
        ;
        assert(value & NPT_PHYS_ADDR_MASK == raw_addr) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr & NPT_PHYS_ADDR_MASK == raw_addr,
                raw_addr & 0xfff == 0,
                flags == NPT_PRESENT | NPT_WRITABLE | NPT_USER,
        ;
        assert((value & NPT_PHYS_ADDR_MASK) as nat == addr.0);
        assert(pte.spec_addr() == addr);
        assert(value & NPT_VALID_MASK != 0) by (bit_vector)
            requires
                value == raw_addr | flags,
                flags == NPT_PRESENT | NPT_WRITABLE | NPT_USER,
        ;
        assert(pte.spec_valid());
        assert(value & NPT_HUGE == 0) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr & 0xfff == 0,
                flags == NPT_PRESENT | NPT_WRITABLE | NPT_USER,
        ;
        assert(!pte.spec_huge());
    }

    proof fn lemma_empty_invalid() {
        assert(0u64 & NPT_VALID_MASK == 0) by (bit_vector);
    }

    proof fn lemma_from_0_invalid() {
        assert(0u64 & NPT_VALID_MASK == 0) by (bit_vector);
    }

    proof fn lemma_eq_by_u64(pte1: Self, pte2: Self) {
        assert(pte1.value == pte2.value);
    }

    proof fn lemma_from_to_u64_inverse(val: u64) {
    }
}

} // verus!
