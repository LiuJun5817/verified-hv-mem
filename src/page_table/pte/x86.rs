//! Intel x86 Extended Page Table (EPT) entry.
use super::PageTableEntry;
use crate::address::{
    addr::{PAddr, SpecPAddr},
    frame::MemAttr,
};
use vstd::prelude::*;

verus! {

// Low fields of an Intel EPT entry:
//
// | Bits | Field       | Encoding used here                                  |
// |------|-------------|-----------------------------------------------------|
// | 7    | large page  | Set for a 2 MiB/1 GiB mapping                       |
// | 5:3  | memory type | 0b110 for Normal (WB), 0b100 for Device (WT) memory |
// | 2    | execute     | Execute permission                                  |
// | 1    | write       | Write permission                                    |
// | 0    | read        | Read permission                                     |
//
// Bits 51:12 carry the host physical address.  The generic page-table
// interface also permits a valid mapping with no access permissions.  Such an
// entry is tracked as occupied by its non-zero memory-type field even though an
// EPT walk cannot use it until at least one of R/W/X is enabled.

/// EPT read permission.
pub const EPT_R: u64 = 1 << 0;

/// EPT write permission.
pub const EPT_W: u64 = 1 << 1;

/// EPT execute permission.
pub const EPT_X: u64 = 1 << 2;

/// EPT memory-type field.
pub const EPT_MEM_TYPE_MASK: u64 = 0b111 << 3;

/// Write-through memory, used for device mappings by hvisor.
pub const EPT_DEVICE_ATTR: u64 = 0b100 << 3;

/// Write-back memory, used for normal RAM mappings.
pub const EPT_NORMAL_ATTR: u64 = 0b110 << 3;

/// Large-page bit in an EPT PDPTE/PDE.
pub const EPT_HUGE: u64 = 1 << 7;

/// Fields which make an entry occupied in the software page-table model.
pub const EPT_VALID_MASK: u64 = EPT_R | EPT_W | EPT_X | EPT_MEM_TYPE_MASK;

/// Physical-address bits supported by an EPT entry (bits 51:12).
pub const EPT_PHYS_ADDR_MASK: u64 = 0x000f_ffff_ffff_f000;

/// An Intel Extended Page Table entry.
///
/// Keeping the raw value makes parsing and serialization exact inverses.
#[derive(Clone, Copy)]
pub struct X86PTE {
    pub value: u64,
}

impl X86PTE {
    /// Encode the EPT flags used by the hvisor x86 stage-2 implementation.
    pub open spec fn spec_descriptor_flags(attr: MemAttr, huge: bool) -> u64 {
        let mem_type = if attr.device {
            EPT_DEVICE_ATTR
        } else {
            EPT_NORMAL_ATTR
        };
        let readable = if attr.readable {
            EPT_R
        } else {
            0
        };
        let writable = if attr.writable {
            EPT_W
        } else {
            0
        };
        let executable = if attr.executable {
            EPT_X
        } else {
            0
        };
        let large_page = if huge {
            EPT_HUGE
        } else {
            0
        };
        mem_type | readable | writable | executable | large_page
    }

    fn descriptor_flags(attr: MemAttr, huge: bool) -> (res: u64)
        ensures
            res == Self::spec_descriptor_flags(attr, huge),
    {
        let mem_type = if attr.device {
            EPT_DEVICE_ATTR
        } else {
            EPT_NORMAL_ATTR
        };
        let readable = if attr.readable {
            EPT_R
        } else {
            0
        };
        let writable = if attr.writable {
            EPT_W
        } else {
            0
        };
        let executable = if attr.executable {
            EPT_X
        } else {
            0
        };
        let large_page = if huge {
            EPT_HUGE
        } else {
            0
        };
        mem_type | readable | writable | executable | large_page
    }
}

impl PageTableEntry for X86PTE {
    open spec fn wf(self) -> bool {
        true
    }

    open spec fn spec_new(addr: SpecPAddr, attr: MemAttr, huge: bool) -> Self {
        Self {
            value: ((addr.0 as u64) & EPT_PHYS_ADDR_MASK)
                | Self::spec_descriptor_flags(attr, huge),
        }
    }

    open spec fn spec_new_table(addr: SpecPAddr) -> Self {
        Self {
            value: ((addr.0 as u64) & EPT_PHYS_ADDR_MASK) | EPT_R | EPT_W | EPT_X,
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
        SpecPAddr((self.value & EPT_PHYS_ADDR_MASK) as nat)
    }

    open spec fn spec_attr(self) -> MemAttr {
        MemAttr {
            readable: self.value & EPT_R != 0,
            writable: self.value & EPT_W != 0,
            executable: self.value & EPT_X != 0,
            device: self.value & EPT_MEM_TYPE_MASK == EPT_DEVICE_ATTR,
        }
    }

    open spec fn spec_valid(self) -> bool {
        self.value & EPT_VALID_MASK != 0
    }

    open spec fn spec_huge(self) -> bool {
        self.value & EPT_HUGE != 0
    }

    fn new(addr: PAddr, attr: MemAttr, huge: bool) -> (pte: Self) {
        let flags = Self::descriptor_flags(attr, huge);
        let value = ((addr.0 as u64) & EPT_PHYS_ADDR_MASK) | flags;
        Self { value }
    }

    fn new_table(addr: PAddr) -> (pte: Self) {
        let value = ((addr.0 as u64) & EPT_PHYS_ADDR_MASK) | EPT_R | EPT_W | EPT_X;
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
        PAddr((self.value & EPT_PHYS_ADDR_MASK) as usize)
    }

    fn attr(&self) -> (res: MemAttr) {
        MemAttr {
            readable: self.value & EPT_R != 0,
            writable: self.value & EPT_W != 0,
            executable: self.value & EPT_X != 0,
            device: self.value & EPT_MEM_TYPE_MASK == EPT_DEVICE_ATTR,
        }
    }

    fn huge(&self) -> (res: bool) {
        self.value & EPT_HUGE != 0
    }

    fn valid(&self) -> (res: bool) {
        self.value & EPT_VALID_MASK != 0
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
        let mem_type = if attr.device {
            EPT_DEVICE_ATTR
        } else {
            EPT_NORMAL_ATTR
        };
        let readable = if attr.readable {
            EPT_R
        } else {
            0
        };
        let writable = if attr.writable {
            EPT_W
        } else {
            0
        };
        let executable = if attr.executable {
            EPT_X
        } else {
            0
        };
        let large_page = if huge {
            EPT_HUGE
        } else {
            0
        };

        assert(raw_addr % 4096 == 0);
        assert(raw_addr < 0x1_0000_0000_0000u64);
        assert(flags == mem_type | readable | writable | executable | large_page);
        assert(value == (raw_addr & EPT_PHYS_ADDR_MASK) | flags);
        assert(mem_type == EPT_DEVICE_ATTR || mem_type == EPT_NORMAL_ATTR);
        assert(readable == 0 || readable == EPT_R);
        assert(writable == 0 || writable == EPT_W);
        assert(executable == 0 || executable == EPT_X);
        assert(large_page == 0 || large_page == EPT_HUGE);

        assert((raw_addr & EPT_PHYS_ADDR_MASK) == raw_addr) by (bit_vector)
            requires
                raw_addr % 4096 == 0,
                raw_addr < 0x1_0000_0000_0000u64,
        ;
        assert(raw_addr & 0xfff == 0) by (bit_vector)
            requires
                raw_addr % 4096 == 0,
        ;
        assert(flags & EPT_PHYS_ADDR_MASK == 0) by (bit_vector)
            requires
                flags == mem_type | readable | writable | executable | large_page,
                mem_type == EPT_DEVICE_ATTR || mem_type == EPT_NORMAL_ATTR,
                readable == 0 || readable == EPT_R,
                writable == 0 || writable == EPT_W,
                executable == 0 || executable == EPT_X,
                large_page == 0 || large_page == EPT_HUGE,
        ;
        assert(flags & EPT_R == readable) by (bit_vector)
            requires
                flags == mem_type | readable | writable | executable | large_page,
                mem_type == EPT_DEVICE_ATTR || mem_type == EPT_NORMAL_ATTR,
                readable == 0 || readable == EPT_R,
                writable == 0 || writable == EPT_W,
                executable == 0 || executable == EPT_X,
                large_page == 0 || large_page == EPT_HUGE,
        ;
        assert(flags & EPT_W == writable) by (bit_vector)
            requires
                flags == mem_type | readable | writable | executable | large_page,
                mem_type == EPT_DEVICE_ATTR || mem_type == EPT_NORMAL_ATTR,
                readable == 0 || readable == EPT_R,
                writable == 0 || writable == EPT_W,
                executable == 0 || executable == EPT_X,
                large_page == 0 || large_page == EPT_HUGE,
        ;
        assert(flags & EPT_X == executable) by (bit_vector)
            requires
                flags == mem_type | readable | writable | executable | large_page,
                mem_type == EPT_DEVICE_ATTR || mem_type == EPT_NORMAL_ATTR,
                readable == 0 || readable == EPT_R,
                writable == 0 || writable == EPT_W,
                executable == 0 || executable == EPT_X,
                large_page == 0 || large_page == EPT_HUGE,
        ;
        assert(flags & EPT_HUGE == large_page) by (bit_vector)
            requires
                flags == mem_type | readable | writable | executable | large_page,
                mem_type == EPT_DEVICE_ATTR || mem_type == EPT_NORMAL_ATTR,
                readable == 0 || readable == EPT_R,
                writable == 0 || writable == EPT_W,
                executable == 0 || executable == EPT_X,
                large_page == 0 || large_page == EPT_HUGE,
        ;
        assert(flags & EPT_MEM_TYPE_MASK == mem_type) by (bit_vector)
            requires
                flags == mem_type | readable | writable | executable | large_page,
                mem_type == EPT_DEVICE_ATTR || mem_type == EPT_NORMAL_ATTR,
                readable == 0 || readable == EPT_R,
                writable == 0 || writable == EPT_W,
                executable == 0 || executable == EPT_X,
                large_page == 0 || large_page == EPT_HUGE,
        ;
        assert(flags & EPT_VALID_MASK != 0) by (bit_vector)
            requires
                flags == mem_type | readable | writable | executable | large_page,
                mem_type == EPT_DEVICE_ATTR || mem_type == EPT_NORMAL_ATTR,
                readable == 0 || readable == EPT_R,
                writable == 0 || writable == EPT_W,
                executable == 0 || executable == EPT_X,
                large_page == 0 || large_page == EPT_HUGE,
        ;

        assert(value & EPT_PHYS_ADDR_MASK == raw_addr) by (bit_vector)
            requires
                value == (raw_addr & EPT_PHYS_ADDR_MASK) | flags,
                raw_addr & EPT_PHYS_ADDR_MASK == raw_addr,
                flags & EPT_PHYS_ADDR_MASK == 0,
        ;
        assert((value & EPT_PHYS_ADDR_MASK) as nat == addr.0);
        assert(pte.spec_addr() == addr);

        assert(value & EPT_VALID_MASK == flags & EPT_VALID_MASK) by (bit_vector)
            requires
                value == (raw_addr & EPT_PHYS_ADDR_MASK) | flags,
                raw_addr & 0xfff == 0,
        ;
        assert(pte.spec_valid());

        assert(value & EPT_HUGE == large_page) by (bit_vector)
            requires
                value == (raw_addr & EPT_PHYS_ADDR_MASK) | flags,
                raw_addr & 0xfff == 0,
                flags & EPT_HUGE == large_page,
        ;
        if huge {
            assert(large_page == EPT_HUGE);
            assert(EPT_HUGE != 0) by (bit_vector);
            assert(pte.spec_huge());
        } else {
            assert(large_page == 0);
            assert(!pte.spec_huge());
        }

        assert(value & EPT_R == readable) by (bit_vector)
            requires
                value == (raw_addr & EPT_PHYS_ADDR_MASK) | flags,
                raw_addr & 0xfff == 0,
                flags & EPT_R == readable,
        ;
        if attr.readable {
            assert(readable == EPT_R);
            assert(EPT_R != 0) by (bit_vector);
        } else {
            assert(readable == 0);
        }
        assert(value & EPT_W == writable) by (bit_vector)
            requires
                value == (raw_addr & EPT_PHYS_ADDR_MASK) | flags,
                raw_addr & 0xfff == 0,
                flags & EPT_W == writable,
        ;
        if attr.writable {
            assert(writable == EPT_W);
            assert(EPT_W != 0) by (bit_vector);
        } else {
            assert(writable == 0);
        }
        assert(value & EPT_X == executable) by (bit_vector)
            requires
                value == (raw_addr & EPT_PHYS_ADDR_MASK) | flags,
                raw_addr & 0xfff == 0,
                flags & EPT_X == executable,
        ;
        if attr.executable {
            assert(executable == EPT_X);
            assert(EPT_X != 0) by (bit_vector);
        } else {
            assert(executable == 0);
        }
        assert(value & EPT_MEM_TYPE_MASK == mem_type) by (bit_vector)
            requires
                value == (raw_addr & EPT_PHYS_ADDR_MASK) | flags,
                raw_addr & 0xfff == 0,
                flags & EPT_MEM_TYPE_MASK == mem_type,
        ;
        if attr.device {
            assert(mem_type == EPT_DEVICE_ATTR);
        } else {
            assert(mem_type == EPT_NORMAL_ATTR);
            assert(EPT_NORMAL_ATTR != EPT_DEVICE_ATTR) by (bit_vector);
        }
        assert(pte.spec_attr().readable == attr.readable);
        assert(pte.spec_attr().writable == attr.writable);
        assert(pte.spec_attr().executable == attr.executable);
        assert(pte.spec_attr().device == attr.device);
        assert(pte.spec_attr() == attr);
    }

    proof fn lemma_new_table_keeps_value(addr: SpecPAddr) {
        let pte = Self::spec_new_table(addr);
        let raw_addr = addr.0 as u64;
        let flags = EPT_R | EPT_W | EPT_X;
        let value = pte.value;

        assert(raw_addr % 4096 == 0);
        assert(raw_addr < 0x1_0000_0000_0000u64);
        assert((raw_addr & EPT_PHYS_ADDR_MASK) == raw_addr) by (bit_vector)
            requires
                raw_addr % 4096 == 0,
                raw_addr < 0x1_0000_0000_0000u64,
        ;
        assert(raw_addr & 0xfff == 0) by (bit_vector)
            requires
                raw_addr % 4096 == 0,
        ;
        assert(value == (raw_addr & EPT_PHYS_ADDR_MASK) | EPT_R | EPT_W | EPT_X);
        assert(value == (raw_addr & EPT_PHYS_ADDR_MASK) | flags) by (bit_vector)
            requires
                value == (raw_addr & EPT_PHYS_ADDR_MASK) | EPT_R | EPT_W | EPT_X,
                flags == EPT_R | EPT_W | EPT_X,
        ;
        assert(value == raw_addr | flags) by (bit_vector)
            requires
                value == (raw_addr & EPT_PHYS_ADDR_MASK) | flags,
                raw_addr & EPT_PHYS_ADDR_MASK == raw_addr,
        ;
        assert(value & EPT_PHYS_ADDR_MASK == raw_addr) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr & EPT_PHYS_ADDR_MASK == raw_addr,
                raw_addr & 0xfff == 0,
                flags == EPT_R | EPT_W | EPT_X,
        ;
        assert((value & EPT_PHYS_ADDR_MASK) as nat == addr.0);
        assert(pte.spec_addr() == addr);
        assert(value & EPT_VALID_MASK != 0) by (bit_vector)
            requires
                value == raw_addr | flags,
                flags == EPT_R | EPT_W | EPT_X,
        ;
        assert(pte.spec_valid());
        assert(value & EPT_HUGE == 0) by (bit_vector)
            requires
                value == raw_addr | flags,
                raw_addr & 0xfff == 0,
                flags == EPT_R | EPT_W | EPT_X,
        ;
        assert(!pte.spec_huge());
    }

    proof fn lemma_empty_invalid() {
        assert(0u64 & EPT_VALID_MASK == 0) by (bit_vector);
    }

    proof fn lemma_from_0_invalid() {
        assert(0u64 & EPT_VALID_MASK == 0) by (bit_vector);
    }

    proof fn lemma_eq_by_u64(pte1: Self, pte2: Self) {
        assert(pte1.value == pte2.value);
    }

    proof fn lemma_from_to_u64_inverse(val: u64) {
    }
}

} // verus!
