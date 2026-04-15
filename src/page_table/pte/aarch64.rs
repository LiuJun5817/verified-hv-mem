//! Page table entry for Aarch64 architecture.
use super::PageTableEntry;
use crate::{
    address::{
        addr::{self, PAddr, SpecPAddr},
        frame::{FrameSize, MemAttr},
    },
    page_table::pt_arch::PTArch,
};
use vstd::prelude::*;

verus! {

/// macro: `if cond { a } else { b }`
macro_rules! ifelse {
    ($cond:expr, $a:expr, $b:expr) => {
        if $cond {
            $a
        } else {
            $b
        }
    };
}

/// macro: `( x & b1 == 0 && x & b2 == 0 && ... )`
#[allow(unused)]
macro_rules! and_eq_0 {
    ($x:expr, $($b:expr),*) => {
        ($($b & $x == 0)&&*)
    };
}

/// macro: `( x & b1 == 0 && x & b2 == 0 && ... )`
#[allow(unused)]
macro_rules! and_eq_0_commut {
    ($x:expr, $($b:expr),*) => {
        ($($x & $b == 0)&&*)
    };
}

/// Aarch64 page table entry.
///
/// Format: |addr: 63-12||padding: 11-7||attr: 6-2||huge: 1||valid: 0|
pub struct Aarch64PTE {
    pub addr: PAddr,
    pub attr: MemAttr,
    pub huge: bool,
    pub valid: bool,
    /// Reserved for future use.
    pub padding: u64,
}

impl PageTableEntry for Aarch64PTE {
    open spec fn wf(self) -> bool {
        &&& self.padding & 0b111110000000 == self.padding
        &&& self.addr@.aligned(FrameSize::Size4K.as_nat())
    }

    open spec fn spec_new(addr: SpecPAddr, attr: MemAttr, huge: bool) -> Self {
        Self { addr: PAddr(addr.0 as usize), attr, huge, valid: true, padding: 0 }
    }

    open spec fn spec_empty() -> Self {
        Self {
            addr: PAddr(0),
            attr: MemAttr::spec_default(),
            huge: false,
            valid: false,
            padding: 0,
        }
    }

    open spec fn spec_from_u64(val: u64) -> Self {
        let addr = PAddr((val & 0xFFFFFFFFFFFFF000) as usize);
        let readable = val & 0b100 != 0;
        let writable = val & 0b1000 != 0;
        let executable = val & 0b10000 != 0;
        let user_accessible = val & 0b100000 != 0;
        let device = val & 0b1000000 != 0;
        let huge = val & 0b10 != 0;
        let valid = val & 0b1 != 0;
        let padding = val & 0b111110000000;
        Self {
            addr,
            attr: MemAttr { readable, writable, executable, user_accessible, device },
            huge,
            valid,
            padding,
        }
    }

    open spec fn spec_to_u64(self) -> u64 {
        let a = self.addr.0 as u64;
        let b = ifelse!(self.attr.readable, 0b100, 0);
        let c = ifelse!(self.attr.writable, 0b1000, 0);
        let d = ifelse!(self.attr.executable, 0b10000, 0);
        let e = ifelse!(self.attr.user_accessible, 0b100000, 0);
        let f = ifelse!(self.attr.device, 0b1000000, 0);
        let g = ifelse!(self.huge, 0b10, 0);
        let h = ifelse!(self.valid, 0b1, 0);
        let i = self.padding;
        a | b | c | d | e | f | g | h | i
    }

    open spec fn spec_addr(self) -> SpecPAddr {
        self.addr@
    }

    open spec fn spec_attr(self) -> MemAttr {
        self.attr
    }

    open spec fn spec_valid(self) -> bool {
        self.valid
    }

    open spec fn spec_huge(self) -> bool {
        self.huge
    }

    fn new(addr: PAddr, attr: MemAttr, huge: bool) -> Self {
        assert(0 & 0b111110000000 == 0) by (bit_vector);
        Self { addr, attr, huge, valid: true, padding: 0 }
    }

    fn empty() -> Self {
        assert(0nat % FrameSize::Size4K.as_nat() == 0);
        assert(0 & 0b111110000000 == 0) by (bit_vector);
        Self { addr: PAddr(0), attr: MemAttr::default(), huge: false, valid: false, padding: 0 }
    }

    fn from_u64(val: u64) -> Self {
        let addr = PAddr((val & 0xFFFFFFFFFFFFF000) as usize);
        let readable = val & 0b100 != 0;
        let writable = val & 0b1000 != 0;
        let executable = val & 0b10000 != 0;
        let user_accessible = val & 0b100000 != 0;
        let device = val & 0b1000000 != 0;
        let huge = val & 0b10 != 0;
        let valid = val & 0b1 != 0;
        let padding = val & 0b111110000000;
        assert((val & 0xFFFFFFFFFFFFF000) % 4096 == 0) by (bit_vector);
        assert((val & 0b111110000000) & 0b111110000000 == val & 0b111110000000) by (bit_vector);

        Self {
            addr,
            attr: MemAttr { readable, writable, executable, user_accessible, device },
            huge,
            valid,
            padding,
        }
    }

    fn to_u64(&self) -> u64 {
        let a = self.addr.0 as u64;
        let b = ifelse!(self.attr.readable, 0b100, 0);
        let c = ifelse!(self.attr.writable, 0b1000, 0);
        let d = ifelse!(self.attr.executable, 0b10000, 0);
        let e = ifelse!(self.attr.user_accessible, 0b100000, 0);
        let f = ifelse!(self.attr.device, 0b1000000, 0);
        let g = ifelse!(self.huge, 0b10, 0);
        let h = ifelse!(self.valid, 0b1, 0);
        let i = self.padding;
        a | b | c | d | e | f | g | h | i
    }

    fn addr(&self) -> PAddr {
        self.addr
    }

    fn attr(&self) -> MemAttr {
        self.attr
    }

    fn huge(&self) -> bool {
        self.huge
    }

    fn valid(&self) -> bool {
        self.valid
    }

    proof fn lemma_empty_invalid() {
    }

    proof fn lemma_from_0_invalid() {
        assert(0 & 0b1 == 0) by (bit_vector);
    }

    proof fn lemma_from_to_u64_inverse(val: u64) {
        let pte = Self::spec_from_u64(val);
        Self::lemma_from_u64_wf(val);

        pte.lemma_fields_consistent_with_bits();
        pte.lemma_addr_consistent_with_bits();
        pte.lemma_padding_consistent_with_bits();
        lemma_and_eq_0_or_self(val);

        let u = pte.spec_to_u64();
        assert(u == val) by (bit_vector)
            requires
                u & 0b1 == val & 0b1,
                u & 0b10 == val & 0b10,
                u & 0b100 == val & 0b100,
                u & 0b1000 == val & 0b1000,
                u & 0b10000 == val & 0b10000,
                u & 0b100000 == val & 0b100000,
                u & 0b1000000 == val & 0b1000000,
                u & 0b111110000000 == val & 0b111110000000,
                u & 0xFFFFFFFFFFFFF000 == val & 0xFFFFFFFFFFFFF000,
        ;
    }

    proof fn lemma_new_wf(addr: SpecPAddr, attr: MemAttr, huge: bool) {
        assert(0 & 0b111110000000 == 0) by (bit_vector);
    }

    proof fn lemma_from_u64_wf(val: u64) {
        assert((val & 0xFFFFFFFFFFFFF000) % 4096 == 0) by (bit_vector);
        assert((val & 0b111110000000) & 0b111110000000 == val & 0b111110000000) by (bit_vector);
    }

    proof fn lemma_empty_wf() {
        assert(0nat % FrameSize::Size4K.as_nat() == 0);
        assert(0 & 0b111110000000 == 0) by (bit_vector);
    }

    proof fn lemma_new_keeps_value(addr: SpecPAddr, attr: MemAttr, huge: bool) {
    }

    proof fn lemma_eq_by_u64(pte1: Self, pte2: Self) {
        pte1.lemma_fields_consistent_with_bits();
        pte1.lemma_addr_consistent_with_bits();
        pte1.lemma_padding_consistent_with_bits();
        pte2.lemma_fields_consistent_with_bits();
        pte2.lemma_addr_consistent_with_bits();
        pte2.lemma_padding_consistent_with_bits();
    }
}

impl Aarch64PTE {
    /// Lemma. The fields in the PTE are consistent with the bits in the u64 representation.
    proof fn lemma_fields_consistent_with_bits(self)
        requires
            self.wf(),
        ensures
            ifelse!(self.attr.readable, self.spec_to_u64() & 0b100 == 0b100, self.spec_to_u64() & 0b100 == 0),
            ifelse!(self.attr.writable, self.spec_to_u64() & 0b1000 == 0b1000, self.spec_to_u64() & 0b1000 == 0),
            ifelse!(self.attr.executable, self.spec_to_u64() & 0b10000 == 0b10000, self.spec_to_u64() & 0b10000 == 0),
            ifelse!(self.attr.user_accessible, self.spec_to_u64() & 0b100000 == 0b100000, self.spec_to_u64() & 0b100000 == 0),
            ifelse!(self.attr.device, self.spec_to_u64() & 0b1000000 == 0b1000000, self.spec_to_u64() & 0b1000000 == 0),
            ifelse!(self.huge, self.spec_to_u64() & 0b10 == 0b10, self.spec_to_u64() & 0b10 == 0),
            ifelse!(self.valid, self.spec_to_u64() & 0b1 == 0b1, self.spec_to_u64() & 0b1 == 0),
    {
        let u = self.spec_to_u64();
        let a = self.addr.0 as u64;
        let b = ifelse!(self.attr.readable, 0b100, 0);
        let c = ifelse!(self.attr.writable, 0b1000, 0);
        let d = ifelse!(self.attr.executable, 0b10000, 0);
        let e = ifelse!(self.attr.user_accessible, 0b100000, 0);
        let f = ifelse!(self.attr.device, 0b1000000, 0);
        let g = ifelse!(self.huge, 0b10, 0);
        let h = ifelse!(self.valid, 0b1, 0);
        let i = self.padding;
        assert(u == a | b | c | d | e | f | g | h | i);

        assert(and_eq_0_commut!(a, 0b1, 0b10, 0b100, 0b1000, 0b10000, 0b100000, 0b1000000, 0b111110000000))
            by (bit_vector)
            requires
                a % 4096 == 0,
        ;
        assert(and_eq_0_commut!(i, 0b1, 0b10, 0b100, 0b1000, 0b10000, 0b100000, 0b1000000))
            by (bit_vector)
            requires
                i & 0b111110000000 == i,
        ;

        assert(and_eq_0!(0b1, 0, 0b10, 0b100, 0b1000, 0b10000, 0b100000, 0b1000000, 0b111110000000))
            by (bit_vector);
        assert(0b1 & 0b1 == 0b1) by (bit_vector);
        if self.valid {
            assert(u & 0b1 == 0b1) by (bit_vector)
                requires
                    h == 0b1,
                    u == a | b | c | d | e | f | g | h | i,
            ;
        } else {
            assert(u & 0b1 == 0) by (bit_vector)
                requires
                    h == 0,
                    a & 0b1 == 0,
                    b & 0b1 == 0,
                    c & 0b1 == 0,
                    d & 0b1 == 0,
                    e & 0b1 == 0,
                    f & 0b1 == 0,
                    g & 0b1 == 0,
                    h & 0b1 == 0,
                    i & 0b1 == 0,
                    u == a | b | c | d | e | f | g | h | i,
            ;
        }

        assert(and_eq_0!(0b10, 0, 0b1, 0b100, 0b1000, 0b10000, 0b100000, 0b1000000, 0b111110000000))
            by (bit_vector);
        assert(0b10 & 0b10 == 0b10) by (bit_vector);
        if self.huge {
            assert(u & 0b10 == 0b10) by (bit_vector)
                requires
                    g == 0b10,
                    u == a | b | c | d | e | f | g | h | i,
            ;
        } else {
            assert(u & 0b10 == 0) by (bit_vector)
                requires
                    g == 0,
                    a & 0b10 == 0,
                    b & 0b10 == 0,
                    c & 0b10 == 0,
                    d & 0b10 == 0,
                    e & 0b10 == 0,
                    f & 0b10 == 0,
                    g & 0b10 == 0,
                    h & 0b10 == 0,
                    i & 0b10 == 0,
                    u == a | b | c | d | e | f | g | h | i,
            ;
        }

        assert(and_eq_0!(0b100, 0, 0b1, 0b10, 0b1000, 0b10000, 0b100000, 0b1000000, 0b111110000000))
            by (bit_vector);
        assert(0b100 & 0b100 == 0b100) by (bit_vector);
        if self.attr.readable {
            assert(u & 0b100 == 0b100) by (bit_vector)
                requires
                    b == 0b100,
                    u == a | b | c | d | e | f | g | h | i,
            ;
        } else {
            assert(u & 0b100 == 0) by (bit_vector)
                requires
                    b == 0,
                    a & 0b100 == 0,
                    b & 0b100 == 0,
                    c & 0b100 == 0,
                    d & 0b100 == 0,
                    e & 0b100 == 0,
                    f & 0b100 == 0,
                    g & 0b100 == 0,
                    h & 0b100 == 0,
                    i & 0b100 == 0,
                    u == a | b | c | d | e | f | g | h | i,
            ;
        }

        assert(and_eq_0!(0b1000, 0, 0b1, 0b10, 0b100, 0b10000, 0b100000, 0b1000000, 0b111110000000))
            by (bit_vector);
        assert(0b1000 & 0b1000 == 0b1000) by (bit_vector);
        if self.attr.writable {
            assert(u & 0b1000 == 0b1000) by (bit_vector)
                requires
                    c == 0b1000,
                    u == a | b | c | d | e | f | g | h | i,
            ;
        } else {
            assert(u & 0b1000 == 0) by (bit_vector)
                requires
                    c == 0,
                    a & 0b1000 == 0,
                    b & 0b1000 == 0,
                    c & 0b1000 == 0,
                    d & 0b1000 == 0,
                    e & 0b1000 == 0,
                    f & 0b1000 == 0,
                    g & 0b1000 == 0,
                    h & 0b1000 == 0,
                    i & 0b1000 == 0,
                    u == a | b | c | d | e | f | g | h | i,
            ;
        }

        assert(and_eq_0!(0b10000, 0, 0b1, 0b10, 0b100, 0b1000, 0b100000, 0b1000000, 0b111110000000))
            by (bit_vector);
        assert(0b10000 & 0b10000 == 0b10000) by (bit_vector);
        if self.attr.executable {
            assert(u & 0b10000 == 0b10000) by (bit_vector)
                requires
                    d == 0b10000,
                    u == a | b | c | d | e | f | g | h | i,
            ;
        } else {
            assert(u & 0b10000 == 0) by (bit_vector)
                requires
                    d == 0,
                    a & 0b10000 == 0,
                    b & 0b10000 == 0,
                    c & 0b10000 == 0,
                    d & 0b10000 == 0,
                    e & 0b10000 == 0,
                    f & 0b10000 == 0,
                    g & 0b10000 == 0,
                    h & 0b10000 == 0,
                    i & 0b10000 == 0,
                    u == a | b | c | d | e | f | g | h | i,
            ;
        }

        assert(and_eq_0!(0b100000, 0, 0b1, 0b10, 0b100, 0b1000, 0b10000, 0b1000000, 0b111110000000))
            by (bit_vector);
        assert(0b100000 & 0b100000 == 0b100000) by (bit_vector);
        if self.attr.user_accessible {
            assert(u & 0b100000 == 0b100000) by (bit_vector)
                requires
                    e == 0b100000,
                    u == a | b | c | d | e | f | g | h | i,
            ;
        } else {
            assert(u & 0b100000 == 0) by (bit_vector)
                requires
                    e == 0,
                    a & 0b100000 == 0,
                    b & 0b100000 == 0,
                    c & 0b100000 == 0,
                    d & 0b100000 == 0,
                    e & 0b100000 == 0,
                    f & 0b100000 == 0,
                    g & 0b100000 == 0,
                    h & 0b100000 == 0,
                    i & 0b100000 == 0,
                    u == a | b | c | d | e | f | g | h | i,
            ;
        }

        assert(and_eq_0!(0b1000000, 0, 0b1, 0b10, 0b100, 0b1000, 0b10000, 0b100000, 0b111110000000))
            by (bit_vector);
        assert(0b1000000 & 0b1000000 == 0b1000000) by (bit_vector);
        if self.attr.device {
            assert(u & 0b1000000 == 0b1000000) by (bit_vector)
                requires
                    f == 0b1000000,
                    u == a | b | c | d | e | f | g | h | i,
            ;
        } else {
            assert(u & 0b1000000 == 0) by (bit_vector)
                requires
                    f == 0,
                    a & 0b1000000 == 0,
                    b & 0b1000000 == 0,
                    c & 0b1000000 == 0,
                    d & 0b1000000 == 0,
                    e & 0b1000000 == 0,
                    f & 0b1000000 == 0,
                    g & 0b1000000 == 0,
                    h & 0b1000000 == 0,
                    i & 0b1000000 == 0,
                    u == a | b | c | d | e | f | g | h | i,
            ;
        }

        assert(and_eq_0!(0b111110000000, 0, 0b1, 0b10, 0b100, 0b1000, 0b10000, 0b100000, 0b1000000))
            by (bit_vector);
        assert(u & 0b111110000000 == i) by (bit_vector)
            requires
                i & 0b111110000000 == i,
                a & 0b111110000000 == 0,
                b & 0b111110000000 == 0,
                c & 0b111110000000 == 0,
                d & 0b111110000000 == 0,
                e & 0b111110000000 == 0,
                f & 0b111110000000 == 0,
                g & 0b111110000000 == 0,
                h & 0b111110000000 == 0,
                u == a | b | c | d | e | f | g | h | i,
        ;
    }

    /// Lemma. The address field in the PTE is consistent with the address bits in the u64 representation.
    proof fn lemma_addr_consistent_with_bits(self)
        requires
            self.wf(),
        ensures
            self.addr.0 == self.spec_to_u64() & 0xFFFFFFFFFFFFF000,
    {
        let u = self.spec_to_u64();
        let a = self.addr.0 as u64;
        let b = ifelse!(self.attr.readable, 0b100, 0);
        let c = ifelse!(self.attr.writable, 0b1000, 0);
        let d = ifelse!(self.attr.executable, 0b10000, 0);
        let e = ifelse!(self.attr.user_accessible, 0b100000, 0);
        let f = ifelse!(self.attr.device, 0b1000000, 0);
        let g = ifelse!(self.huge, 0b10, 0);
        let h = ifelse!(self.valid, 0b1, 0);
        let i = self.padding;
        assert(u == a | b | c | d | e | f | g | h | i);

        assert(a & 0xFFFFFFFFFFFFF000 == a) by (bit_vector)
            requires
                a % 4096 == 0,
        ;
        assert(i & 0xFFFFFFFFFFFFF000 == 0) by (bit_vector)
            requires
                i & 0b111110000000 == i,
        ;
        assert(and_eq_0!(0xFFFFFFFFFFFFF000usize, 0, 0b1, 0b10, 0b100, 0b1000, 0b10000, 0b100000, 0b1000000))
            by (bit_vector);

        assert(u & 0xFFFFFFFFFFFFF000 == a) by (bit_vector)
            requires
                a & 0xFFFFFFFFFFFFF000 == a,
                b & 0xFFFFFFFFFFFFF000 == 0,
                c & 0xFFFFFFFFFFFFF000 == 0,
                d & 0xFFFFFFFFFFFFF000 == 0,
                e & 0xFFFFFFFFFFFFF000 == 0,
                f & 0xFFFFFFFFFFFFF000 == 0,
                g & 0xFFFFFFFFFFFFF000 == 0,
                h & 0xFFFFFFFFFFFFF000 == 0,
                i & 0xFFFFFFFFFFFFF000 == 0,
                u == a | b | c | d | e | f | g | h | i,
        ;
    }

    /// Lemma. The padding field in the PTE is consistent with the padding bits in the u64 representation.
    proof fn lemma_padding_consistent_with_bits(self)
        requires
            self.wf(),
        ensures
            self.padding == self.spec_to_u64() & 0b111110000000,
    {
        let u = self.spec_to_u64();
        let a = self.addr.0 as u64;
        let b = ifelse!(self.attr.readable, 0b100, 0);
        let c = ifelse!(self.attr.writable, 0b1000, 0);
        let d = ifelse!(self.attr.executable, 0b10000, 0);
        let e = ifelse!(self.attr.user_accessible, 0b100000, 0);
        let f = ifelse!(self.attr.device, 0b1000000, 0);
        let g = ifelse!(self.huge, 0b10, 0);
        let h = ifelse!(self.valid, 0b1, 0);
        let i = self.padding;
        assert(u == a | b | c | d | e | f | g | h | i);

        assert(i & 0b111110000000 == i) by (bit_vector)
            requires
                i & 0b111110000000 == i,
        ;
        assert(a & 0b111110000000 == 0) by (bit_vector)
            requires
                a % 4096 == 0,
        ;
        assert(and_eq_0!(0b111110000000, 0, 0b1, 0b10, 0b100, 0b1000, 0b10000, 0b100000, 0b1000000))
            by (bit_vector);

        assert(u & 0b111110000000 == i) by (bit_vector)
            requires
                i & 0b111110000000 == i,
                a & 0b111110000000 == 0,
                b & 0b111110000000 == 0,
                c & 0b111110000000 == 0,
                d & 0b111110000000 == 0,
                e & 0b111110000000 == 0,
                f & 0b111110000000 == 0,
                g & 0b111110000000 == 0,
                h & 0b111110000000 == 0,
                u == a | b | c | d | e | f | g | h | i,
        ;
    }
}

proof fn lemma_and_eq_0_or_self(x: u64)
    by (bit_vector)
    ensures
        x & 0b1 == 0 || x & 0b1 == 0b1,
        x & 0b10 == 0 || x & 0b10 == 0b10,
        x & 0b100 == 0 || x & 0b100 == 0b100,
        x & 0b1000 == 0 || x & 0b1000 == 0b1000,
        x & 0b10000 == 0 || x & 0b10000 == 0b10000,
        x & 0b100000 == 0 || x & 0b100000 == 0b100000,
        x & 0b1000000 == 0 || x & 0b1000000 == 0b1000000,
{
}

} // verus!
