//! Page table entry specification defined by Rust trait.
use crate::address::{
    addr::{PAddr, SpecPAddr},
    frame::{FrameSize, MemAttr},
};
use vstd::prelude::*;

verus! {

/// Generic page table entry interface.
pub trait PageTableEntry: Sized {
    /// Construct from address and attributes.
    spec fn spec_new(addr: SpecPAddr, attr: MemAttr, huge: bool) -> Self;

    /// Construct an empty entry.
    spec fn spec_empty() -> Self;

    /// Parse from a u64 value.
    spec fn spec_from_u64(val: u64) -> Self;

    /// Convert to a u64 value.
    spec fn spec_to_u64(self) -> u64;

    /// Returns the physical address mapped by this entry.
    spec fn spec_addr(self) -> SpecPAddr;

    /// Returns the attributes of this entry.
    spec fn spec_attr(self) -> MemAttr;

    /// Returns whether this entry is valid.
    spec fn spec_valid(self) -> bool;

    /// Returns whether this entry maps to a huge frame.
    spec fn spec_huge(self) -> bool;

    /// Construct from address and attributes.
    fn new(addr: PAddr, attr: MemAttr, huge: bool) -> (pte: Self)
        requires
            addr@.aligned(FrameSize::Size4K.as_nat()),
        ensures
            pte == Self::spec_new(addr@, attr, huge),
    ;

    /// Construct an empty entry.
    fn empty() -> (pte: Self)
        ensures
            pte == Self::spec_empty(),
    ;

    /// Parse from a u64 value.
    fn from_u64(val: u64) -> (pte: Self)
        ensures
            pte == Self::spec_from_u64(val),
    ;

    /// Convert to a u64 value.
    fn to_u64(&self) -> (res: u64)
        ensures
            res == self.spec_to_u64(),
    ;

    /// Returns the physical address mapped by this entry.
    fn addr(&self) -> (res: PAddr)
        ensures
            res@ == self.spec_addr(),
    ;

    /// Returns the attributes of this entry.
    fn attr(&self) -> (res: MemAttr)
        ensures
            res == self.spec_attr(),
    ;

    /// Returns whether this entry is valid.
    fn valid(&self) -> (res: bool)
        ensures
            res == self.spec_valid(),
    ;

    /// Returns whether this entry maps to a huge frame.
    fn huge(&self) -> (res: bool)
        ensures
            res == self.spec_huge(),
    ;

    /// PTE constructed by `new` keeps the same value.
    broadcast proof fn lemma_new_keeps_value(addr: SpecPAddr, attr: MemAttr, huge: bool)
        requires
            addr.aligned(FrameSize::Size4K.as_nat()),
        ensures
            ({
                let pte = #[trigger] Self::spec_new(addr, attr, huge);
                pte.spec_valid() && pte.spec_addr() == addr && pte.spec_attr() == attr
                    && pte.spec_huge() == huge
            }),
    ;

    /// `PTE::empty().valid()` is false.
    broadcast proof fn lemma_empty_invalid()
        ensures
            #[trigger] Self::spec_empty().spec_valid() == false,
    ;

    /// If a page table entry has value 0, it must be invalid.
    broadcast proof fn lemma_from_0_invalid()
        ensures
            #[trigger] Self::spec_from_u64(0).spec_valid() == false,
    ;

    /// `pte1.spec_to_u64() == pte2.spec_to_u64()` implies `pte1 == pte2`.
    broadcast proof fn lemma_eq_by_u64(pte1: Self, pte2: Self)
        requires
            #[trigger] pte1.spec_to_u64() == #[trigger] pte2.spec_to_u64(),
        ensures
            pte1 == pte2,
    ;

    /// `from_u64` and `to_u64` are inverses.
    broadcast proof fn lemma_from_to_u64_inverse(val: u64)
        ensures
            #[trigger] Self::spec_from_u64(val).spec_to_u64() == val,
    ;
}

/// Broadcasted lemmas for GhostPTE.
pub broadcast group group_pte_lemmas {
    PageTableEntry::lemma_from_0_invalid,
    PageTableEntry::lemma_empty_invalid,
    PageTableEntry::lemma_eq_by_u64,
    PageTableEntry::lemma_from_to_u64_inverse,
    PageTableEntry::lemma_new_keeps_value,
}

} // verus!
