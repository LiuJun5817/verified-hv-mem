//! Page table entry specification defined by Rust trait.
use crate::address::{
    addr::{PAddr, SpecPAddr},
    frame::{FrameSize, MemAttr},
};
use vstd::prelude::*;

// mod aarch64;

verus! {

/// Generic specification and properties of Page Table Entry.
pub trait GhostPTE: Sized {
    /// Construct from address and attributes.
    spec fn new(addr: SpecPAddr, attr: MemAttr, huge: bool) -> Self;

    /// Construct an empty entry.
    spec fn empty() -> Self;

    /// Parse from a u64 value.
    spec fn from_u64(val: u64) -> Self;

    /// Convert to a u64 value.
    spec fn to_u64(self) -> u64;

    /// Returns the physical address mapped by this entry.
    spec fn addr(self) -> SpecPAddr;

    /// Returns the attributes of this entry.
    spec fn attr(self) -> MemAttr;

    /// Returns whether this entry is valid.
    spec fn valid(self) -> bool;

    /// Returns whether this entry maps to a huge frame.
    spec fn huge(self) -> bool;

    /// PTE constructed by `new` keeps the same value.
    broadcast proof fn lemma_new_keeps_value(addr: SpecPAddr, attr: MemAttr, huge: bool)
        requires
            addr.aligned(FrameSize::Size4K.as_nat()),
        ensures
            ({
                let pte = #[trigger] Self::new(addr, attr, huge);
                pte.valid() && pte.addr() == addr && pte.attr() == attr && pte.huge() == huge
            }),
    ;

    /// `PTE::empty().valid()` is false.
    broadcast proof fn lemma_empty_invalid()
        ensures
            #[trigger] Self::empty().valid() == false,
    ;

    /// If a page table entry has value 0, it must be invalid.
    broadcast proof fn lemma_from_0_invalid()
        ensures
            #[trigger] Self::from_u64(0).valid() == false,
    ;

    /// `pte1.spec_to_u64() == pte2.spec_to_u64()` implies `pte1 == pte2`.
    broadcast proof fn lemma_eq_by_u64(pte1: Self, pte2: Self)
        requires
            #[trigger] pte1.to_u64() == #[trigger] pte2.to_u64(),
        ensures
            pte1 == pte2,
    ;

    /// `from_u64` and `to_u64` are inverses.
    broadcast proof fn lemma_from_to_u64_inverse(val: u64)
        ensures
            #[trigger] Self::from_u64(val).to_u64() == val,
    ;
}

/// Executable Page Table Entry interface.
pub trait ExecPTE<G>: Sized where G: GhostPTE {
    /// View as a ghost PTE.
    spec fn view(self) -> G;

    /// Construct from address and attributes.
    fn new(addr: PAddr, attr: MemAttr, huge: bool) -> (pte: Self)
        requires
            addr@.aligned(FrameSize::Size4K.as_nat()),
        ensures
            pte@ == G::new(addr@, attr, huge),
    ;

    /// Construct an empty entry.
    fn empty() -> (pte: Self)
        ensures
            pte@ == G::empty(),
    ;

    /// Parse from a u64 value.
    fn from_u64(val: u64) -> (pte: Self)
        ensures
            pte@ == G::from_u64(val),
    ;

    /// Convert to a u64 value.
    fn to_u64(&self) -> (res: u64)
        ensures
            res == self@.to_u64(),
    ;

    /// Returns the physical address mapped by this entry.
    fn addr(&self) -> (res: PAddr)
        ensures
            res@ == self@.addr(),
    ;

    /// Returns the attributes of this entry.
    fn attr(&self) -> (res: MemAttr)
        ensures
            res == self@.attr(),
    ;

    /// Returns whether this entry is valid.
    fn valid(&self) -> (res: bool)
        ensures
            res == self@.valid(),
    ;

    /// Returns whether this entry maps to a huge frame.
    ///
    /// In VMSAv8-64, the entry is called a "block descriptor".
    fn huge(&self) -> (res: bool)
        ensures
            res == self@.huge(),
    ;
}

/// Broadcasted lemmas for GhostPTE.
pub broadcast group group_pte_lemmas {
    GhostPTE::lemma_from_0_invalid,
    GhostPTE::lemma_empty_invalid,
    GhostPTE::lemma_eq_by_u64,
    GhostPTE::lemma_from_to_u64_inverse,
    GhostPTE::lemma_new_keeps_value,
}

} // verus!
