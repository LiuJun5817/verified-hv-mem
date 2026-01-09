use core::ops::Range;
use vstd::{prelude::*, seq_lib::*};

verus! {
    
pub trait BitAllocView {
    /// Specification function to view the internal u16 as a sequence of booleans.
    spec fn view(&self) -> Seq<bool>;

    /// The bitmap has a total of CAP bits, numbered from 0 to CAP-1 inclusively.
    fn cap() -> (res:usize)
        requires
            Self::cascade_not_overflow(),
        ensures
            res == Self::spec_cap(),
    ;

    spec fn spec_cap() -> (res:usize);

    spec fn cascade_not_overflow() -> bool; // cap_not_overflow

    // spec fn lemma_cap_is_pow16_pre() -> bool;

    // /// The capacity is an exponential multiple of 16.
    // /// and the current bitmap only supports the maximum allocatable page size of 1M.
    // proof fn lemma_cap_is_pow16()
    //     requires
    //         Self::lemma_cap_is_pow16_pre(),
    //         Self::cascade_not_overflow(),
    //     ensures
    //         is_pow16(Self::spec_cap()),
    // ;

    /// The default value. Workaround for `const fn new() -> Self`.
    fn default() -> Self where Self: Sized;

    /// Structure is well_formed
    spec fn wf(&self) -> bool;

    // /// Find a index not less than a given key, where the bit is free.
    // fn next(&self, key: usize) -> (res: Option<usize>)
    //     requires
    //         self.wf(),
    //         key < Self::spec_cap(),
    //     ensures
    //         self.wf(),
    //         match res {
    //             Some(re) => {
    //                 // If successful, returns the first free index `re` that is not less than `key`.
    //                 // All indices between `key` and `re` (exclusive) must be allocated (false).
    //                 &&& self@[re as int] == true
    //                 &&& key <= re < Self::spec_cap()
    //                 &&& forall|i: int| key <= i < re ==> self@[i] == false
    //             },
    //             None => {
    //                 // If failed, all indices from `key` to the end are allocated (false).
    //                 forall|i: int| key <= i < Self::spec_cap() ==> self@[i] == false
    //             }
    //         },
    // ;

    // /// Lemma: When self is well-formed, spec_any() is equivalent to
    // /// “there exists an index j such that self@[j] == true”,
    // /// linking the abstract semantics with the concrete boolean bits.
    // proof fn lemma_bits_nonzero_implies_exists_true(&self)
    //     requires
    //         self.wf(),
    //     ensures
    //         self.wf(),
    //         self.spec_any() == exists|j:int| 0 <= j < Self::spec_cap() && self@[j] == true,
    // ;

    /// Whether there are free bits remaining
    fn any(&self) -> (res: bool)
        ensures
            res == self.spec_any(),
    ;

    spec fn spec_any(&self) -> bool;

    /// Whether a specific bit is free
    fn test(&self, key: usize) -> (res: bool)
        requires
            self.wf(),
            key < Self::spec_cap(),
        ensures
            self.wf(),
            res == self@[key as int],
    ;

    // /// Finds a contiguous block of `size` free bits within the bitmap, respecting `align_log2`.
    // /// Returns the base index of the found block, or `None` if no such block exists.
    // fn find_contiguous(&self, capacity: usize, size: usize, align_log2: usize) -> (res: Option<usize>)
    //     requires
    //         self.wf(),
    //         capacity == Self::spec_cap(),
    //         capacity < 0x100000,
    //         is_pow16(capacity),
    //         0 < size <= capacity,
    //         align_log2 < 64,
    //     ensures
    //         self.wf(),
    //         match res {
    //             Some(base) => {
    //                 // If successful, a block of `size` free bits is found starting at `base`.
    //                 // The block must be within capacity, aligned, and all bits within the block must be free (true).
    //                 &&& base + size <= capacity
    //                 &&& base % (1usize << align_log2) == 0
    //                 &&& forall|i: int| base <= i < base + size ==> self@[i] == true //self.next(i) != None
    //             },
    //             None => {
    //                 // If failed, no suitable block exists.
    //                 // This implies either no free bits, or all potential blocks are obstructed or misaligned.
    //                 capacity < (1usize << align_log2) || !self.spec_any() ||
    //                 forall|i: int| (0 <= i <= capacity - size) ==> has_obstruction(self@, i, size as int,(1usize << align_log2) as int)
    //             }
    //         }
    // ;
}

/// Allocator of a bitmap, able to allocate / free bits.
pub trait BitAlloc: BitAllocView{
    /// Allocate a free bit.
    fn alloc(&mut self) -> (res:Option<usize>)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            match res {
                Some(i) => {
                    // If successful, a previously free index `i` is now allocated (set to false).
                    // Other indices remain unchanged.
                    &&& i < Self::spec_cap()
                    &&& old(self)@[i as int] == true
                    &&& forall |j: int| 0 <= j < i ==> old(self)@[j] == false
                    &&& self@ == old(self)@.update(i as int, false)
                },
                None => {
                    // If failed, all bits were already allocated (self.bits is 0), and the state is unchanged.
                    &&& !old(self).spec_any()
                    &&& forall |j: int| 0 <= j < Self::spec_cap() ==> old(self)@[j] == false
                    &&& self@ == old(self)@
                },
            }
    ;

    /// Allocates a contiguous block of `size` bits with specified `align_log2` alignment.
    /// Returns `Some(base_index)` if successful, `None` if no suitable block is found.
    fn alloc_contiguous(&mut self, size: usize, align_log2: usize) -> (res: Option<usize>)
        requires
            old(self).wf(),
            0 < size <= Self::spec_cap(),
            align_log2 < 64, // Prevent displacement overflow
        ensures
            self.wf(),
            match res {
                Some(base) => {
                    // If successful, a contiguous block from `base` to `base + size` is allocated (set to false).
                    // Other indices remain unchanged.
                    &&& base % (1usize << align_log2) == 0
                    &&& forall|loc1: int|
                        (base <= loc1 < (base + size)) ==> self@[loc1] == false
                    &&& forall|loc2: int|
                        (0 <= loc2 < base || (base + size) <= loc2  < Self::spec_cap()) ==> self@[loc2] == old(self)@[loc2]
                    &&& self@.len() == old(self)@.len()
                },
                None => {
                    // If failed, no suitable space was found, and the state is unchanged.
                    // This implies either no free bits, or all free contiguous blocks are too small or misaligned.
                    Self::spec_cap() < (1usize << align_log2) || !self.spec_any() ||
                    forall|i: int| (0 <= i <= (Self::spec_cap() - size) as int) ==> has_obstruction(self@, i, size as int,(1usize << align_log2) as int)
                }
            },
    ;

    /// Free an allocated bit.
    fn dealloc(&mut self, key: usize)
        requires
            old(self).wf(),
            key < Self::spec_cap(),
            !old(self)@[key as int],
        ensures
            self@ == old(self)@.update(key as int, true),
            self.wf(),
    ;

    // /// Mark bits in the range as val
    // fn set_range_to(&mut self, range: Range<usize>, val: bool)
    //     requires
    //         old(self).wf(),
    //         range.start < Self::spec_cap(),
    //         range.end <= Self::spec_cap(),
    //         range.start < range.end,
    //     ensures
    //         forall|loc1: int|
    //             (range.start <= loc1 < range.end) ==> self@[loc1] == val,
    //         forall|loc2: int|
    //             (0 <= loc2 < range.start || range.end <= loc2 < Self::spec_cap()) ==> self@[loc2] == old(self)@[loc2],
    //         self@.len() == old(self)@.len(),
    //         self.wf(),
    // ;

    // /// Mark bits in the range as unallocated (available)
    // fn insert(&mut self, range: Range<usize>)
    //     requires
    //         old(self).wf(),
    //         range.start < Self::spec_cap(),
    //         range.end <= Self::spec_cap(),
    //         range.start < range.end,
    //     ensures
    //         forall|loc1: int|
    //             (range.start <= loc1 < range.end) ==> self@[loc1] == true,
    //         forall|loc2: int|
    //             (0 <= loc2 < range.start || range.end <= loc2 < Self::spec_cap()) ==> self@[loc2] == old(self)@[loc2],
    //         self@.len() == old(self)@.len(),
    //         self.wf(),
    // ;

    // /// Reverse of insert
    // fn remove(&mut self, range: Range<usize>)
    //     requires
    //         old(self).wf(),
    //         range.start < Self::spec_cap(),
    //         range.end <= Self::spec_cap(),
    //         range.start < range.end,
    //     ensures
    //         forall|loc1: int|
    //             (range.start <= loc1 < range.end) ==> self@[loc1] == false,
    //         forall|loc2: int|
    //             (0 <= loc2 < range.start || range.end <= loc2 < Self::spec_cap()) ==> self@[loc2] == old(self)@[loc2],
    //         self@.len() == old(self)@.len(),
    //         self.wf(),
    // ;
}

/// Specification function to check if a contiguous block starting at `i` of `size` contains any allocated bits (false).
/// or `i` is not a multiple of `align`
pub open spec fn has_obstruction(ba: Seq<bool>, i: int, size: int, align: int) -> bool {
    (i % align != 0) ||
    exists |k: int| i <= k < i + size && #[trigger] ba[k] == false
}

// /// The capacity is an exponential multiple of 16.
// /// and the current bitmap only supports the maximum allocatable page size of 1M.
// pub open spec fn is_pow16(cap: usize) -> bool {
//     cap == 16 || cap == 256 || cap == 4096 || cap == 65536 || cap == 1048576
// }

#[verifier::external]
fn main() {}

}



