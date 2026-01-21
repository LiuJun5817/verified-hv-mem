use core::ops::Range;
use vstd::{prelude::*, seq_lib::*};

verus! {

/// Allocator that uses a bitmap to track resource usage (0: allocated, 1: free).
pub trait BitmapAllocator {
    /// Specification function to view the internal u16 as a sequence of booleans.
    spec fn view(&self) -> Seq<bool>;

    /// The bitmap has a total of CAP bits, numbered from 0 to CAP-1 inclusively.
    fn cap() -> (res: usize)
        requires
            Self::cascade_not_overflow(),
        ensures
            res == Self::spec_cap(),
    ;

    spec fn spec_cap() -> (res: usize);

    spec fn cascade_not_overflow() -> bool;
      // cap_not_overflow
    /// The default value. Workaround for `const fn new() -> Self`.
    fn default() -> Self where Self: Sized;

    /// Structure is well_formed
    spec fn wf(&self) -> bool;

    /// Allocate a free bit.
    fn alloc(&mut self) -> (res: Option<usize>)
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
                    &&& forall|j: int| 0 <= j < i ==> old(self)@[j] == false
                    &&& self@ == old(self)@.update(i as int, false)
                },
                None => {
                    // If failed, all bits were already allocated (self.bits is 0), and the state is unchanged.
                    &&& forall|j: int| 0 <= j < Self::spec_cap() ==> old(self)@[j] == false
                    &&& self@ == old(self)@
                },
            },
    ;

    /// Allocates a contiguous block of `size` bits with specified `align_log2` alignment.
    /// Returns `Some(base_index)` if successful, `None` if no suitable block is found.
    fn alloc_contiguous(&mut self, size: usize, align_log2: usize) -> (res: Option<usize>)
        requires
            old(self).wf(),
            0 < size <= Self::spec_cap(),
            align_log2 < 64,  // Prevent displacement overflow

        ensures
            self.wf(),
            match res {
                Some(base) => {
                    // If successful, a contiguous block from `base` to `base + size` is allocated (set to false).
                    // Other indices remain unchanged.
                    &&& base % (1usize << align_log2) == 0
                    &&& forall|loc1: int| (base <= loc1 < (base + size)) ==> self@[loc1] == false
                    &&& forall|loc2: int|
                        (0 <= loc2 < base || (base + size) <= loc2 < Self::spec_cap())
                            ==> self@[loc2] == old(self)@[loc2]
                    &&& self@.len() == old(self)@.len()
                },
                None => {
                    // If failed, no suitable space was found, and the state is unchanged.
                    // This implies either no free bits, or all free contiguous blocks are too small or misaligned.
                    Self::spec_cap() < (1usize << align_log2) || forall|i: int|
                        (0 <= i <= (Self::spec_cap() - size) as int) ==> has_obstruction(
                            self@,
                            i,
                            size as int,
                            (1usize << align_log2) as int,
                        )
                },
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
}

/// Specification function to check if a contiguous block starting at `i` of `size` contains any allocated bits (false).
/// or `i` is not a multiple of `align`
pub open spec fn has_obstruction(ba: Seq<bool>, i: int, size: int, align: int) -> bool {
    (i % align != 0) || exists|k: int| i <= k < i + size && #[trigger] ba[k] == false
}

#[verifier::external]
fn main() {
}

} // verus!
