use crate::address::addr::{PAddr, SpecPAddr};
use vstd::prelude::*;

verus! {

/// Map page idx to physical address: base + idx * page_size
pub open spec fn idx_to_paddr(base: SpecPAddr, idx: nat, page_size: usize) -> SpecPAddr {
    SpecPAddr((base.0 + idx * page_size) as nat)
}

/// Map physical address to page idx: (addr - base) / page_size
pub open spec fn paddr_to_idx(base: SpecPAddr, addr: SpecPAddr, page_size: usize) -> nat
    recommends
        addr.0 >= base.0,
        page_size > 0,
        (addr.0 - base.0) % page_size as int == 0,
{
    ((addr.0 - base.0) / page_size as int) as nat
}

/// Physical frame allocator, supporting allocation and deallocation of frames.
pub trait FrameAllocator {
    spec fn view(&self) -> Seq<bool>;

    spec fn base(&self) -> SpecPAddr;

    spec fn cap_pages() -> (res: usize);

    spec fn wf(&self) -> bool;

    spec fn spec_page_size() -> usize;

    fn page_size() -> (res: usize)
        ensures
            res == Self::spec_page_size(),
    ;

    /// The empty value.
    fn empty() -> Self where Self: Sized;

    /// Initialize the frame allocator with a base physical address and size in bytes.
    fn init(&mut self, base: PAddr, size: usize)
        requires
            old(self).wf(),
            base@.aligned(Self::spec_page_size() as nat),
            size % Self::spec_page_size() == 0,
            (size / Self::spec_page_size()) <= Self::cap_pages(),
        ensures
            self.wf(),
            forall|loc1: int| (0 <= loc1 < (size / Self::spec_page_size())) ==> self@[loc1] == true,
            forall|loc2: int|
                ((size / Self::spec_page_size()) <= loc2 < Self::spec_page_size()) ==> self@[loc2]
                    == old(self)@[loc2],
            self@.len() == old(self)@.len(),
    ;

    /// Allocate a single frame.
    unsafe fn alloc(&mut self) -> (res: Option<PAddr>)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            match res {
                Some(addr) => {
                    let i = paddr_to_idx(old(self).base(), addr.view(), Self::spec_page_size());
                    &&& i < Self::cap_pages()
                    &&& old(self)@[i as int] == true
                    &&& forall|j: int| 0 <= j < i ==> old(self)@[j] == false
                    &&& self@ == old(self)@.update(i as int, false)
                },
                None => {
                    &&& forall|j: int| 0 <= j < Self::cap_pages() ==> old(self)@[j] == false
                    &&& self@ == old(self)@
                },
            },
    ;

    /// Allocate a contiguous block of frames.
    unsafe fn alloc_contiguous(&mut self, frame_count: usize, align_log2: usize) -> (res: Option<
        PAddr,
    >)
        requires
            old(self).wf(),
            0 < frame_count <= Self::cap_pages(),
            align_log2 < 64,
        ensures
            self.wf(),
            match res {
                Some(addr) => {
                    let i = paddr_to_idx(old(self).base(), addr.view(), Self::spec_page_size());
                    &&& i as usize % (1usize << align_log2) == 0
                    &&& forall|loc1: int| (i <= loc1 < (i + frame_count)) ==> self@[loc1] == false
                    &&& forall|loc2: int|
                        (0 <= loc2 < i || (i + frame_count) <= loc2 < Self::cap_pages())
                            ==> self@[loc2] == old(self)@[loc2]
                    &&& self@.len() == old(self)@.len()
                },
                None => {
                    &&& self@ == old(self)@
                    &&& forall|j: int|
                        (0 <= j <= (Self::cap_pages() - frame_count) as int) ==> has_obstruction(
                            self@,
                            j,
                            frame_count as int,
                            (1usize << align_log2) as int,
                        )
                },
            },
    ;

    /// Deallocate a single frame.
    unsafe fn dealloc(&mut self, target: PAddr)
        requires
            old(self).wf(),
            paddr_to_idx(old(self).base(), target.view(), Self::spec_page_size())
                < Self::cap_pages(),
            !old(self)@[paddr_to_idx(
                old(self).base(),
                target.view(),
                Self::spec_page_size(),
            ) as int],
        ensures
            self.wf(),
            self@ == old(self)@.update(
                paddr_to_idx(old(self).base(), target.view(), Self::spec_page_size()) as int,
                true,
            ),
    ;

    /// Deallocate a contiguous block of frames.
    unsafe fn dealloc_contiguous(&mut self, target: PAddr, frame_count: usize)
        requires
            old(self).wf(),
            paddr_to_idx(old(self).base(), target.view(), Self::spec_page_size()) + frame_count
                < Self::cap_pages(),
            forall|j: int|
                paddr_to_idx(old(self).base(), target.view(), Self::spec_page_size()) as int <= j
                    < (paddr_to_idx(old(self).base(), target.view(), Self::spec_page_size())
                    + frame_count) as int ==> !old(self)@[j],
        ensures
            self.wf(),
            forall|j: int|
                paddr_to_idx(old(self).base(), target.view(), Self::spec_page_size()) <= j
                    < paddr_to_idx(old(self).base(), target.view(), Self::spec_page_size())
                    + frame_count ==> self@[j] == true,
            forall|j: int|
                (0 <= j < paddr_to_idx(old(self).base(), target.view(), Self::spec_page_size())
                    || paddr_to_idx(old(self).base(), target.view(), Self::spec_page_size())
                    + frame_count <= j < Self::cap_pages()) ==> self@[j] == old(self)@[j],
            self@.len() == old(self)@.len(),
    ;
}

/// Specification function to check if a contiguous block starting at `i` of `size` contains any allocated bits (false).
/// or `i` is not a multiple of `align`
pub open spec fn has_obstruction(ba: Seq<bool>, i: int, size: int, align: int) -> bool {
    (i % align != 0) || exists|k: int| i <= k < i + size && #[trigger] ba[k] == false
}

} // verus!
