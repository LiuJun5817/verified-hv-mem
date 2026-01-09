use vstd::prelude::*;
use crate::memory::address::addr::{PAddr, PAddrExec};

verus! {

/// 将“页下标 idx”映射到物理地址：base + idx * page_size
pub open spec fn idx_to_paddr(base: PAddr, idx: nat, page_size: usize) -> PAddr {
    PAddr((base.0 + idx * page_size) as nat)
}

/// 将物理地址映射回“页下标”
pub open spec fn paddr_to_idx(base: PAddr, addr: PAddr, page_size: usize) -> nat
    recommends
        addr.0 >= base.0,
        page_size > 0,
        (addr.0 - base.0) % page_size as int == 0,
{
    ((addr.0 - base.0) / page_size as int) as nat
}

// pub trait FrameAllocator: FrameAllocView {
pub trait FrameAllocator {
    spec fn view(&self) -> Seq<bool>;

    spec fn base(&self) -> PAddr;

    spec fn cap_pages() -> (res:usize);

    spec fn wf(&self) -> bool;

    spec fn spec_page_size() -> usize;

    fn page_size() -> (res:usize)
        ensures
            res == Self::spec_page_size()
    ;

    /// The empty value.
    fn empty() -> Self where Self: Sized;

    // TODO:初始化为管理 [base, base+size) 这一段连续物理内存（按页管理）
    fn init(&mut self, base: PAddrExec, size: usize)
        requires
            old(self).wf(),
            base@.aligned(Self::spec_page_size() as nat),
            size % Self::spec_page_size() == 0,
            (size / Self::spec_page_size()) <= Self::cap_pages(),
        ensures
            self.wf(),
            forall|loc1: int|
                (0 <= loc1 < (size / Self::spec_page_size())) ==> self@[loc1] == true,
            forall|loc2: int|
                ((size / Self::spec_page_size()) <= loc2 < Self::spec_page_size()) ==> self@[loc2] == old(self)@[loc2],
            self@.len() == old(self)@.len(),
    ;

    unsafe fn alloc(&mut self) -> (res: Option<PAddrExec>)
        requires
            old(self).wf(),
        ensures
            self.wf(),
            match res {
                Some(addr) => {
                    let i = paddr_to_idx(old(self).base(), addr.view(), Self::spec_page_size());
                    &&& i < Self::cap_pages()
                    &&& old(self)@[i as int] == true
                    &&& forall |j: int| 0 <= j < i ==> old(self)@[j] == false
                    &&& self@ == old(self)@.update(i as int, false)
                },
                None => {
                    &&& forall |j: int| 0 <= j < Self::cap_pages() ==> old(self)@[j] == false
                    &&& self@ == old(self)@
                },
            }
    ;

    unsafe fn alloc_contiguous(&mut self, frame_count: usize, align_log2: usize) -> (res: Option<PAddrExec>)
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
                    &&& forall|loc1: int|
                        (i <= loc1 < (i + frame_count)) ==> self@[loc1] == false
                    &&& forall|loc2: int|
                        (0 <= loc2 < i || (i + frame_count) <= loc2  < Self::cap_pages()) ==> self@[loc2] == old(self)@[loc2]
                    &&& self@.len() == old(self)@.len()
                },
                None => {
                    &&& self@ == old(self)@
                    &&& forall|j: int| (0 <= j <= (Self::cap_pages() - frame_count) as int) ==> has_obstruction(self@, j, frame_count as int,(1usize << align_log2) as int)
                }
            }
    ;

    unsafe fn dealloc(&mut self, target: PAddrExec)
        requires
            old(self).wf(),
            paddr_to_idx(old(self).base(), target.view(), Self::spec_page_size()) < Self::cap_pages(),
            !old(self)@[paddr_to_idx(old(self).base(), target.view(), Self::spec_page_size()) as int],
        ensures
            self.wf(),
            self@ == old(self)@.update(paddr_to_idx(old(self).base(), target.view(), Self::spec_page_size()) as int, true),
    ;

    unsafe fn dealloc_contiguous(&mut self, target: PAddrExec, frame_count: usize)
        requires
            old(self).wf(),
            paddr_to_idx(old(self).base(), target.view(), Self::spec_page_size()) + frame_count < Self::cap_pages(),
            forall|j: int| 
                paddr_to_idx(old(self).base(), target.view(), Self::spec_page_size()) as int <= j < (paddr_to_idx(old(self).base(), target.view(), Self::spec_page_size()) + frame_count) as int
                ==> !old(self)@[j],
        ensures
            self.wf(),
                forall|j: int| paddr_to_idx(old(self).base(), target.view(), Self::spec_page_size()) <= j < paddr_to_idx(old(self).base(), target.view(), Self::spec_page_size()) + frame_count 
                    ==> self@[j] == true,
                forall|j: int|
                    (0 <= j < paddr_to_idx(old(self).base(), target.view(), Self::spec_page_size()) || paddr_to_idx(old(self).base(), target.view(), Self::spec_page_size()) + frame_count <= j < Self::cap_pages())
                    ==> self@[j] == old(self)@[j],
                self@.len() == old(self)@.len(),
    ;
}

/// Specification function to check if a contiguous block starting at `i` of `size` contains any allocated bits (false).
/// or `i` is not a multiple of `align`
pub open spec fn has_obstruction(ba: Seq<bool>, i: int, size: int, align: int) -> bool {
    (i % align != 0) ||
    exists |k: int| i <= k < i + size && #[trigger] ba[k] == false
}

} // verus!
