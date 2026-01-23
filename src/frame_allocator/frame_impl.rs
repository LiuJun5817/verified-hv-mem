use super::frame_trait::FrameAllocator;
use crate::{
    address::{
        addr::{PAddr, SpecPAddr},
        frame::FrameSize,
    },
    bitmap_allocator::bitmap_impl::{BitAlloc, BitAlloc1M, BitAllocView},
};
use vstd::prelude::*;

verus! {

/// A frame allocator implementation using a 1M-bitmap to track allocated frames.
pub struct FrameAllocator1M {
    pub base: PAddr,
    pub inner: BitAlloc1M,
}

impl FrameAllocator for FrameAllocator1M {
    open spec fn view(&self) -> Seq<bool> {
        self.inner@
    }

    open spec fn base(&self) -> SpecPAddr {
        self.base@
    }

    open spec fn cap_pages() -> (res: usize) {
        BitAlloc1M::spec_cap()
    }

    open spec fn wf(&self) -> bool {
        self.inner.wf()
    }

    open spec fn spec_page_size() -> usize {
        FrameSize::Size4K.as_nat() as usize
    }

    fn page_size() -> usize {
        FrameSize::Size4K.as_usize()
    }

    fn empty() -> Self where Self: Sized {
        Self { base: PAddr(0), inner: BitAlloc1M::default() }
    }

    fn init(&mut self, base: PAddr, size: usize) {
        self.base = base;
        let page_count = (size / Self::page_size());
        self.inner.insert(0..page_count);
    }

    fn alloc(&mut self) -> (res: Option<PAddr>) {
        let ret = self.inner.alloc().map(|idx| PAddr(idx * Self::page_size() + self.base.0));
        ret
    }

    fn alloc_contiguous(&mut self, frame_count: usize, align_log2: usize) -> (res: Option<PAddr>) {
        let ret = self.inner.alloc_contiguous(frame_count, align_log2).map(
            |idx| PAddr(idx * Self::page_size() + self.base.0),
        );
        ret
    }

    fn dealloc(&mut self, target: PAddr) {
        self.inner.dealloc((target.0 - self.base.0) / Self::page_size())
    }

    fn dealloc_contiguous(&mut self, target: PAddr, frame_count: usize) {
        let start_idx = (target.0 - self.base.0) / Self::page_size();
        self.inner.remove(start_idx..(start_idx + frame_count));
    }
}

// pub open spec fn align_up(addr: usize) -> usize {
//     (addr + FrameSize::Size4K.as_usize() - 1) & !(FrameSize::Size4K.as_usize() - 1)
// }
// pub open spec fn align_up_spec(addr: usize) -> usize
// {
//     if addr % PAGE_SIZE == 0 {
//         addr
//     } else {
//         (addr + (PAGE_SIZE - addr % PAGE_SIZE)) as usize
//     }
// }
// #[verifier::bit_vector]
// proof fn lemma_align_up(addr: usize)
//     requires
//         addr + PAGE_SIZE <= usize::MAX,
//     ensures
//        ((addr + PAGE_SIZE - 1) & !(PAGE_SIZE - 1)) == align_up_spec(addr),
// {}
// pub fn align_up(addr: usize) -> (res:usize)
//     requires
//         addr + PAGE_SIZE <= usize::MAX,
//         // PAGE_SIZE == 0x1000,
//     ensures
//         res == align_up_spec(addr),
// {
//     (addr + PAGE_SIZE - 1) & !(PAGE_SIZE - 1)
//     // if addr % PAGE_SIZE == 0 {
//     //     addr
//     // } else {
//     //     (addr + (PAGE_SIZE - addr % PAGE_SIZE)) as usize
//     // }
// }
// pub struct BitmapFrameAllocator {
//     base: SpecPAddr,
//     region_pages_exec: usize,
//     inner: BitAlloc1M,
// }
// impl BitmapFrameAllocator {
//     pub fn empty() -> Self {
//         Self { base: SpecPAddr(0), region_pages_exec: 0, inner: BitAlloc1M::default() }
//     }
//     ///（可选）运行时查询
//     pub fn region_pages_usize(&self) -> usize { self.region_pages_exec }
// }
// impl FrameAllocView for BitmapFrameAllocator {
//     spec fn base(&self) -> SpecSpecPAddr { self.base.view() }
//     spec fn region_pages(&self) -> nat { self.region_pages_exec as nat }
//     spec fn bits(&self) -> Seq<bool> { self.inner@ }
//     spec fn page_size() -> nat {
//         // 你也可以改成：crate::consts::PAGE_SIZE as nat
//         4096
//     }
//     spec fn cap_pages() -> nat {
//         // BitAlloc1M::spec_cap() 是 usize，这里转成 nat
//         BitAlloc1M::spec_cap() as nat
//     }
//     // wf() 使用 trait 默认定义即可（如果你想加强，也可以在这里重写）
// }
// impl FrameAllocator for BitmapFrameAllocator {
//     /// Creates a new `BitAllocCascade16` with all bits set to 0 (all free).
//     fn default() -> Self {
//         BitAllocCascade16 {
//             bitset: BitAlloc16 { bits: 0 },
//             sub: [T::default(); 16], // need the trait "std::marker::Copy"
//         }
//     }
//     fn init(&mut self, base: SpecPAddr, size: usize) {
//         let ps = Self::page_size() as usize;
//         let pages: usize = size / ps;
//         // reset
//         self.base = base;
//         self.region_pages_exec = pages;
//         self.inner = BitAlloc1M::default();
//         // 只把 [0, pages) 标记为 free；其余保持 false（不可用）
//         self.inner.insert(0..pages);
//     }
// unsafe fn alloc(&mut self) -> (res: Option<SpecPAddr>) {
//     match self.inner.alloc() {
//         Some(idx) => {
//             let ps = Self::page_size() as usize;
//             Some(SpecPAddr(self.base.0 + idx * ps))
//         }
//         None => None
//     }
// }
// unsafe fn alloc_contiguous(&mut self, count: usize, align_log2: usize) -> (res: Option<SpecPAddr>) {
//     match self.inner.alloc_contiguous(count, align_log2) {
//         Some(base_idx) => {
//             let ps = Self::page_size() as usize;
//             Some(SpecPAddr(self.base.0 + base_idx * ps))
//         }
//         None => None
//     }
// }
// unsafe fn dealloc(&mut self, p: SpecPAddr) {
//     let ps = Self::page_size() as usize;
//     let idx = (p.0 - self.base.0) / ps;
//     self.inner.dealloc(idx);
// }
// unsafe fn dealloc_contiguous(&mut self, p: SpecPAddr, count: usize) {
//     let ps = Self::page_size() as usize;
//     let base_idx = (p.0 - self.base.0) / ps;
//     // 用 while 写，后续你要做 Verus 证明时更好加 invariant
//     let mut k: usize = 0;
//     while k < count
//         invariant
//             k <= count,
//             self.wf(), // 需要的话也可写更细的循环不变量
//     {
//         self.inner.dealloc(base_idx + k);
//         k = k + 1;
//     }
// }
// }
} // verus!
