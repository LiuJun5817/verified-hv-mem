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

    proof fn lemma_view_len_eq_cap_pages(&self) {
    }
}

} // verus!
