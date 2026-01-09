use vstd::prelude::*;
use crate::memory::{
    address::addr::{PAddr, PAddrExec},
    bitmap_allocator::{
        bitmap_impl::BitAlloc1M,
        bitmap_trait::{BitAllocView, BitAlloc},
    },
};
use super::frame_trait::FrameAllocator;

verus! {

/// Page & Block size supported by VMSA-v8.
///
/// - For 4KB granule, support: 4K, 2M, 1G, 512G.
/// - For 16KB granule, support: 16K, 32M, 64G.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum FrameSize {
    /// 4 KiB
    Size4K,
    /// 16 KiB
    Size16K,
    /// 2 MiB
    Size2M,
    /// 32 MiB
    Size32M,
    /// 1 GiB
    Size1G,
    // /// 64 GiB
    // Size64G,
    // /// 512 GiB
    // Size512G,
}

impl FrameSize {
    /// Convert to u64.
    pub open spec fn as_nat(self) -> nat {
        match self {
            FrameSize::Size4K => 0x1000,
            FrameSize::Size16K => 0x4000,
            FrameSize::Size2M => 0x200000,
            FrameSize::Size32M => 0x2000000,
            FrameSize::Size1G => 0x40000000,
            // FrameSize::Size64G => 0x1000000000,
            // FrameSize::Size512G => 0x8000000000,
        }
    }

    /// Convert to usize.
    pub const fn as_usize(self) -> (res: usize)
        ensures
            self.as_nat() == res as nat,
    {
        match self {
            FrameSize::Size4K => 0x1000,
            FrameSize::Size16K => 0x4000,
            FrameSize::Size2M => 0x200000,
            FrameSize::Size32M => 0x2000000,
            FrameSize::Size1G => 0x40000000,
            // FrameSize::Size64G => 0x1000000000,
            // FrameSize::Size512G => 0x8000000000,
        }
    }
}

pub const PAGE_SIZE: usize = 0x1000;

pub struct FrameAllocator1M {
    pub base: PAddrExec,
    pub inner: BitAlloc1M,
}

impl FrameAllocator for FrameAllocator1M {
    open spec fn view(&self) -> Seq<bool> {
        self.inner@
    }

    open spec fn base(&self) -> PAddr {
        self.base@
    }

    open spec fn cap_pages() -> (res:usize) {
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
        Self { base: PAddrExec(0), inner: BitAlloc1M::default() }
    }

    // fn init(&mut self, base: PAddrExec, size: usize) {
        // self.base = PAddrExec(align_up(base.0));
        // // self.base = base;
        // // let page_count = align_up(size) / FrameSize::Size4K.as_usize();
        // let page_count = (size / Self::page_size());
        // self.inner.insert(0..page_count);
    // }

    unsafe fn alloc(&mut self) -> (res: Option<PAddrExec>) {
        let ret = self.inner.alloc().map(|idx| PAddrExec(idx * Self::page_size() + self.base.0));
        ret
    }

    unsafe fn alloc_contiguous(&mut self, frame_count: usize, align_log2: usize) -> (res: Option<PAddrExec>) {
        let ret = self
            .inner
            .alloc_contiguous(frame_count, align_log2)
            .map(|idx| PAddrExec(idx * Self::page_size() + self.base.0));
        ret
    }

    unsafe fn dealloc(&mut self, target: PAddrExec) {
        self.inner.dealloc((target.0 - self.base.0) / Self::page_size())
    }

    unsafe fn dealloc_contiguous(&mut self, target: PAddrExec, frame_count: usize) {
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
//     base: PAddrExec,
//     region_pages_exec: usize,
//     inner: BitAlloc1M,
// }

// impl BitmapFrameAllocator {
//     pub fn empty() -> Self {
//         Self { base: PAddrExec(0), region_pages_exec: 0, inner: BitAlloc1M::default() }
//     }

//     ///（可选）运行时查询
//     pub fn region_pages_usize(&self) -> usize { self.region_pages_exec }
// }

// impl FrameAllocView for BitmapFrameAllocator {
//     spec fn base(&self) -> PAddr { self.base.view() }

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

//     fn init(&mut self, base: PAddrExec, size: usize) {
//         let ps = Self::page_size() as usize;
//         let pages: usize = size / ps;

//         // reset
//         self.base = base;
//         self.region_pages_exec = pages;
//         self.inner = BitAlloc1M::default();

//         // 只把 [0, pages) 标记为 free；其余保持 false（不可用）
//         self.inner.insert(0..pages);
//     }

    // unsafe fn alloc(&mut self) -> (res: Option<PAddrExec>) {
    //     match self.inner.alloc() {
    //         Some(idx) => {
    //             let ps = Self::page_size() as usize;
    //             Some(PAddrExec(self.base.0 + idx * ps))
    //         }
    //         None => None
    //     }
    // }

    // unsafe fn alloc_contiguous(&mut self, count: usize, align_log2: usize) -> (res: Option<PAddrExec>) {
    //     match self.inner.alloc_contiguous(count, align_log2) {
    //         Some(base_idx) => {
    //             let ps = Self::page_size() as usize;
    //             Some(PAddrExec(self.base.0 + base_idx * ps))
    //         }
    //         None => None
    //     }
    // }

    // unsafe fn dealloc(&mut self, p: PAddrExec) {
    //     let ps = Self::page_size() as usize;
    //     let idx = (p.0 - self.base.0) / ps;
    //     self.inner.dealloc(idx);
    // }

    // unsafe fn dealloc_contiguous(&mut self, p: PAddrExec, count: usize) {
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
#[verifier::external]
fn main() {}

} // verus!
