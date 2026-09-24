//! Interface-only adapter for the shared host memory-operation benchmarks.
//!
//! Keep native allocation/result types in measured buffers. Every assertion,
//! pool check, registration, and table creation/destruction runs outside timing.

use std::{
    alloc::{alloc_zeroed, dealloc, handle_alloc_error, Layout},
    mem,
    ptr::NonNull,
};

use verified_hv_mem::{
    address::{
        addr::{PAddr, VAddr},
        frame::{Frame, FrameSize, MemAttr},
    },
    bitmap_allocator::bitmap_impl::BitAlloc1M,
    global_allocator::{ClientState, GlobalAllocator},
    page_table::{
        pt_arch::{PTArch, PTArchLevel},
        Aarch64PTE, ExPageTable, PTConstants, PageTable,
    },
};
use vstd::prelude::Tracked;

pub const PAGE_SIZE: usize = 4096;
pub const POOL_FRAMES: usize = 1024;
const TABLE_PA: usize = 0x1000_0000;
const VIRTUAL_BASE: usize = 0x1000_0000;
const DATA_PA: usize = 0x6000_0000;

type Allocator = GlobalAllocator<BitAlloc1M>;
pub type Allocation = PAddr;
pub type Table = ExPageTable<BitAlloc1M, Aarch64PTE>;
pub type MapResult = Result<(), ()>;
pub type UnmapResult = Result<Frame, ()>;
pub type QueryResult = Result<(VAddr, Frame), ()>;

pub struct Client {
    token: Tracked<ClientState>,
}

/// Own the actual host memory dereferenced by the page-table implementation.
struct Pool {
    ptr: NonNull<u8>,
    layout: Layout,
}

impl Pool {
    fn new() -> Self {
        let layout = Layout::from_size_align(POOL_FRAMES * PAGE_SIZE, PAGE_SIZE).unwrap();
        // SAFETY: nonzero page-aligned layout, uniquely owned below.
        let ptr = NonNull::new(unsafe { alloc_zeroed(layout) })
            .unwrap_or_else(|| handle_alloc_error(layout));
        let pool = Self { ptr, layout };
        for page in 0..POOL_FRAMES {
            // SAFETY: each address is inside the owned allocation. Commit every
            // page before timing; initial allocator frames must be all zero.
            unsafe { pool.ptr.as_ptr().add(page * PAGE_SIZE).write_volatile(0) };
        }
        pool
    }

    fn base(&self) -> usize {
        self.ptr.as_ptr() as usize
    }

    fn frame_index(&self, addr: PAddr) -> usize {
        let offset = addr.0.checked_sub(self.base()).expect("frame below pool");
        assert!(offset < self.layout.size(), "frame outside pool");
        assert_eq!(offset % PAGE_SIZE, 0, "unaligned frame");
        offset / PAGE_SIZE
    }

    fn assert_zero_frame(&self, addr: PAddr) {
        let index = self.frame_index(addr);
        // SAFETY: checked in-pool frame, initialized by alloc_zeroed. The
        // fixture performs this check only while it uniquely owns the frame.
        let bytes = unsafe {
            std::slice::from_raw_parts(self.ptr.as_ptr().add(index * PAGE_SIZE), PAGE_SIZE)
        };
        assert!(bytes.iter().all(|&byte| byte == 0), "frame was not cleared");
    }
}

impl Drop for Pool {
    fn drop(&mut self) {
        // SAFETY: matching allocation and layout. The fixture drops its
        // allocator before this pool; callers destroy tables first.
        unsafe { dealloc(self.ptr.as_ptr(), self.layout) };
    }
}

pub struct Fixture {
    // Field order keeps the backing allocation alive until after the allocator.
    allocator: Allocator,
    pool: Pool,
}

impl Fixture {
    pub fn new() -> Self {
        let pool = Pool::new();
        let allocator = Allocator::default(PAddr(pool.base()));
        // This runtime-only harness supplies real zeroed frames. Only the
        // erased Verus permission map is assumed; library code is unchanged.
        allocator.init(POOL_FRAMES, Tracked::assume_new());
        Self { allocator, pool }
    }

    pub fn new_client(&self) -> Client {
        Client {
            token: self.allocator.register_client(),
        }
    }

    #[inline]
    pub fn alloc(&self, client: &mut Client) -> Allocation {
        // Tracked<ClientState> is zero-sized but intentionally not Copy. Move
        // the actual token into the API and retain its returned successor.
        let token = mem::replace(&mut client.token, Tracked::assume_new());
        let (allocation, next) = self.allocator.alloc(token);
        client.token = next;
        allocation
    }

    #[inline]
    pub fn dealloc(&self, client: &mut Client, allocation: Allocation) {
        let token = mem::replace(&mut client.token, Tracked::assume_new());
        client.token = self.allocator.dealloc(token, allocation);
    }

    pub fn frame_index(&self, allocation: &Allocation) -> usize {
        self.pool.frame_index(*allocation)
    }

    /// Check recovery, uniqueness, bounds, and zeroing before/after benchmarks.
    /// No table or allocated frame may remain live when this is called.
    pub fn assert_all_frames_returned(&self) {
        let mut client = self.new_client();
        let mut frames = Vec::with_capacity(POOL_FRAMES);
        let mut seen = [false; POOL_FRAMES];
        for _ in 0..POOL_FRAMES {
            let frame = self.alloc(&mut client);
            let index = self.frame_index(&frame);
            assert!(!seen[index], "allocator returned a duplicate frame");
            seen[index] = true;
            self.pool.assert_zero_frame(frame);
            frames.push(frame);
        }
        assert!(seen.iter().all(|&present| present));
        for frame in frames {
            self.dealloc(&mut client, frame);
        }
    }

    fn constants(&self) -> PTConstants {
        PTConstants {
            arch: PTArch(
                [FrameSize::Size1G, FrameSize::Size2M, FrameSize::Size4K]
                    .into_iter()
                    .map(|frame_size| PTArchLevel {
                        entry_count: 512,
                        frame_size,
                    })
                    .collect(),
            ),
            huge_pages: false,
            // Encode low simulated PAs, then translate back to host pointers
            // within PageTableMem, avoiding high host address bits in PTEs.
            hva_to_pa_offset: self.pool.base().checked_sub(TABLE_PA).unwrap(),
        }
    }

    pub fn new_table(&self) -> Table {
        Table::new(&self.allocator, self.constants())
    }

    pub fn destroy_table(&self, table: Table) {
        // This is the explicit PageTable trait method, not Rust's Drop.
        <Table as PageTable<BitAlloc1M>>::drop(table, &self.allocator);
    }

    #[inline]
    pub fn map(&self, table: &mut Table, mapping: &Mapping) -> MapResult {
        table.map(
            &self.allocator,
            VAddr(mapping.vaddr),
            Frame {
                base: mapping.paddr,
                size: mapping.size,
                attr: mapping.attr,
            },
        )
    }

    #[inline]
    pub fn unmap(&self, table: &mut Table, mapping: &Mapping) -> UnmapResult {
        table.unmap(&self.allocator, VAddr(mapping.vaddr))
    }

    #[inline]
    pub fn query(&self, table: &Table, addr: usize) -> QueryResult {
        table.query(VAddr(addr))
    }
}

pub fn allocation_size(_allocation: &Allocation) -> usize {
    PAGE_SIZE
}

pub struct Mapping {
    pub vaddr: usize,
    paddr: PAddr,
    size: FrameSize,
    attr: MemAttr,
}

pub fn mapping(index: usize) -> Mapping {
    Mapping {
        vaddr: VIRTUAL_BASE + index * PAGE_SIZE,
        // Leaf data addresses are encoded and checked, never dereferenced.
        paddr: PAddr(DATA_PA + index * PAGE_SIZE),
        size: FrameSize::Size4K,
        attr: MemAttr::new(true, true, false, false),
    }
}

fn check_frame(actual: &Frame, index: usize) {
    let expected = mapping(index);
    assert_eq!(actual.base.0, expected.paddr.0);
    assert!(actual.size == expected.size, "unexpected frame size");
    assert!(actual.attr == expected.attr, "unexpected frame attributes");
}

pub fn check_map(result: &MapResult) {
    assert!(result.is_ok(), "map failed");
}

pub fn check_unmap(result: &UnmapResult, index: usize) {
    check_frame(result.as_ref().expect("unmap failed"), index);
}

pub fn check_query(result: &QueryResult, index: usize, offset: usize) {
    assert!(offset < PAGE_SIZE, "query offset crosses frame boundary");
    let (base, frame) = result.as_ref().expect("query failed");
    assert_eq!(base.0, VIRTUAL_BASE + index * PAGE_SIZE);
    check_frame(frame, index);
}

pub fn check_missing(result: &QueryResult) {
    assert!(result.is_err(), "removed mapping still exists");
}
