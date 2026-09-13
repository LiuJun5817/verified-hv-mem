//! Host software benchmarks: one Criterion iteration is 100 successful operations.
//! Run with `cargo bench --bench memory_ops`; see benches/README.md for boundaries.

use std::{
    alloc::{alloc_zeroed, dealloc, handle_alloc_error, Layout},
    hint::black_box,
    ptr::NonNull,
    time::{Duration, Instant},
};

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use verified_hv_mem::{
    address::{
        addr::{PAddr, VAddr},
        frame::{Frame, FrameSize, MemAttr},
    },
    bitmap_allocator::bitmap_impl::BitAlloc1M,
    global_allocator::GlobalAllocator,
    page_table::{
        pt_arch::{PTArch, PTArchLevel},
        Aarch64PTE, ExPageTable, PTConstants, PageTable,
    },
};
use vstd::prelude::Tracked;

const PAGE_SIZE: usize = 4096;
const POOL_FRAMES: usize = 1024;
const OPERATIONS: usize = 100;
const TABLE_PA: usize = 0x1000_0000;
const VIRTUAL_BASE: usize = 0x1000_0000;
const DATA_PA: usize = 0x6000_0000;

type Allocator = GlobalAllocator<BitAlloc1M>;
type HostPageTable = ExPageTable<BitAlloc1M, Aarch64PTE>;

/// Own the real memory dereferenced by the page-table implementation.
struct Pool {
    ptr: NonNull<u8>,
    layout: Layout,
}

impl Pool {
    fn new() -> Self {
        let layout = Layout::from_size_align(POOL_FRAMES * PAGE_SIZE, PAGE_SIZE).unwrap();
        // SAFETY: a nonzero, page-aligned layout; allocation is uniquely owned below.
        let ptr = NonNull::new(unsafe { alloc_zeroed(layout) })
            .unwrap_or_else(|| handle_alloc_error(layout));
        let pool = Self { ptr, layout };
        for page in 0..POOL_FRAMES {
            // SAFETY: each address lies in the owned allocation. Commit every page
            // before timing; the allocator requires all initial frame bytes to be zero.
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
        // SAFETY: checked in-pool frame; callers read only while no operation
        // mutates this frame. All allocation bytes were initialized by alloc_zeroed.
        let bytes = unsafe {
            std::slice::from_raw_parts(self.ptr.as_ptr().add(index * PAGE_SIZE), PAGE_SIZE)
        };
        assert!(bytes.iter().all(|&byte| byte == 0), "frame was not cleared");
    }
}

impl Drop for Pool {
    fn drop(&mut self) {
        // SAFETY: matching allocation/layout; the allocator and page table have
        // already been dropped before their backing pool on the normal path.
        unsafe { dealloc(self.ptr.as_ptr(), self.layout) };
    }
}

struct Fixture {
    // Field drop order keeps the backing allocation alive until after the allocator.
    allocator: Allocator,
    pool: Pool,
}

impl Fixture {
    fn new() -> Self {
        let pool = Pool::new();
        let allocator = Allocator::default(PAddr(pool.base()));
        // Runtime-only harness: pool supplies real, zeroed frames. Only the
        // erased Verus permission map is assumed; library code is unchanged.
        allocator.init(POOL_FRAMES, Tracked::assume_new());
        Self { allocator, pool }
    }

    /// Check ownership recovery, uniqueness, bounds and zeroing outside timing.
    /// Call only when no page table or allocated frame remains live.
    fn assert_all_frames_returned(&self) {
        let mut client = self.allocator.register_client();
        let mut frames = Vec::with_capacity(POOL_FRAMES);
        let mut seen = [false; POOL_FRAMES];
        for _ in 0..POOL_FRAMES {
            let (frame, next) = self.allocator.alloc(client);
            client = next;
            let index = self.pool.frame_index(frame);
            assert!(!seen[index], "allocator returned a duplicate frame");
            seen[index] = true;
            self.pool.assert_zero_frame(frame);
            frames.push(frame);
        }
        assert!(seen.iter().all(|&present| present));
        for frame in frames {
            client = self.allocator.dealloc(client, frame);
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
            // Encode low simulated PAs, then translate back to real host pointers
            // inside PageTableMem. This avoids encoding high host address bits.
            hva_to_pa_offset: self.pool.base().checked_sub(TABLE_PA).unwrap(),
        }
    }
}

fn vaddr(index: usize) -> VAddr {
    VAddr(VIRTUAL_BASE + index * PAGE_SIZE)
}

fn frame(index: usize) -> Frame {
    Frame {
        // Leaf data addresses are only encoded/query-checked, never dereferenced.
        base: PAddr(DATA_PA + index * PAGE_SIZE),
        size: FrameSize::Size4K,
        attr: MemAttr::new(true, true, false, false),
    }
}

fn check_frame(actual: &Frame, index: usize) {
    let expected = frame(index);
    assert_eq!(actual.base.0, expected.base.0);
    assert!(actual.size == expected.size);
    assert!(actual.attr == expected.attr);
}

fn prepare_mappings(pt: &mut HostPageTable, allocator: &Allocator) {
    for index in 0..OPERATIONS {
        pt.map(allocator, vaddr(index), frame(index))
            .expect("map failed");
    }
}

fn clear_mappings(pt: &mut HostPageTable, allocator: &Allocator) {
    for index in 0..OPERATIONS {
        let removed = pt.unmap(allocator, vaddr(index)).expect("unmap failed");
        check_frame(&removed, index);
    }
}

fn allocator_benches(c: &mut Criterion) {
    let fixture = Fixture::new();
    fixture.assert_all_frames_returned();
    let allocator = black_box(&fixture.allocator);
    let mut group = c.benchmark_group("allocator");
    group.throughput(Throughput::Elements(OPERATIONS as u64));

    group.bench_function(BenchmarkId::new("alloc", OPERATIONS), |b| {
        b.iter_custom(|rounds| {
            let mut client = allocator.register_client();
            let mut frames = [PAddr(0); OPERATIONS];
            let mut elapsed = Duration::ZERO;
            for _ in 0..rounds {
                let start = Instant::now();
                for slot in &mut frames {
                    let (allocated, next) = allocator.alloc(client);
                    client = next;
                    *slot = allocated;
                }
                elapsed += start.elapsed();
                black_box(&frames);
                // Reset outside timing; never benchmark allocator exhaustion.
                for &allocated in &frames {
                    client = allocator.dealloc(client, allocated);
                }
            }
            elapsed
        });
    });

    group.bench_function(BenchmarkId::new("dealloc", OPERATIONS), |b| {
        b.iter_custom(|rounds| {
            let mut client = allocator.register_client();
            let mut frames = [PAddr(0); OPERATIONS];
            let mut elapsed = Duration::ZERO;
            for _ in 0..rounds {
                for slot in &mut frames {
                    let (allocated, next) = allocator.alloc(client);
                    client = next;
                    *slot = allocated;
                }
                let input = black_box(&frames);
                let start = Instant::now();
                for &allocated in input {
                    client = allocator.dealloc(client, allocated);
                }
                elapsed += start.elapsed();
                black_box(allocator);
            }
            elapsed
        });
    });
    group.finish();
    fixture.assert_all_frames_returned();
}

fn page_table_benches(c: &mut Criterion) {
    let fixture = Fixture::new();
    let allocator = black_box(&fixture.allocator);
    let mut pt = HostPageTable::new(allocator, fixture.constants());
    let root_hva = PAddr(pt.root().0 + fixture.constants().hva_to_pa_offset);

    // Check the real library path, translation, repeated reuse and empty root
    // before collecting samples. These checks are not part of measured work.
    for _ in 0..2 {
        prepare_mappings(&mut pt, allocator);
        for index in 0..OPERATIONS {
            let (base, actual) = pt.query(VAddr(vaddr(index).0 + 17)).unwrap();
            assert_eq!(base.0, vaddr(index).0);
            check_frame(&actual, index);
        }
        clear_mappings(&mut pt, allocator);
        for index in 0..OPERATIONS {
            assert!(pt.query(vaddr(index)).is_err());
        }
        fixture.pool.assert_zero_frame(root_hva);
    }

    let mut group = c.benchmark_group("page_table");
    group.throughput(Throughput::Elements(OPERATIONS as u64));
    group.bench_function(BenchmarkId::new("map_page", OPERATIONS), |b| {
        b.iter_custom(|rounds| {
            let mut results = [Ok(()); OPERATIONS];
            let mut elapsed = Duration::ZERO;
            for _ in 0..rounds {
                let start = Instant::now();
                for (index, result) in results.iter_mut().enumerate() {
                    *result = pt.map(allocator, black_box(vaddr(index)), black_box(frame(index)));
                }
                elapsed += start.elapsed();
                assert!(black_box(&results).iter().all(Result::is_ok), "map failed");
                clear_mappings(&mut pt, allocator);
            }
            elapsed
        });
    });

    group.bench_function(BenchmarkId::new("unmap_page", OPERATIONS), |b| {
        b.iter_custom(|rounds| {
            let mut results: [Result<Frame, ()>; OPERATIONS] = std::array::from_fn(|_| Err(()));
            let mut elapsed = Duration::ZERO;
            for _ in 0..rounds {
                prepare_mappings(&mut pt, allocator);
                let start = Instant::now();
                for (index, result) in results.iter_mut().enumerate() {
                    *result = pt.unmap(allocator, black_box(vaddr(index)));
                }
                elapsed += start.elapsed();
                for (index, result) in black_box(&results).iter().enumerate() {
                    check_frame(result.as_ref().expect("unmap failed"), index);
                }
            }
            elapsed
        });
    });

    // Query hits in an already populated table; setup and teardown are excluded.
    // Keep the same mappings across samples because query does not mutate them.
    prepare_mappings(&mut pt, allocator);
    group.bench_function(BenchmarkId::new("query", OPERATIONS), |b| {
        let table = black_box(&pt);
        b.iter_custom(|rounds| {
            let mut results: [Result<(VAddr, Frame), ()>; OPERATIONS] =
                std::array::from_fn(|_| Err(()));
            let mut elapsed = Duration::ZERO;
            for _ in 0..rounds {
                let start = Instant::now();
                for (index, result) in results.iter_mut().enumerate() {
                    // Use an in-page offset to exercise query's containing-page lookup.
                    *result = table.query(black_box(VAddr(vaddr(index).0 + 17)));
                }
                elapsed += start.elapsed();
                for (index, result) in black_box(&results).iter().enumerate() {
                    let (base, actual) = result.as_ref().expect("query failed");
                    assert_eq!(base.0, vaddr(index).0);
                    check_frame(actual, index);
                }
            }
            elapsed
        });
    });
    clear_mappings(&mut pt, allocator);
    group.finish();
    fixture.pool.assert_zero_frame(root_hva);
    // PageTable::drop is an explicit trait method, not Rust's automatic Drop.
    <HostPageTable as PageTable<BitAlloc1M>>::drop(pt, allocator);
    fixture.assert_all_frames_returned();
}

criterion_group! {
    name = benches;
    config = Criterion::default()
        .sample_size(100)
        .warm_up_time(Duration::from_secs(3))
        .measurement_time(Duration::from_secs(10))
        .confidence_level(0.95);
    targets = allocator_benches, page_table_benches
}
criterion_main!(benches);
