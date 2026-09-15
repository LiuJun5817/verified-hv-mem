//! Host fixture for region and zone benchmarks of this checkout.
//!
//! Keep the workload and timing boundaries aligned with hvisor/tools/memory-bench.
//!
//! Region operations retain the production HvMem/zone locks, region metadata,
//! allocator and AArch64 page tables. Zone cases construct and destroy the
//! memory manager's CPU and IOMMU sets with an empty integration payload.
//! Platform maintenance callbacks are no-ops: these are host software costs,
//! excluding GIC/PCI initialization, cache maintenance and guest execution.

#[cfg(not(all(target_pointer_width = "64", target_endian = "little")))]
compile_error!("these AArch64 page-table benchmarks require a 64-bit little-endian host");

use std::{
    alloc::{alloc_zeroed, dealloc, handle_alloc_error, Layout},
    ptr::NonNull,
};

use verified_hv_mem::{
    address::{
        addr::{PAddr, VAddr},
        frame::{FrameSize, MemAttr},
    },
    bitmap_allocator::bitmap_impl::BitAlloc1M,
    global_allocator::GlobalAllocator,
    hardware::{HardwareInstr, MmuInstr, SmmuInstr, ZoneIdInstr},
    hv_mem::{protocol::BudgetProtocol, HvMem},
    memory_set::{MemorySet, VecMemorySet},
    page_table::{
        pt_arch::{PTArch, PTArchLevel},
        Aarch64PTE, ExPageTable, PTConstants, PageTable,
    },
};
use vstd::prelude::Tracked;

pub use verified_hv_mem::address::region::MemoryRegion as Mapping;
pub type OpResult = Result<(), ()>;
pub const PAGE_SIZE: usize = 4096;
pub const POOL_FRAMES: usize = 1024;
pub const MAX_REGIONS: usize = 4096;
pub const MAX_MAPPED_PAGES: usize = 32768;
pub const ZONE_ID: usize = 1;
const TABLE_PA: usize = 0x1000_0000;
const GUEST_BASE: usize = 0x1000_0000;
const DATA_PA: usize = 0x6000_0000;

// Empty hooks deliberately remove hardware costs. They add no counters,
// fences, allocation or dispatch to the measured operations.
struct HostHardware;
impl ZoneIdInstr for HostHardware {}
impl MmuInstr for HostHardware {
    fn issue_tlbi_s2_sync(_zone_id: usize, _ipa_page: usize) {}
    fn issue_tlbi_s2_range_sync(_zone_id: usize, _ipa_page: usize, _page_count: usize) {}
    fn issue_dsb_ish() {}
}
impl SmmuInstr for HostHardware {
    fn issue_smmu_tlbi_s2(_zone_id: usize, _ipa_page: usize) {}
    fn issue_smmu_tlbi_s2_range(_zone_id: usize, _ipa_page: usize, _page_count: usize) {}
    fn issue_smmu_sync() {}
}
impl HardwareInstr for HostHardware {}

type Allocator = GlobalAllocator<BitAlloc1M>;
type Table = ExPageTable<BitAlloc1M, Aarch64PTE>;
type Set = VecMemorySet<Table, BitAlloc1M, HostHardware>;
type Manager = HvMem<Table, Set, BitAlloc1M, BudgetProtocol, HostHardware, ()>;

struct Pool {
    ptr: NonNull<u8>,
    layout: Layout,
}

impl Pool {
    fn new() -> Self {
        let layout = Layout::from_size_align(POOL_FRAMES * PAGE_SIZE, PAGE_SIZE).unwrap();
        // SAFETY: a nonzero, page-aligned layout, owned until Pool::drop.
        let ptr = NonNull::new(unsafe { alloc_zeroed(layout) })
            .unwrap_or_else(|| handle_alloc_error(layout));
        let pool = Self { ptr, layout };
        for page in 0..POOL_FRAMES {
            // SAFETY: in-bounds, uniquely owned writes commit every page before
            // any timed operation. All allocator frames start zeroed.
            unsafe { pool.ptr.as_ptr().add(page * PAGE_SIZE).write_volatile(0) };
        }
        pool
    }

    fn base(&self) -> usize {
        self.ptr.as_ptr() as usize
    }

    fn frame_index(&self, address: PAddr) -> usize {
        let offset = address
            .0
            .checked_sub(self.base())
            .expect("frame below pool");
        assert!(offset < self.layout.size(), "frame outside pool");
        assert_eq!(offset % PAGE_SIZE, 0, "unaligned allocator frame");
        offset / PAGE_SIZE
    }

    fn check_zero(&self, index: usize) {
        assert!(index < POOL_FRAMES);
        // SAFETY: called only for a frame uniquely owned by the recovery check.
        let bytes = unsafe {
            std::slice::from_raw_parts(self.ptr.as_ptr().add(index * PAGE_SIZE), PAGE_SIZE)
        };
        assert!(
            bytes.iter().all(|&byte| byte == 0),
            "returned frame is not zeroed"
        );
    }
}

impl Drop for Pool {
    fn drop(&mut self) {
        // SAFETY: matching allocation/layout, after the manager was destroyed.
        unsafe { dealloc(self.ptr.as_ptr(), self.layout) };
    }
}

pub struct Fixture {
    // Drop order keeps pool backing alive throughout manager destruction.
    memory: Manager,
    pool: Pool,
}

impl Fixture {
    pub fn new() -> Self {
        let pool = Pool::new();
        let allocator = Allocator::default(PAddr(pool.base()));
        // The initial permission map is erased. This unverified host harness
        // supplies the actual zeroed, exclusively owned frames at runtime.
        allocator.init(POOL_FRAMES, Tracked::assume_new());
        let constants = PTConstants {
            arch: PTArch(
                [FrameSize::Size1G, FrameSize::Size2M, FrameSize::Size4K]
                    .into_iter()
                    .map(|frame_size| PTArchLevel {
                        entry_count: 512,
                        frame_size,
                    })
                    .collect(),
            ),
            // Keep every mapped page at 4 KiB regardless of region alignment
            // or length, matching the existing host page-table workload.
            huge_pages: false,
            // PTEs encode low simulated physical addresses; the production
            // PageTableMem translates them back to valid host pointers.
            hva_to_pa_offset: pool.base().checked_sub(TABLE_PA).unwrap(),
        };
        Self {
            memory: Manager::new(allocator, constants),
            pool,
        }
    }

    #[inline]
    pub fn add_empty_zone(&self) -> OpResult {
        self.memory.add_zone(ZONE_ID, ())
    }

    #[inline]
    pub fn insert(&self, mapping: &Mapping) -> OpResult {
        self.memory.insert_region(ZONE_ID, copy_mapping(mapping))
    }

    #[inline]
    pub fn remove(&self, mapping: &Mapping) -> OpResult {
        self.memory.remove_region(ZONE_ID, copy_mapping(mapping))
    }

    /// Create and populate both translation sets; RAM mappings are read/write.
    pub fn create_zone(&self, mappings: &[Mapping]) -> OpResult {
        self.add_empty_zone()?;
        for mapping in mappings {
            self.insert(mapping)?;
        }
        for mapping in mappings {
            self.memory
                .insert_iommu_region(ZONE_ID, copy_mapping(mapping))?;
        }
        Ok(())
    }

    /// Include unmapping and both page tables' explicit resource destruction.
    pub fn remove_zone(&self) -> OpResult {
        self.memory.clear(ZONE_ID)?;
        self.memory.clear_iommu(ZONE_ID)?;
        self.memory.remove_zone(ZONE_ID)
    }

    // The production library exposes vstd's legacy PCell interface.
    #[allow(deprecated)]
    fn with_sets(&self, check: impl FnOnce(&Set, &Set)) {
        let checked = self
            .memory
            .with_zone(ZONE_ID, |zone| {
                let guard = zone.lock.lock_read();
                // Only checks use these assumed, erased read permissions. Both
                // real read locks are held, all access is immutable, and Criterion
                // uses this fixture on one thread. No tracked state is mutated.
                let cpu = zone.cpu_mem_set.borrow(Tracked::assume_new());
                let iommu = zone.iommu_mem_set.borrow(Tracked::assume_new());
                // These native locks require explicit release. Catch check failures
                // until both locks are released so fixture teardown cannot deadlock.
                let checked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    check(cpu, iommu);
                }));
                zone.lock.unlock_read(guard);
                checked
            })
            .expect("benchmark zone is missing");
        if let Err(panic) = checked {
            std::panic::resume_unwind(panic);
        }
    }

    /// Check CPU metadata and actual page-table translations outside timing.
    pub fn check_mappings(&self, mappings: &[Mapping]) {
        self.with_sets(|cpu, iommu| {
            check_set(cpu, mappings);
            assert!(iommu.is_empty(), "region fixture has IOMMU mappings");
        });
    }

    pub fn check_zone(&self, mappings: &[Mapping]) {
        self.with_sets(|cpu, iommu| {
            check_set(cpu, mappings);
            check_set(iommu, mappings);
        });
    }

    pub fn check_empty(&self) {
        self.with_sets(|cpu, iommu| {
            assert!(cpu.is_empty(), "CPU regions were not removed");
            assert!(iommu.is_empty(), "IOMMU regions were not removed");
            assert!(cpu.pt.query(VAddr(GUEST_BASE)).is_err());
            assert!(iommu.pt.query(VAddr(GUEST_BASE)).is_err());
        });
    }

    pub fn check_removed(&self) {
        assert!(
            self.memory.with_zone(ZONE_ID, |_| ()).is_none(),
            "zone is still registered"
        );
    }

    /// Recover every pool frame, checking uniqueness, alignment and zeroing.
    /// The caller must remove the zone first. No extra exhausted allocation is
    /// attempted: this allocator's allocation API requires a nonempty pool.
    pub fn assert_all_frames_returned(&self) {
        self.check_removed();
        let mut token = self.memory.allocator.register_client();
        let mut frames = Vec::with_capacity(POOL_FRAMES);
        let mut seen = [false; POOL_FRAMES];
        for _ in 0..POOL_FRAMES {
            let (frame, next) = self.memory.allocator.alloc(token);
            token = next;
            let index = self.pool.frame_index(frame);
            assert!(!seen[index], "duplicate allocator frame");
            self.pool.check_zero(index);
            seen[index] = true;
            frames.push(frame);
        }
        assert!(seen.iter().all(|&present| present));
        for frame in frames {
            token = self.memory.allocator.dealloc(token, frame);
        }
    }
}

impl Default for Fixture {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        // HvMem uses explicit page-table destruction. Also clean up if a
        // caller leaves the last fixture populated before normal destruction.
        if self.memory.with_zone(ZONE_ID, |_| ()).is_some() {
            self.remove_zone().expect("fixture zone cleanup failed");
        }
    }
}

pub fn mapping(index: usize, pages: usize) -> Mapping {
    assert!(index < MAX_REGIONS, "too many regions");
    assert!(
        (1..=MAX_MAPPED_PAGES).contains(&pages),
        "invalid region page count"
    );
    let end_page = (index + 1).checked_mul(pages).unwrap();
    assert!(
        end_page <= MAX_MAPPED_PAGES,
        "mapping exceeds the 128 MiB test range"
    );
    let offset = index * pages * PAGE_SIZE;
    let region = Mapping {
        vstart: VAddr(GUEST_BASE + offset),
        pstart: PAddr(DATA_PA + offset),
        pages,
        attr: MemAttr::new(true, true, false, false),
    };
    assert!(region.valid());
    region
}

#[inline]
fn copy_mapping(mapping: &Mapping) -> Mapping {
    Mapping {
        vstart: mapping.vstart,
        pstart: mapping.pstart,
        pages: mapping.pages,
        attr: mapping.attr,
    }
}

fn check_set(set: &Set, mappings: &[Mapping]) {
    assert_eq!(set.regions.len(), mappings.len(), "unexpected region count");
    for mapping in mappings {
        for offset in [0, mapping.pages * PAGE_SIZE - 1] {
            let vaddr = VAddr(mapping.vstart.0 + offset);
            let (paddr, attr) = set.query_vaddr(vaddr).expect("region metadata missing");
            assert_eq!(paddr.0, mapping.pstart.0 + offset);
            assert!(attr == mapping.attr, "wrong region attributes");
            let (base, frame) = set.pt.query(vaddr).expect("page-table mapping missing");
            assert_eq!(base.0, vaddr.0 & !(PAGE_SIZE - 1));
            assert_eq!(frame.base.0 + (vaddr.0 - base.0), paddr.0);
            assert!(frame.size == FrameSize::Size4K, "unexpected huge page");
            assert!(frame.attr == mapping.attr, "wrong page-table attributes");
        }
    }
}
