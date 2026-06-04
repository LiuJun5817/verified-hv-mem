//! A memory set is a collection of memory areas that can be mapped into the virtual address
//! space of a zone (process). It manages the page table for the zone, and provides methods to
//! insert, remove, and find memory areas.
use crate::{
    address::{
        addr::{SpecPAddr, SpecVAddr, VAddr},
        frame::{self, Frame, FrameSize, SpecFrame},
        region::{MemoryRegion, PAGE_SIZE, SPEC_PAGE_SIZE},
    },
    bitmap_allocator::bitmap_trait::BitmapAllocator,
    global_allocator::GlobalAllocator,
    page_table::{PTConstants, PageTable},
};
use std::marker::PhantomData;
use vstd::prelude::*;
use vstd::tokens::InstanceId;

mod vec;

verus! {

/// Abstract state of a memory set: the regions **and** the page-table mappings
/// they induce.
pub struct SpecMemorySet {
    /// The set of memory regions in the memory set.
    pub regions: Set<MemoryRegion>,
    /// The page table: the real virtual→physical-frame mapping.  `wf()` pins this
    /// to be *exactly* the dense per-page mapping of `regions`.
    pub mappings: Map<SpecVAddr, SpecFrame>,
}

impl SpecMemorySet {
    /// Well-formedness.
    pub open spec fn wf(&self) -> bool {
        // Regions are valid
        &&& forall|r: MemoryRegion| #[trigger]
            self.regions.contains(r)
                ==> r.spec_valid()
        // Regions do not overlap
        &&& forall|r1: MemoryRegion, r2: MemoryRegion| #[trigger]
            self.regions.contains(r1) && #[trigger] self.regions.contains(r2) && r1 != r2
                ==> !r1.spec_overlaps_vmem(
                r2,
            )
            // Exact-dense consistency (completeness): every region page is mapped to
            // exactly its frame.
        &&& forall|r: MemoryRegion, i: nat|
            #![trigger self.regions.contains(r), r.spec_page_vaddr(i)]
            self.regions.contains(r) && 0 <= i < r.pages ==> self.mappings.contains_pair(
                r.spec_page_vaddr(i),
                r.spec_frame(i),
            )
        // Exact-dense consistency (soundness): every mapping is exactly some
        // region page's frame.
        &&& forall|v: SpecVAddr, f: SpecFrame| #[trigger]
            self.mappings.contains_pair(v, f) ==> exists|r: MemoryRegion, i: nat|
                #![trigger self.regions.contains(r), r.spec_page_vaddr(i)]
                self.regions.contains(r) && 0 <= i < r.pages && v == r.spec_page_vaddr(i) && f
                    == r.spec_frame(i)
    }

    /// Check if a virtual address is mapped in the memory set.
    pub open spec fn contains_vaddr(&self, v: SpecVAddr) -> bool {
        exists|r: MemoryRegion| self.regions.contains(r) && #[trigger] r.spec_contains_vaddr(v)
    }

    /// Check if a region starts at the given virtual address is mapped in the memory set.
    pub open spec fn has_region_starting_at(&self, v: SpecVAddr) -> bool {
        exists|r: MemoryRegion| self.regions.contains(r) && #[trigger] r.start@ == v
    }

    /// Check if a region overlaps with any existing region in virtual address space.
    pub open spec fn overlaps_vmem(&self, region: MemoryRegion) -> bool {
        exists|r: MemoryRegion| self.regions.contains(r) && #[trigger] r.spec_overlaps_vmem(region)
    }

    /// Translate a virtual address in the memory set to a physical address, if it is mapped.
    pub open spec fn translate(&self, v: SpecVAddr) -> SpecPAddr
        recommends
            self.contains_vaddr(v),
    {
        let r = choose|r: MemoryRegion|
            self.regions.contains(r) && #[trigger] r.spec_contains_vaddr(v);
        r.spec_translate(v)
    }

    /// Insert a new region into the memory set, returning the new memory set.
    pub open spec fn insert_region(&self, region: MemoryRegion) -> Self {
        Self {
            regions: self.regions.insert(region),
            mappings: self.mappings.union_prefer_right(region.spec_mappings()),
        }
    }

    /// Remove a region starting at the given virtual address from the memory set, returning the new memory set.
    pub open spec fn remove_region(&self, start: SpecVAddr) -> Self {
        let removed = choose|r: MemoryRegion| #[trigger]
            self.regions.contains(r) && r.start@ == start;
        Self {
            regions: self.regions.remove(removed),
            mappings: self.mappings.remove_keys(removed.spec_mappings().dom()),
        }
    }
}

/// Specification of a memory set viewed by higher-level components.
pub trait MemorySet<PT, A> where PT: PageTable<A>, A: BitmapAllocator, Self: Sized {
    /// View the memory set as a list of memory regions.
    spec fn view(&self) -> SpecMemorySet;

    /// Invariants that must be implied at initial state and preseved after each operation.
    spec fn invariants(&self) -> bool;

    /// Instance ID of the allocator this memory set is associated with.
    spec fn inst_id(&self) -> InstanceId;

    /// Check if a region overlaps with any existing region in virtual address space.
    fn overlaps_vmem(&self, region: &MemoryRegion) -> (res: bool)
        requires
            self.invariants(),
            region.spec_valid(),
        ensures
            res == self@.overlaps_vmem(*region),
    ;

    /// Check if a region starts at the given virtual address is mapped in the memory set.
    fn has_region_starting_at(&self, v: VAddr) -> (res: bool)
        requires
            self.invariants(),
        ensures
            res == self@.has_region_starting_at(v@),
    ;

    /// Create an empty memory set with the given instance ID.
    fn new(allocator: &GlobalAllocator<A>, pt_constants: PTConstants) -> (res: Self)
        requires
            allocator.invariants(),
            pt_constants@.valid(),
            pt_constants@.arch.leaf_frame_size() == FrameSize::Size4K,
            forall|level: nat|
                level < pt_constants.arch@.level_count() ==> pt_constants.arch@.entry_count(level)
                    == 512,
        ensures
            res@.regions == Set::<MemoryRegion>::empty(),
            res@.mappings == Map::<SpecVAddr, SpecFrame>::empty(),
            res.inst_id() == allocator.inst_id(),
            res.invariants(),
    ;

    /// Insert a new memory region into the memory set.
    fn insert(&mut self, allocator: &GlobalAllocator<A>, region: MemoryRegion)
        requires
            old(self).invariants(),
            allocator.invariants(),
            old(self).inst_id() == allocator.inst_id(),
            region.spec_valid(),
            !old(self)@.overlaps_vmem(region),
        ensures
            self.inst_id() == old(self).inst_id(),
            self@ == old(self)@.insert_region(region),
            self.invariants(),
    ;

    /// Remove a memory region from the memory set by its starting virtual address.
    fn remove(&mut self, allocator: &GlobalAllocator<A>, start: VAddr)
        requires
            old(self).invariants(),
            allocator.invariants(),
            old(self).inst_id() == allocator.inst_id(),
            old(self)@.has_region_starting_at(start@),
        ensures
            self.inst_id() == old(self).inst_id(),
            self@ == old(self)@.remove_region(start@),
            self.invariants(),
    ;

    /// Lemma. The invariants imply the well-formedness of the memory set.
    proof fn lemma_invariants_implies_wf(self)
        requires
            self.invariants(),
        ensures
            self.view().wf(),
    ;
}

} // verus!
