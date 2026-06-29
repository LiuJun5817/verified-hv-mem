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
use core::marker::PhantomData;
use vstd::prelude::*;
use vstd::tokens::InstanceId;

verus! {

broadcast use crate::page_table::PageTable::lemma_invariants_implies_wf;

/// Abstract state of a memory set, which is a collection of memory regions.
/// Each region represents a contiguous range of virtual addresses.
pub struct SpecMemorySet {
    /// The set of memory regions in the memory set.
    pub regions: Set<MemoryRegion>,
}

impl SpecMemorySet {
    /// Well-formedness.
    pub open spec fn wf(&self) -> bool {
        // Regions are valid
        &&& forall|r: MemoryRegion|
            #[trigger] self.regions.contains(r)
                ==> r.spec_valid()
        // Regions do not overlap
        &&& forall|r1: MemoryRegion, r2: MemoryRegion|
            #[trigger] self.regions.contains(r1) && #[trigger] self.regions.contains(r2) && r1 != r2
                ==> !r1.spec_overlaps_vmem(r2)
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
            self@.regions == old(self)@.regions.insert(region),
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
            self@.regions == old(self)@.regions.remove(
                choose|r: MemoryRegion| #[trigger]
                    old(self)@.regions.contains(r) && r.start@ == start@,
            ),
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

/// Memory set implementation using a vector of memory regions.
pub struct VecMemorySet<PT, A> where PT: PageTable<A>, A: BitmapAllocator {
    /// The list of memory regions in the memory set.
    pub regions: Vec<MemoryRegion>,
    /// Page table managing the mappings.
    pub pt: PT,
    /// Phantom data for the page table memory type.
    pub phantom: PhantomData<A>,
}

impl<PT, A> VecMemorySet<PT, A> where PT: PageTable<A>, A: BitmapAllocator {
    /// If a region is mapped in the page table.
    ///
    /// TODO: For now we only support 4KB pages, so we use `mappings.contains_key` to simplify the proof.
    /// In the future if we want to support huge pages, we may use `pt.has_mapping_for` instead.
    pub open spec fn has_mapping_for(&self, region: MemoryRegion) -> bool {
        forall|i: nat|
            i < region.pages ==> #[trigger] self.pt.view().mappings.contains_key(
                region.start@.offset(i * SPEC_PAGE_SIZE),
            )
    }

    /// If there is region contains the given virtual frame.
    pub open spec fn has_region_for_frame(&self, vbase: SpecVAddr, frame: SpecFrame) -> bool {
        exists|i: int|
            0 <= i < self.regions.len() && #[trigger] SpecVAddr::interval_subset(
                vbase,
                frame.size.as_nat(),
                self.regions[i].start@,
                self.regions[i].pages as nat * SPEC_PAGE_SIZE,
            )
    }

    /// If there is region other than `ridx` contains the given virtual frame.
    pub open spec fn has_region_for_frame_except(
        &self,
        vbase: SpecVAddr,
        frame: SpecFrame,
        ridx: int,
    ) -> bool {
        exists|i: int|
            0 <= i < self.regions.len() && i != ridx && #[trigger] SpecVAddr::interval_subset(
                vbase,
                frame.size.as_nat(),
                self.regions[i].start@,
                self.regions[i].pages as nat * SPEC_PAGE_SIZE,
            )
    }

    /// Lemma: two regions cannot have the same starting virtual address.
    proof fn lemma_region_start_unique(self)
        requires
            self.invariants(),
        ensures
            forall|i: int, j: int|
                #![auto]
                0 <= i < self.regions.len() && 0 <= j < self.regions.len() && i != j
                    ==> self.regions[i].start@ != self.regions[j].start@,
    {
        if exists|i: int, j: int|
            #![auto]
            0 <= i < self.regions.len() && 0 <= j < self.regions.len() && i != j
                && self.regions[i].start@ == self.regions[j].start@ {
            let (i, j) = choose|i: int, j: int|
                #![auto]
                0 <= i < self.regions.len() && 0 <= j < self.regions.len() && i != j
                    && self.regions[i].start@ == self.regions[j].start@;
            assert(self.regions[i].spec_valid());
            assert(self.regions[j].spec_valid());
            assert(self.regions[i].spec_overlaps_vmem(self.regions[j]));
        }
    }
}

impl<PT, A> MemorySet<PT, A> for VecMemorySet<PT, A> where PT: PageTable<A>, A: BitmapAllocator {
    open spec fn view(&self) -> SpecMemorySet {
        SpecMemorySet {
            regions: Set::new(
                |r: MemoryRegion|
                    exists|i: int| 0 <= i < self.regions.len() && self.regions[i] == r,
            ),
        }
    }

    open spec fn inst_id(&self) -> InstanceId {
        self.pt.inst_id()
    }

    open spec fn invariants(&self) -> bool {
        &&& self.pt.view().constants.valid()
        // Frame size is 4K
        &&& self.pt.view().constants.arch.leaf_frame_size()
            == FrameSize::Size4K
        // Page table invariants
        &&& self.pt.invariants()
        // Regions are valid
        &&& forall|i: int|
            0 <= i < self.regions.len()
                ==> #[trigger] self.regions[i].spec_valid()
        // Regions do not overlap
        &&& forall|i: int, j: int|
            0 <= i < self.regions.len() && 0 <= j < self.regions.len() && i != j
                ==> !self.regions[i].spec_overlaps_vmem(
                self.regions[j],
            )
            // Page table contains mappings only within these regions
        &&& forall|vbase: SpecVAddr, frame: SpecFrame| #[trigger]
            self.pt.view().mappings.contains_pair(vbase, frame) ==> self.has_region_for_frame(
                vbase,
                frame,
            )
        // All regions are mapped in the page table
        &&& forall|i: int|
            0 <= i < self.regions.len() ==> #[trigger] self.has_mapping_for(self.regions[i])
    }

    fn new(allocator: &GlobalAllocator<A>, pt_constants: PTConstants) -> (res: Self) {
        let pt = PT::new(allocator, pt_constants);
        VecMemorySet { regions: Vec::new(), pt, phantom: PhantomData }
    }

    fn overlaps_vmem(&self, region: &MemoryRegion) -> (res: bool) {
        for i in 0..self.regions.len()
            invariant
                0 <= i <= self.regions.len(),
                region.spec_valid(),
                self.invariants(),
                forall|j: int| #![auto] 0 <= j < i ==> !self.regions[j].spec_overlaps_vmem(*region),
        {
            let r = &self.regions[i];
            if r.overlaps_vmem(region) {
                return true;
            }
        }
        false
    }

    fn has_region_starting_at(&self, v: VAddr) -> (res: bool) {
        for i in 0..self.regions.len()
            invariant
                0 <= i <= self.regions.len(),
                self.invariants(),
                forall|j: int| #![auto] 0 <= j < i ==> self.regions[j].start@ != v@,
        {
            let r = &self.regions[i];
            if r.start.0 == v.0 {
                return true;
            }
        }
        false
    }

    fn insert(&mut self, allocator: &GlobalAllocator<A>, region: MemoryRegion) {
        // New region does not overlap with old regions
        assert(forall|j: int|
            #![auto]
            0 <= j < self.regions.len() ==> !self.regions[j].spec_overlaps_vmem(region));
        assert forall|j: int|
            #![auto]
            0 <= j < self.regions.len() implies !region.spec_overlaps_vmem(self.regions[j]) by {
            self.regions[j].lemma_overlaps_vmem_symmetric(region);
        };

        // Map the region in the page table
        let mut i: usize = 0;
        while i < region.pages
            invariant
                region.spec_valid(),
                i <= region.pages,
                self.pt.invariants(),
                self.pt.inst_id() == allocator.inst_id(),
                allocator.invariants(),
                self.pt.view().constants == old(self).pt.view().constants,
                self.pt.view().constants.valid(),
                self.pt.view().constants.arch.leaf_frame_size() == FrameSize::Size4K,
                self.regions == old(self).regions,
                old(self).invariants(),
                // Old regions do not overlap with each other
                forall|j: int|
                    0 <= j < self.regions.len() ==> !region.spec_overlaps_vmem(
                        #[trigger] self.regions[j],
                    ),
                // New region does not overlap with any old region
                !self@.overlaps_vmem(region),
                // The first `i` pages of the new region are mapped in the page table
                forall|j: nat|
                    j < i ==> #[trigger] self.pt.view().mappings.contains_key(
                        region.start@.offset(j * SPEC_PAGE_SIZE),
                    ),
                // All mappings in the page table are within old regions or the first `i` pages of the new region
                forall|vbase2: SpecVAddr, frame2: SpecFrame| #[trigger]
                    self.pt.view().mappings.contains_pair(vbase2, frame2)
                        ==> self.has_region_for_frame(vbase2, frame2) || SpecVAddr::interval_subset(
                        vbase2,
                        frame2.size.as_nat(),
                        region.start@,
                        i as nat * SPEC_PAGE_SIZE,
                    ),
                // Old regions are mapped in the page table
                forall|j: int|
                    0 <= j < self.regions.len() ==> #[trigger] self.has_mapping_for(
                        self.regions[j],
                    ),
            decreases region.pages - i,
        {
            let vaddr = VAddr(region.start.0 + i * PAGE_SIZE);
            let paddr = region.mapper.map(vaddr);
            // TODO: support huge pages
            let frame = Frame { base: paddr, size: FrameSize::Size4K, attr: region.attr.clone() };

            proof {
                assert(vaddr@.within(region.start@, region.pages as nat * SPEC_PAGE_SIZE));
                // vaddr not within any existing region
                assert forall|j: int| #![auto] 0 <= j < self.regions.len() implies !vaddr@.within(
                    self.regions[j].start@,
                    self.regions[j].pages as nat * SPEC_PAGE_SIZE,
                ) by {
                    let r = self.regions[j];
                    assert(!region.spec_overlaps_vmem(r));
                    if vaddr@.within(r.start@, r.pages as nat * SPEC_PAGE_SIZE) {
                        assert(region.spec_overlaps_vmem(r));
                    }
                };
                // (vaddr, frame) does not overlap with any existing region
                assert(forall|j: int|
                    #![auto]
                    0 <= j < self.regions.len() ==> !SpecVAddr::overlap(
                        vaddr@,
                        frame.size.as_nat(),
                        self.regions[j].start@,
                        self.regions[j].pages as nat * SPEC_PAGE_SIZE,
                    ));

                if i > 0 {
                    // vaddr not within the already mapped part of the new region
                    assert(!vaddr@.within(region.start@, (i - 1) as nat * SPEC_PAGE_SIZE));
                    // (vaddr, frame) does not overlap with the already mapped part of the new region
                    assert(!SpecVAddr::overlap(
                        vaddr@,
                        frame.size.as_nat(),
                        region.start@,
                        (i - 1) as nat * SPEC_PAGE_SIZE,
                    ));
                }
                let mappings = self.pt.view().mappings;
                // (vaddr, frame) does not overlap with any existing mapping
                assert forall|vbase2: SpecVAddr| #[trigger]
                    mappings.contains_key(vbase2) implies !SpecVAddr::overlap(
                    vbase2,
                    mappings[vbase2].size.as_nat(),
                    vaddr@,
                    frame.size.as_nat(),
                ) by {
                    assert(mappings.contains_pair(vbase2, mappings[vbase2]));
                    assert(self.pt.view().has_mapping_for(vbase2));
                    if i == 0 {
                        // (vbase2, frame2) is within some existing region
                        assert(self.has_region_for_frame(vbase2, mappings[vbase2]));
                    } else {
                        // (vbase2, frame2) is within some existing region or the already mapped part of the new region
                        assert(self.has_region_for_frame(vbase2, mappings[vbase2])
                            || SpecVAddr::interval_subset(
                            vbase2,
                            mappings[vbase2].size.as_nat(),
                            region.start@,
                            i as nat * SPEC_PAGE_SIZE,
                        ));
                    }
                    assert(!SpecVAddr::overlap(
                        vbase2,
                        self.pt.view().mappings[vbase2].size.as_nat(),
                        vaddr@,
                        frame.size.as_nat(),
                    ));
                }
                assert(!self.pt.view().overlaps_vmem(vaddr@, frame@));
            }
            // TODO: edit precondition to require the new region is within the address space limit
            assume(vaddr@.0 < self.pt.view().constants.arch.vspace_size());

            let ghost old_self = *self;
            let ghost old_mappings = self.pt.view().mappings;
            let res = self.pt.map(allocator, vaddr, frame);
            let ghost mappings = self.pt.view().mappings;
            i += 1;

            proof {
                // Prove loop invariants
                assert(self.pt.invariants());
                assert(res.is_ok());
                assert(mappings == old_mappings.insert(vaddr@, frame@));
                assert(mappings.contains_pair(vaddr@, frame@));
                // The first `i` pages of the new region are mapped in the page table
                assert forall|j: nat| j < i implies #[trigger] self.pt.view().mappings.contains_key(
                    region.start@.offset(j * SPEC_PAGE_SIZE),
                ) by {
                    let vaddr2 = region.start@.offset(j * SPEC_PAGE_SIZE);
                    if j == i - 1 {
                        assert(vaddr2 == vaddr@);
                    } else {
                        assert(old_mappings.contains_key(vaddr2));
                    }
                }
                // All mappings in the page table are within old regions or the first `i` pages of the new region
                assert forall|vbase2: SpecVAddr, frame2: SpecFrame| #[trigger]
                    mappings.contains_pair(vbase2, frame2) implies self.has_region_for_frame(
                    vbase2,
                    frame2,
                ) || SpecVAddr::interval_subset(
                    vbase2,
                    frame2.size.as_nat(),
                    region.start@,
                    i as nat * SPEC_PAGE_SIZE,
                ) by {
                    if old_mappings.contains_pair(vbase2, frame2) {
                        assert(self.has_region_for_frame(vbase2, frame2)
                            || SpecVAddr::interval_subset(
                            vbase2,
                            frame2.size.as_nat(),
                            region.start@,
                            (i - 1) as nat * SPEC_PAGE_SIZE,
                        ));
                    } else {
                        assert(vbase2 == vaddr@ && frame2 == frame@);
                        assert(SpecVAddr::interval_subset(
                            vaddr@,
                            frame@.size.as_nat(),
                            region.start@,
                            i as nat * SPEC_PAGE_SIZE,
                        ));
                    }
                }
                // Old regions are still mapped in the page table
                assert forall|j: int|
                    0 <= j < self.regions.len() implies #[trigger] self.has_mapping_for(
                    self.regions[j],
                ) by {
                    let region = self.regions[j];
                    assert(old_self.has_mapping_for(region));
                }
            }
        }

        // After the loop, the whole region is mapped in the page table
        assert(self.has_mapping_for(region));
        // Push the region into the list
        let ghost old_self = *self;
        self.regions.push(region);

        proof {
            assert forall|r: MemoryRegion| #[trigger]
                self@.regions.contains(r) <==> old(self)@.regions.insert(region).contains(r) by {
                if self@.regions.contains(r) {
                    let i = choose|i: int| 0 <= i < self.regions.len() && self.regions[i] == r;
                    if i < old(self).regions.len() {
                        assert(old(self).regions[i] == r);
                    } else {
                        assert(r == region);
                    }
                }
                if old(self)@.regions.insert(region).contains(r) {
                    if old(self)@.regions.contains(r) {
                        let i = choose|i: int|
                            0 <= i < old(self).regions.len() && old(self).regions[i] == r;
                        assert(self.regions[i] == r);
                    } else {
                        assert(r == region);
                        assert(self.regions[old(self).regions.len() as int] == region);
                    }
                }
            };
            // Prove invariants
            // All regions are still valid
            assert forall|i: int|
                0 <= i < self.regions.len() implies #[trigger] self.regions[i].spec_valid() by {
                if i < self.regions.len() - 1 {
                    assert(self.regions[i] == old(self).regions[i]);
                } else {
                    assert(self.regions[i] == region);
                }
            };
            // All regions are still non-overlapping
            assert forall|i: int, j: int|
                0 <= i < self.regions.len() && 0 <= j < self.regions.len() && i
                    != j implies !self.regions[i].spec_overlaps_vmem(self.regions[j]) by {
                self.regions[i].lemma_overlaps_vmem_symmetric(self.regions[j]);
                if i != self.regions.len() - 1 && j != self.regions.len() - 1 {
                    // Old regions
                    assert(!self.regions[i].spec_overlaps_vmem(self.regions[j])) by {
                        assert(!old(self).regions[i].spec_overlaps_vmem(old(self).regions[j]));
                    };
                }
            }
            // All regions are mapped in the page table
            assert forall|i: int|
                0 <= i < self.regions.len() implies #[trigger] self.has_mapping_for(
                self.regions[i],
            ) by {
                if i == self.regions.len() - 1 {
                    assert(self.regions[i] == region);
                } else {
                    assert(old_self.has_mapping_for(self.regions[i]));
                }
            }
            // All mappings in the page table are within these regions
            assert(forall|vbase2: SpecVAddr, frame2: SpecFrame| #[trigger]
                self.pt.view().mappings.contains_pair(vbase2, frame2) ==> self.has_region_for_frame(
                    vbase2,
                    frame2,
                )) by {
                assert(forall|j: int|
                    #![auto]
                    0 <= j < self.regions.len() - 1 ==> self.regions[j] == old_self.regions[j]);
                assert(self.regions[self.regions.len() - 1] == region);
            }
            assert(self.invariants());
        }
    }

    fn remove(&mut self, allocator: &GlobalAllocator<A>, start: VAddr) {
        let len = self.regions.len();
        let mut i = 0;
        // Find the region with the given start address
        while i < len
            invariant
                len == self.regions.len(),
                0 <= i <= self.regions.len(),
                *self == *old(self),
                forall|j: int| 0 <= j < i ==> #[trigger] self.regions[j].start@ != start@,
            ensures
                i < len ==> self.regions[i as int].start@ == start@,
            decreases len - i,
        {
            if self.regions[i].start.0 == start.0 {
                break ;
            }
            i += 1;
        }
        if i == len {
            assert(false);  // No region starts at the given address, contradicts precondition
        }
        proof {
            self.lemma_region_start_unique();
            assert(i == choose|i: int|
                0 <= i < self.regions.len() && #[trigger] self.regions[i].start@ == start@);
        }

        let ridx = i;
        let region = &self.regions[ridx];
        assert(region.start@ == start@);
        assert(self.has_mapping_for(*region));

        let mut i = 0;
        // Unmap the region from the page table
        while i < region.pages
            invariant
                region.spec_valid(),
                i <= region.pages,
                self.pt.invariants(),
                self.pt.inst_id() == allocator.inst_id(),
                allocator.invariants(),
                self.pt.view().constants == old(self).pt.view().constants,
                self.pt.view().constants.valid(),
                self.pt.view().constants.arch.leaf_frame_size() == FrameSize::Size4K,
                self.regions == old(self).regions,
                old(self).invariants(),
                // Region do not overlap with other regions
                forall|j: int|
                    0 <= j < self.regions.len() && j != ridx ==> !region.spec_overlaps_vmem(
                        #[trigger] self.regions[j],
                    ),
                // Pages [i, region.pages) of the removed region are mapped in the page table
                forall|j: nat|
                    i <= j < region.pages ==> #[trigger] self.pt.view().mappings.contains_key(
                        region.start@.offset(j * SPEC_PAGE_SIZE),
                    ),
                // All mappings are within old regions or the pages [i, region.pages) of the removed region
                forall|vbase2: SpecVAddr, frame2: SpecFrame| #[trigger]
                    self.pt.view().mappings.contains_pair(vbase2, frame2)
                        ==> self.has_region_for_frame_except(vbase2, frame2, ridx as int)
                        || SpecVAddr::interval_subset(
                        vbase2,
                        frame2.size.as_nat(),
                        region.start@.offset((i * PAGE_SIZE) as nat),
                        (region.pages - i) as nat * SPEC_PAGE_SIZE,
                    ),
                // Other regions are mapped in the page table
                forall|j: int|
                    0 <= j < self.regions.len() && j != ridx ==> #[trigger] self.has_mapping_for(
                        self.regions[j],
                    ),
            decreases region.pages - i,
        {
            let vaddr = VAddr(region.start.0 + i * PAGE_SIZE);
            proof {
                assert(vaddr@.0 % SPEC_PAGE_SIZE == 0);
                assert(self.pt.view().mappings.contains_key(
                    region.start@.offset((i * PAGE_SIZE) as nat),
                ));
                // TODO: edit precondition to require the new region is within the address space limit
                assume(vaddr@.0 < self.pt.view().constants.arch.vspace_size());
            }

            let ghost old_self = *self;
            let ghost old_mappings = self.pt.view().mappings;
            // Unmap the frame, always succeed
            let res = self.pt.unmap(allocator, vaddr);
            let ghost mappings = self.pt.view().mappings;
            i += 1;

            proof {
                // Prove loop invariants
                assert(self.pt.invariants());
                assert(res.is_ok());
                assert(mappings == old_mappings.remove(vaddr@));
                // All mappings are within old regions or the pages [i, region.pages) of the removed region
                assert forall|vbase2: SpecVAddr, frame2: SpecFrame| #[trigger]
                    mappings.contains_pair(vbase2, frame2) implies self.has_region_for_frame_except(
                    vbase2,
                    frame2,
                    ridx as int,
                ) || SpecVAddr::interval_subset(
                    vbase2,
                    frame2.size.as_nat(),
                    region.start@.offset((i * PAGE_SIZE) as nat),
                    (region.pages - i) as nat * SPEC_PAGE_SIZE,
                ) by {
                    if !self.has_region_for_frame_except(vbase2, frame2, ridx as int) {
                        assert(old_mappings.contains_pair(vbase2, frame2));
                        assert(!old_self.has_region_for_frame_except(vbase2, frame2, ridx as int));
                        assert(SpecVAddr::interval_subset(
                            vbase2,
                            frame2.size.as_nat(),
                            vaddr@,
                            (region.pages - (i - 1)) as nat * SPEC_PAGE_SIZE,
                        ));
                        assert(vbase2.aligned(SPEC_PAGE_SIZE));
                        assert(vbase2.0 - vaddr@.0 >= PAGE_SIZE);
                        assert(SpecVAddr::interval_subset(
                            vbase2,
                            frame2.size.as_nat(),
                            region.start@.offset((i * PAGE_SIZE) as nat),
                            (region.pages - i) as nat * SPEC_PAGE_SIZE,
                        ));
                    }
                }
                // Other regions are still mapped in the page table
                assert forall|j: int|
                    0 <= j < self.regions.len() && j
                        != ridx implies #[trigger] self.has_mapping_for(self.regions[j]) by {
                    let region2 = self.regions[j];
                    assert(old_self.has_mapping_for(region2));
                    assert(!region.spec_overlaps_vmem(region2));
                }
            }
        }

        // Remove the region from the list
        let ghost old_self = *self;
        self.regions.remove(ridx);

        proof {
            let removed = old(self).regions[ridx as int];
            assert forall|r: MemoryRegion| #[trigger]
                self@.regions.contains(r) <==> old(self)@.regions.remove(removed).contains(r) by {
                if self@.regions.contains(r) {
                    let i = choose|i: int| 0 <= i < self.regions.len() && self.regions[i] == r;
                    let oi: int = if i < ridx {
                        i
                    } else {
                        i + 1
                    };
                    assert(old(self).regions[oi] == r);
                    assert(oi != ridx as int);
                }
                if old(self)@.regions.remove(removed).contains(r) {
                    assert(old(self)@.regions.contains(r) && r != removed);
                    let i = choose|i: int|
                        0 <= i < old(self).regions.len() && old(self).regions[i] == r;
                    assert(i != ridx as int);
                    let si: int = if i < ridx {
                        i
                    } else {
                        i - 1
                    };
                    assert(self.regions[si] == r);
                }
            };
            assert(self@.regions =~= old(self)@.regions.remove(removed));
            // Prove invariants
            // All regions are still valid
            assert forall|i: int|
                0 <= i < self.regions.len() implies #[trigger] self.regions[i].spec_valid() by {
                if i < ridx {
                    assert(self.regions[i] == old(self).regions[i]);
                } else {
                    assert(self.regions[i] == old(self).regions[i + 1]);
                }
            };
            // All regions are still non-overlapping
            assert forall|i: int, j: int|
                0 <= i < self.regions.len() && 0 <= j < self.regions.len() && i
                    != j implies !self.regions[i].spec_overlaps_vmem(self.regions[j]) by {
                self.regions[i].lemma_overlaps_vmem_symmetric(self.regions[j]);
                let oi: int = if i < ridx {
                    i
                } else {
                    i + 1
                };
                let oj: int = if j < ridx {
                    j
                } else {
                    j + 1
                };
                assert(self.regions[i] == old(self).regions[oi]);
                assert(self.regions[j] == old(self).regions[oj]);
                assert(oi != oj);
                assert(!old(self).regions[oi].spec_overlaps_vmem(old(self).regions[oj]));
            }
            // All regions are mapped in the page table
            assert forall|i: int|
                0 <= i < self.regions.len() implies #[trigger] self.has_mapping_for(
                self.regions[i],
            ) by {
                if i < ridx {
                    assert(self.regions[i] == old(self).regions[i]);
                    assert(old_self.has_mapping_for(self.regions[i]));
                } else {
                    assert(self.regions[i] == old(self).regions[i + 1]);
                    assert(old_self.has_mapping_for(self.regions[i]));
                }
            }
            // All mappings in the page table are within these regions
            assert forall|vbase2: SpecVAddr, frame2: SpecFrame| #[trigger]
                self.pt.view().mappings.contains_pair(
                    vbase2,
                    frame2,
                ) implies self.has_region_for_frame(vbase2, frame2) by {
                assert(old_self.has_region_for_frame_except(vbase2, frame2, ridx as int));
                let j = choose|j: int|
                    0 <= j < old_self.regions.len() && #[trigger] SpecVAddr::interval_subset(
                        vbase2,
                        frame2.size.as_nat(),
                        old_self.regions[j].start@,
                        old_self.regions[j].pages as nat * SPEC_PAGE_SIZE,
                    );
                if j < ridx {
                    assert(old_self.regions[j] == self.regions[j]);
                } else {
                    assert(old_self.regions[j] == self.regions[j - 1]);
                }
            }
            assert(self.invariants());
        }
    }

    proof fn lemma_invariants_implies_wf(self) {
        assert forall|r: MemoryRegion| #[trigger]
            self.view().regions.contains(r) implies r.spec_valid() by {
            let i = choose|i: int| 0 <= i < self.regions.len() && self.regions[i] == r;
            assert(self.regions[i].spec_valid());
        };
        assert forall|r1: MemoryRegion, r2: MemoryRegion|
            self.view().regions.contains(r1) && self.view().regions.contains(r2) && r1
                != r2 implies !r1.spec_overlaps_vmem(r2) by {
            let i = choose|i: int| 0 <= i < self.regions.len() && self.regions[i] == r1;
            let j = choose|j: int| 0 <= j < self.regions.len() && self.regions[j] == r2;
            assert(i != j);
            assert(!self.regions[i].spec_overlaps_vmem(self.regions[j]));
        };
    }
}

} // verus!
