//! A memory set is a collection of memory areas that can be mapped into the virtual address
//! space of a zone (process). It manages the page table for the zone, and provides methods to
//! insert, remove, and find memory areas.
use crate::{
    address::{
        addr::{SpecVAddr, VAddr},
        frame::{self, Frame, FrameSize, MemoryRegion, SpecFrame, PAGE_SIZE},
    },
    global_allocator::GlobalAllocator,
    page_table::PageTable,
};
use std::marker::PhantomData;
use vstd::{invariant, prelude::*};

verus! {

broadcast use crate::page_table::PageTable::lemma_invariants_implies_wf;

/// Specification of a memory set viewed by higher-level components.
pub trait MemorySet<PT, A> where PT: PageTable<A>, A: GlobalAllocator {
    /// View the memory set as a list of memory regions.
    spec fn view(&self, allocator: &A) -> Seq<MemoryRegion>;

    /// Invariants that must be implied at initial state and preseved after each operation.
    spec fn invariants(&self, allocator: &A) -> bool;

    /// Insert a new memory region into the memory set.
    fn insert(&mut self, allocator: &mut A, region: MemoryRegion) -> (res: Result<(), ()>)
        requires
            old(self).invariants(old(allocator)),
            !old(allocator).view().free.is_empty(),
            region.spec_valid(),
        ensures
            if exists|i: int|
                0 <= i < old(self).view(old(allocator)).len() && #[trigger] old(self).view(
                    old(allocator),
                )[i].spec_overlaps(region) {
                &&& res is Err
                &&& self.view(allocator) == old(self).view(old(allocator))
            } else {
                &&& res is Ok
                &&& self.view(allocator) == old(self).view(old(allocator)).push(region)
                &&& self.invariants(allocator)
            },
    ;

    /// Remove a memory region from the memory set by its starting virtual address.
    fn remove(&mut self, allocator: &mut A, start: VAddr) -> (res: Result<(), ()>)
        requires
            old(self).invariants(old(allocator)),
        ensures
            if exists|i: int|
                0 <= i < old(self).view(old(allocator)).len() && #[trigger] old(self).view(
                    old(allocator),
                )[i].start@ == start@ {
                let i = choose|i: int|
                    0 <= i < old(self).view(old(allocator)).len() && #[trigger] old(self).view(
                        old(allocator),
                    )[i].start@ == start@;
                &&& res is Ok
                &&& self.view(allocator) == old(self).view(old(allocator)).remove(i)
                &&& self.invariants(allocator)
            } else {
                &&& res is Err
                &&& self.view(allocator) == old(self).view(old(allocator))
            },
    ;
}

/// Memory set implementation using a vector of memory regions.
pub struct VecMemorySet<PT, A> where PT: PageTable<A>, A: GlobalAllocator {
    /// The list of memory regions in the memory set.
    pub regions: Vec<MemoryRegion>,
    /// Page table managing the mappings.
    pub pt: PT,
    /// Phantom data for the page table memory type.
    pub phantom: PhantomData<A>,
}

impl<PT, A> VecMemorySet<PT, A> where PT: PageTable<A>, A: GlobalAllocator {
    /// If a region is mapped in the page table.
    ///
    /// TODO: For now we only support 4KB pages, so we use `mappings.contains_key` to simplify the proof.
    /// In the future if we want to support huge pages, we may use `pt.has_mapping_for` instead.
    pub open spec fn has_mapping_for(&self, region: MemoryRegion, allocator: &A) -> bool {
        forall|i: nat|
            i < region.pages ==> #[trigger] self.pt.view(allocator).mappings.contains_key(
                region.start@.offset(i * PAGE_SIZE as nat),
            )
    }

    /// If there is region contains the given virtual frame.
    pub open spec fn has_region_for_frame(&self, vbase: SpecVAddr, frame: SpecFrame) -> bool {
        exists|i: int|
            0 <= i < self.regions.len() && #[trigger] SpecVAddr::interval_subset(
                vbase,
                frame.size.as_nat(),
                self.regions[i].start@,
                self.regions[i].pages as nat * PAGE_SIZE as nat,
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
                self.regions[i].pages as nat * PAGE_SIZE as nat,
            )
    }

    /// Spec-mode overlap check.
    pub open spec fn spec_overlaps(&self, region: MemoryRegion) -> bool {
        exists|i: int|
            0 <= i < self.regions.len() && #[trigger] self.regions[i].spec_overlaps(region)
    }

    /// Check if a region overlaps with any existing region.
    pub fn overlaps(&self, region: &MemoryRegion, allocator: &A) -> (res: bool)
        requires
            self.invariants(allocator),
            region.spec_valid(),
        ensures
            res == self.spec_overlaps(*region),
    {
        for i in 0..self.regions.len()
            invariant
                0 <= i <= self.regions.len(),
                region.spec_valid(),
                self.invariants(allocator),
                forall|j: int| #![auto] 0 <= j < i ==> !self.regions[j].spec_overlaps(*region),
        {
            let r = &self.regions[i];
            if r.overlaps(region) {
                return true;
            }
        }
        false
    }

    /// Lemma: overlaps in `vec` implies overlaps in spec view.
    proof fn lemma_overlaps_equiv(self, region: MemoryRegion, allocator: &A)
        requires
            self.invariants(allocator),
            region.spec_valid(),
        ensures
            self.spec_overlaps(region) == exists|i: int|
                0 <= i < self.view(allocator).len() && #[trigger] self.view(
                    allocator,
                )[i].spec_overlaps(region),
    {
        if self.spec_overlaps(region) {
            let i = choose|i: int|
                {
                    &&& 0 <= i < self.regions.len()
                    &&& #[trigger] self.regions[i].spec_overlaps(region)
                };
            assert(self.view(allocator)[i] == self.regions[i]);
        }
    }

    /// Lemma: two regions cannot have the same starting virtual address.
    proof fn lemma_region_start_unique(self, allocator: &A)
        requires
            self.invariants(allocator),
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
            assert(self.regions[i].spec_overlaps(self.regions[j]));
        }
    }
}

impl<PT, A> MemorySet<PT, A> for VecMemorySet<PT, A> where PT: PageTable<A>, A: GlobalAllocator {
    open spec fn view(&self, allocator: &A) -> Seq<MemoryRegion> {
        Seq::new(self.regions.len() as nat, |i| self.regions[i])
    }

    open spec fn invariants(&self, allocator: &A) -> bool {
        &&& self.pt.view(allocator).constants.valid()
        // Frame size is 4K
        &&& self.pt.view(allocator).constants.arch.leaf_frame_size()
            == FrameSize::Size4K
        // Page table invariants
        &&& self.pt.invariants(allocator)
        // Regions are valid
        &&& forall|i: int|
            0 <= i < self.regions.len()
                ==> #[trigger] self.regions[i].spec_valid()
        // Regions do not overlap
        &&& forall|i: int, j: int|
            0 <= i < self.regions.len() && 0 <= j < self.regions.len() && i != j
                ==> !self.regions[i].spec_overlaps(
                self.regions[j],
            )
        // Page table contains mappings only within these regions
        &&& forall|vbase: SpecVAddr, frame: SpecFrame| #[trigger]
            self.pt.view(allocator).mappings.contains_pair(vbase, frame)
                ==> self.has_region_for_frame(
                vbase,
                frame,
            )
        // All regions are mapped in the page table
        &&& forall|i: int|
            0 <= i < self.regions.len() ==> #[trigger] self.has_mapping_for(
                self.regions[i],
                allocator,
            )
    }

    fn insert(&mut self, allocator: &mut A, region: MemoryRegion) -> (res: Result<(), ()>) {
        proof {
            self.lemma_overlaps_equiv(region, allocator);
        }
        if self.overlaps(&region, allocator) {
            return Err(());
        }
        assert(!self.spec_overlaps(region));

        // New region does not overlap with old regions
        assert(forall|j: int|
            #![auto]
            0 <= j < self.regions.len() ==> !self.regions[j].spec_overlaps(region));
        assert forall|j: int| #![auto] 0 <= j < self.regions.len() implies !region.spec_overlaps(
            self.regions[j],
        ) by {
            self.regions[j].lemma_overlaps_symmetric(region);
        };

        // Map the region in the page table
        let mut i: usize = 0;
        while i < region.pages
            invariant
                region.spec_valid(),
                i <= region.pages,
                self.pt.invariants(allocator),
                self.pt.view(allocator).constants == old(self).pt.view(old(allocator)).constants,
                self.pt.view(allocator).constants.valid(),
                self.pt.view(allocator).constants.arch.leaf_frame_size() == FrameSize::Size4K,
                self.regions == old(self).regions,
                old(self).invariants(old(allocator)),
                // Old regions do not overlap with each other
                forall|j: int|
                    0 <= j < self.regions.len() ==> !region.spec_overlaps(
                        #[trigger] self.regions[j],
                    ),
                // New region does not overlap with any old region
                !self.spec_overlaps(region),
                // The first `i` pages of the new region are mapped in the page table
                forall|j: nat|
                    j < i ==> #[trigger] self.pt.view(allocator).mappings.contains_key(
                        region.start@.offset(j * PAGE_SIZE as nat),
                    ),
                // All mappings in the page table are within old regions or the first `i` pages of the new region
                forall|vbase2: SpecVAddr, frame2: SpecFrame| #[trigger]
                    self.pt.view(allocator).mappings.contains_pair(vbase2, frame2)
                        ==> self.has_region_for_frame(vbase2, frame2) || SpecVAddr::interval_subset(
                        vbase2,
                        frame2.size.as_nat(),
                        region.start@,
                        i as nat * PAGE_SIZE as nat,
                    ),
                // Old regions are mapped in the page table
                forall|j: int|
                    0 <= j < self.regions.len() ==> #[trigger] self.has_mapping_for(
                        self.regions[j],
                        allocator,
                    ),
                // Assumption to avoid OOM: there are enough free frames in the global allocator
                !allocator.view().free.is_empty(),
            decreases region.pages - i,
        {
            let vaddr = VAddr(region.start.0 + i * PAGE_SIZE);
            let paddr = region.mapper.map(vaddr);
            // TODO: support huge pages
            let frame = Frame { base: paddr, size: FrameSize::Size4K, attr: region.attr.clone() };

            proof {
                assert(vaddr@.within(region.start@, region.pages as nat * PAGE_SIZE as nat));
                // vaddr not within any existing region
                assert forall|j: int| #![auto] 0 <= j < self.regions.len() implies !vaddr@.within(
                    self.regions[j].start@,
                    self.regions[j].pages as nat * PAGE_SIZE as nat,
                ) by {
                    let r = self.regions[j];
                    assert(!region.spec_overlaps(r));
                    if vaddr@.within(r.start@, r.pages as nat * PAGE_SIZE as nat) {
                        assert(region.spec_overlaps(r));
                    }
                };
                // (vaddr, frame) does not overlap with any existing region
                assert(forall|j: int|
                    #![auto]
                    0 <= j < self.regions.len() ==> !SpecVAddr::overlap(
                        vaddr@,
                        frame.size.as_nat(),
                        self.regions[j].start@,
                        self.regions[j].pages as nat * PAGE_SIZE as nat,
                    ));

                if i > 0 {
                    // vaddr not within the already mapped part of the new region
                    assert(!vaddr@.within(region.start@, (i - 1) as nat * PAGE_SIZE as nat));
                    // (vaddr, frame) does not overlap with the already mapped part of the new region
                    assert(!SpecVAddr::overlap(
                        vaddr@,
                        frame.size.as_nat(),
                        region.start@,
                        (i - 1) as nat * PAGE_SIZE as nat,
                    ));
                }
                let mappings = self.pt.view(allocator).mappings;
                // (vaddr, frame) does not overlap with any existing mapping
                assert forall|vbase2: SpecVAddr| #[trigger]
                    mappings.contains_key(vbase2) implies !SpecVAddr::overlap(
                    vbase2,
                    mappings[vbase2].size.as_nat(),
                    vaddr@,
                    frame.size.as_nat(),
                ) by {
                    assert(mappings.contains_pair(vbase2, mappings[vbase2]));
                    assert(self.pt.view(allocator).has_mapping_for(vbase2));
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
                            i as nat * PAGE_SIZE as nat,
                        ));
                    }
                    assert(!SpecVAddr::overlap(
                        vbase2,
                        self.pt.view(allocator).mappings[vbase2].size.as_nat(),
                        vaddr@,
                        frame.size.as_nat(),
                    ));
                }
                assert(!self.pt.view(allocator).overlaps_vmem(vaddr@, frame@));
            }
            // TODO: edit precondition to require the new region is within the address space limit
            assume(vaddr@.0 < self.pt.view(allocator).constants.arch.vspace_size());

            let ghost old_self = *self;
            let ghost old_allocator = *allocator;
            let ghost old_mappings = self.pt.view(allocator).mappings;
            let res = self.pt.map(allocator, vaddr, frame);
            let ghost mappings = self.pt.view(allocator).mappings;
            i += 1;

            proof {
                // Prove loop invariants
                assert(self.pt.invariants(allocator));
                assert(res.is_ok());
                assert(mappings == old_mappings.insert(vaddr@, frame@));
                assert(mappings.contains_pair(vaddr@, frame@));
                // The first `i` pages of the new region are mapped in the page table
                assert forall|j: nat| j < i implies #[trigger] self.pt.view(
                    allocator,
                ).mappings.contains_key(region.start@.offset(j * PAGE_SIZE as nat)) by {
                    let vaddr2 = region.start@.offset(j * PAGE_SIZE as nat);
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
                    i as nat * PAGE_SIZE as nat,
                ) by {
                    if old_mappings.contains_pair(vbase2, frame2) {
                        assert(self.has_region_for_frame(vbase2, frame2)
                            || SpecVAddr::interval_subset(
                            vbase2,
                            frame2.size.as_nat(),
                            region.start@,
                            (i - 1) as nat * PAGE_SIZE as nat,
                        ));
                    } else {
                        assert(vbase2 == vaddr@ && frame2 == frame@);
                        assert(SpecVAddr::interval_subset(
                            vaddr@,
                            frame@.size.as_nat(),
                            region.start@,
                            i as nat * PAGE_SIZE as nat,
                        ));
                    }
                }
                // Old regions are still mapped in the page table
                assert forall|j: int|
                    0 <= j < self.regions.len() implies #[trigger] self.has_mapping_for(
                    self.regions[j],
                    allocator,
                ) by {
                    let region = self.regions[j];
                    assert(old_self.has_mapping_for(region, &old_allocator));
                }
                // Assumption to avoid OOM
                assume(!allocator.view().free.is_empty());
            }
        }

        // After the loop, the whole region is mapped in the page table
        assert(self.has_mapping_for(region, allocator));
        // Push the region into the list
        let ghost old_self = *self;
        self.regions.push(region);

        proof {
            assert(self.view(allocator) == old(self).view(old(allocator)).push(region));
            // Prove invariants
            // All regions are still valid
            assert forall|i: int|
                0 <= i < self.regions.len() implies #[trigger] self.regions[i].spec_valid() by {
                if i < self.regions.len() - 1 {
                    assert(self.regions[i] == old(self).view(old(allocator))[i]);
                } else {
                    assert(self.regions[i] == region);
                }
            };
            // All regions are still non-overlapping
            assert forall|i: int, j: int|
                0 <= i < self.regions.len() && 0 <= j < self.regions.len() && i
                    != j implies !self.regions[i].spec_overlaps(self.regions[j]) by {
                self.regions[i].lemma_overlaps_symmetric(self.regions[j]);
                if i != self.regions.len() - 1 && j != self.regions.len() - 1 {
                    // Old regions
                    assert(!self.regions[i].spec_overlaps(self.regions[j])) by {
                        assert(!old(self).view(old(allocator))[i].spec_overlaps(
                            old(self).view(old(allocator))[j],
                        ));
                    };
                }
            }
            // All regions are mapped in the page table
            assert forall|i: int|
                0 <= i < self.regions.len() implies #[trigger] self.has_mapping_for(
                self.regions[i],
                allocator,
            ) by {
                if i == self.regions.len() - 1 {
                    assert(self.regions[i] == region);
                } else {
                    assert(old_self.has_mapping_for(self.regions[i], allocator));
                }
            }
            // All mappings in the page table are within these regions
            assert(forall|vbase2: SpecVAddr, frame2: SpecFrame| #[trigger]
                self.pt.view(allocator).mappings.contains_pair(vbase2, frame2)
                    ==> self.has_region_for_frame(vbase2, frame2)) by {
                assert(forall|j: int|
                    #![auto]
                    0 <= j < self.regions.len() - 1 ==> self.regions[j] == old_self.regions[j]);
                assert(self.regions[self.regions.len() - 1] == region);
            }
            assert(self.invariants(allocator));
        }

        Ok(())
    }

    fn remove(&mut self, allocator: &mut A, start: VAddr) -> (res: Result<(), ()>) {
        let len = self.regions.len();
        let mut i = 0;
        // Find the region with the given start address
        while i < len
            invariant
                len == self.regions.len(),
                0 <= i <= self.regions.len(),
                *self == *old(self),
                *allocator == *old(allocator),
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
            // Region not found
            assert(!exists|i: int|
                0 <= i < self.regions.len() && #[trigger] self.regions[i].start@ == start@);
            return Err(());
        }
        proof {
            self.lemma_region_start_unique(allocator);
            assert(i == choose|i: int|
                0 <= i < self.regions.len() && #[trigger] self.regions[i].start@ == start@);
        }

        let ridx = i;
        let region = &self.regions[ridx];
        assert(region.start@ == start@);
        assert(self.has_mapping_for(*region, allocator));

        let mut i = 0;
        // Unmap the region from the page table
        while i < region.pages
            invariant
                region.spec_valid(),
                i <= region.pages,
                self.pt.invariants(allocator),
                self.pt.view(allocator).constants == old(self).pt.view(old(allocator)).constants,
                self.pt.view(allocator).constants.valid(),
                self.pt.view(allocator).constants.arch.leaf_frame_size() == FrameSize::Size4K,
                self.regions == old(self).regions,
                old(self).invariants(old(allocator)),
                // Region do not overlap with other regions
                forall|j: int|
                    0 <= j < self.regions.len() && j != ridx ==> !region.spec_overlaps(
                        #[trigger] self.regions[j],
                    ),
                // Pages [i, region.pages) of the removed region are mapped in the page table
                forall|j: nat|
                    i <= j < region.pages ==> #[trigger] self.pt.view(
                        allocator,
                    ).mappings.contains_key(region.start@.offset(j * PAGE_SIZE as nat)),
                // All mappings are within old regions or the pages [i, region.pages) of the removed region
                forall|vbase2: SpecVAddr, frame2: SpecFrame| #[trigger]
                    self.pt.view(allocator).mappings.contains_pair(vbase2, frame2)
                        ==> self.has_region_for_frame_except(vbase2, frame2, ridx as int)
                        || SpecVAddr::interval_subset(
                        vbase2,
                        frame2.size.as_nat(),
                        region.start@.offset((i * PAGE_SIZE) as nat),
                        (region.pages - i) as nat * PAGE_SIZE as nat,
                    ),
                // Other regions are mapped in the page table
                forall|j: int|
                    0 <= j < self.regions.len() && j != ridx ==> #[trigger] self.has_mapping_for(
                        self.regions[j],
                        allocator,
                    ),
            decreases region.pages - i,
        {
            let vaddr = VAddr(region.start.0 + i * PAGE_SIZE);
            proof {
                assert(vaddr@.0 % PAGE_SIZE as nat == 0);
                assert(self.pt.view(allocator).mappings.contains_key(
                    region.start@.offset((i * PAGE_SIZE) as nat),
                ));
                // TODO: edit precondition to require the new region is within the address space limit
                assume(vaddr@.0 < self.pt.view(allocator).constants.arch.vspace_size());
            }

            let ghost old_self = *self;
            let ghost old_allocator = *allocator;
            let ghost old_mappings = self.pt.view(allocator).mappings;
            // Unmap the frame, always succeed
            let res = self.pt.unmap(allocator, vaddr);
            let ghost mappings = self.pt.view(allocator).mappings;
            i += 1;

            proof {
                // Prove loop invariants
                assert(self.pt.invariants(allocator));
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
                    (region.pages - i) as nat * PAGE_SIZE as nat,
                ) by {
                    if !self.has_region_for_frame_except(vbase2, frame2, ridx as int) {
                        assert(old_mappings.contains_pair(vbase2, frame2));
                        assert(!old_self.has_region_for_frame_except(vbase2, frame2, ridx as int));
                        assert(SpecVAddr::interval_subset(
                            vbase2,
                            frame2.size.as_nat(),
                            vaddr@,
                            (region.pages - (i - 1)) as nat * PAGE_SIZE as nat,
                        ));
                        assert(vbase2.aligned(PAGE_SIZE as nat));
                        assert(vbase2.0 - vaddr@.0 >= PAGE_SIZE);
                        assert(SpecVAddr::interval_subset(
                            vbase2,
                            frame2.size.as_nat(),
                            region.start@.offset((i * PAGE_SIZE) as nat),
                            (region.pages - i) as nat * PAGE_SIZE as nat,
                        ));
                    }
                }
                // Other regions are still mapped in the page table
                assert forall|j: int|
                    0 <= j < self.regions.len() && j
                        != ridx implies #[trigger] self.has_mapping_for(
                    self.regions[j],
                    allocator,
                ) by {
                    let region2 = self.regions[j];
                    assert(old_self.has_mapping_for(region2, &old_allocator));
                    assert(!region.spec_overlaps(region2));
                }
            }
        }

        // Remove the region from the list
        let ghost old_self = *self;
        self.regions.remove(ridx);

        proof {
            assert(self.view(allocator) == old(self).view(old(allocator)).remove(ridx as int));
            // Prove invariants
            // All regions are still valid
            assert forall|i: int|
                0 <= i < self.regions.len() implies #[trigger] self.regions[i].spec_valid() by {
                if i < ridx {
                    assert(self.regions[i] == old(self).view(old(allocator))[i]);
                } else {
                    assert(self.regions[i] == old(self).view(old(allocator))[i + 1]);
                }
            };
            // All regions are still non-overlapping
            assert forall|i: int, j: int|
                0 <= i < self.regions.len() && 0 <= j < self.regions.len() && i
                    != j implies !self.regions[i].spec_overlaps(self.regions[j]) by {
                self.regions[i].lemma_overlaps_symmetric(self.regions[j]);
                if i != self.regions.len() - 1 && j != self.regions.len() - 1 {
                    // Old regions
                    assert(!self.regions[i].spec_overlaps(self.regions[j])) by {
                        assert(!old(self).view(old(allocator))[i].spec_overlaps(
                            old(self).view(old(allocator))[j],
                        ));
                    };
                }
            }
            // All regions are mapped in the page table
            assert forall|i: int|
                0 <= i < self.regions.len() implies #[trigger] self.has_mapping_for(
                self.regions[i],
                allocator,
            ) by {
                if i < ridx {
                    assert(self.regions[i] == old(self).view(old(allocator))[i]);
                    assert(old_self.has_mapping_for(self.regions[i], allocator));
                } else {
                    assert(self.regions[i] == old(self).view(old(allocator))[i + 1]);
                    assert(old_self.has_mapping_for(self.regions[i], allocator));
                }
            }
            // All mappings in the page table are within these regions
            assert forall|vbase2: SpecVAddr, frame2: SpecFrame| #[trigger]
                self.pt.view(allocator).mappings.contains_pair(
                    vbase2,
                    frame2,
                ) implies self.has_region_for_frame(vbase2, frame2) by {
                assert(old_self.has_region_for_frame_except(vbase2, frame2, ridx as int));
                let j = choose|j: int|
                    0 <= j < old_self.regions.len() && #[trigger] SpecVAddr::interval_subset(
                        vbase2,
                        frame2.size.as_nat(),
                        old_self.regions[j].start@,
                        old_self.regions[j].pages as nat * PAGE_SIZE as nat,
                    );
                if j < ridx {
                    assert(old_self.regions[j] == self.regions[j]);
                } else {
                    assert(old_self.regions[j] == self.regions[j - 1]);
                }
            }
            assert(self.invariants(allocator));
        }

        Ok(())
    }
}

} // verus!
