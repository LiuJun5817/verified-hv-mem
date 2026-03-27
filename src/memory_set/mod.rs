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
    ;  // /
    // Remove a memory region from the memory set by its starting virtual address.
    // fn remove(&mut self, allocator: &mut A, start: VAddr) -> (res: Result<(), ()>)
    //     requires
    //         old(self).invariants(old(allocator)),
    //     ensures
    //         if exists|i: int|
    //             0 <= i < old(self).view(old(allocator)).len() && #[trigger] old(self).view(
    //                 old(allocator),
    //             )[i].start@ == start@ {
    //             let i = choose|i: int|
    //                 0 <= i < old(self).view(old(allocator)).len() && #[trigger] old(self).view(
    //                     old(allocator),
    //                 )[i].start@ == start@;
    //             &&& res is Ok
    //             &&& self.view(allocator) == old(self).view(old(allocator)).remove(i)
    //             &&& self.invariants(old(allocator))
    //         } else {
    //             &&& res is Err
    //             &&& self.view(allocator) == old(self).view(old(allocator))
    //         },
    // ;

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
    /// TODO: should we use `has_mapping_for` or `mappings.contains_key` to specify this?
    pub open spec fn has_mapping_for(&self, region: MemoryRegion, allocator: &A) -> bool {
        forall|i: nat|
            i < region.pages ==> #[trigger] self.pt.view(allocator).has_mapping_for(
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
                    j < i ==> #[trigger] self.pt.view(allocator).has_mapping_for(
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
            let ghost old_pt = self.pt.view(allocator);
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
                ).has_mapping_for(region.start@.offset(j * PAGE_SIZE as nat)) by {
                    let vaddr2 = region.start@.offset(j * PAGE_SIZE as nat);
                    if j == i - 1 {
                        assert(vaddr2 == vaddr@);
                    } else {
                        assert(old_pt.has_mapping_for(vaddr2));
                        let (vbase2, frame2) = choose|vbase2: SpecVAddr, frame2: SpecFrame|
                         #[trigger]
                            old_mappings.contains_pair(vbase2, frame2) && vaddr2.within(
                                vbase2,
                                frame2.size.as_nat(),
                            );
                        assert(mappings.contains_pair(vbase2, frame2));
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
                    assert forall|k: nat| k < region.pages implies #[trigger] self.pt.view(
                        allocator,
                    ).has_mapping_for(region.start@.offset(k * PAGE_SIZE as nat)) by {
                        assert(old_pt.has_mapping_for(region.start@.offset(k * PAGE_SIZE as nat)));
                        let (vbase2, frame2) = choose|vbase2: SpecVAddr, frame2: SpecFrame|
                         #[trigger]
                            old_mappings.contains_pair(vbase2, frame2) && region.start@.offset(
                                k * PAGE_SIZE as nat,
                            ).within(vbase2, frame2.size.as_nat());
                        assert(mappings.contains_pair(vbase2, frame2));
                    }
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
    
    /*
    fn remove(&mut self, allocator: &mut A, start: VAddr) -> (res: Result<(), ()>) {
        let len = self.regions.len();
        for i in 0..len
            invariant
                len == self.regions.len(),
                0 <= i <= self.regions.len(),
                self.invariants(),
                self.pt@.constants == old(self).pt@.constants,
                old(self).regions == self.regions,
                forall|j: int| 0 <= j < i ==> #[trigger] self.regions[j].start@ != start@,
        {
            let r = &self.regions[i];
            // Find the region with the given start address
            if r.start.0 == start.0 {
                assert(old(self).regions == self.regions);

                // Unmap the region from the page table
                for j in 0..r.pages
                    invariant
                        r.spec_valid(),
                        self.pt.invariants(),
                        self.pt@.constants == old(self).pt@.constants,
                        self.pt@.constants.arch.leaf_frame_size() == FrameSize::Size4K,
                        old(self).regions == self.regions,
                {
                    let vaddr = VAddr(r.start.0 + j * PAGE_SIZE);
                    // TODO: prove addr alignment
                    // 从 invariants 的 has_mapping_for(r) 推出每个页都 mapped，从而 unmap_pre 成立。
                    assume(self.pt.view().unmap_pre(vaddr@));
                    self.pt.unmap(vaddr);
                }

                // Remove the region from the list
                self.regions.remove(i);

                proof {
                    assert(old(self)@[i as int].start@ == start@);
                    // TODO: prove uniqueness
                    assume(i == choose|i: int|
                        0 <= i < old(self)@.len() && #[trigger] old(self)@[i].start@ == start@);
                    assert(self@ == old(self)@.remove(i as int));

                    // All regions are still valid
                    assert(forall|j: int|
                        0 <= j < self.regions.len() ==> #[trigger] self.regions[j].spec_valid());
                    // All regions are still non-overlapping
                    assert(forall|i: int, j: int|
                        0 <= i < self.regions.len() && 0 <= j < self.regions.len() && i != j
                            ==> !self.regions[i].spec_overlaps(self.regions[j]));
                    // All regions are mapped in the page table
                    assert forall|i: int|
                        0 <= i < self.regions.len() implies #[trigger] self.has_mapping_for(
                        self.regions[i],
                    ) by {
                        // TODO
                        assume(false);
                    }
                }

                return Ok(());
            }
        }
        // Region not found
        assert(!exists|i: int|
            0 <= i < self.regions.len() && #[trigger] self.regions[i].start@ == start@);
        Err(())
    }
    */

}

proof fn lemma_regions_not_overlaps_implies_pages_disjoint(
    region1: MemoryRegion,
    region2: MemoryRegion,
    p: nat,
    q: nat,
)
    requires
        region1.spec_valid(),
        region2.spec_valid(),
        p < region1.pages as nat,
        q < region2.pages as nat,
        !region1.spec_overlaps(region2),
    ensures
        !SpecVAddr::overlap(
            region1.start@,
            p * PAGE_SIZE as nat,
            region2.start@,
            q * PAGE_SIZE as nat,
        ),
{
}

} // verus!
