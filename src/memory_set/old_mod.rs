//! A memory set is a collection of memory areas that can be mapped into the virtual address
//! space of a zone (process). It manages the page table for the zone, and provides methods to
//! insert, remove, and find memory areas.
use crate::{
    address::{
        addr::{SpecVAddr, VAddr},
        frame::{self, Frame, FrameSize, MemoryRegion, SpecFrame, PAGE_SIZE},
    },
    page_table::{pt_trait::{PageTableState, PagingResult}, PageTable, PageTableMem},
};
use std::marker::PhantomData;
use vstd::{invariant, prelude::*};

verus! {

proof fn lemma_map_preserves_has_mapping_for(
    s1: PageTableState,
    s2: PageTableState,
    vbase: SpecVAddr,
    frame: SpecFrame,
    res: PagingResult,
)
    requires
        PageTableState::map(s1, s2, vbase, frame, res),
    ensures
        forall|vaddr: SpecVAddr| s1.has_mapping_for(vaddr) ==> s2.has_mapping_for(vaddr),
{
    assert forall|vaddr: SpecVAddr|
        s1.has_mapping_for(vaddr) implies s2.has_mapping_for(vaddr) by {
        if res is Err {
            assert(s1.mappings === s2.mappings);
        } else {
            assert(!s1.overlaps_vmem(vbase, frame));
            assert(s2.mappings === s1.mappings.insert(vbase, frame));
            let (vbase2, frame2) = s1.mapping_for(vaddr);
            assert(s1.mappings.contains_pair(vbase2, frame2));
            assert(vaddr.within(vbase2, frame2.size.as_nat()));
            if vbase2 == vbase {
                assert(SpecVAddr::overlap(
                    vbase2,
                    frame2.size.as_nat(),
                    vbase,
                    frame.size.as_nat(),
                ));
                assert(s1.overlaps_vmem(vbase, frame));
            }
            assert(vbase2 != vbase);
            assert(s1.mappings.insert(vbase, frame).contains_pair(vbase2, frame2));
        }
    }
}

/// Specification of a memory set viewed by higher-level components.
pub trait MemorySet {
    /// View the memory set as a list of memory regions.
    spec fn view(self) -> Seq<MemoryRegion>;

    /// Invariants that must be implied at initial state and preseved after each operation.
    spec fn invariants(self) -> bool;

    /// Insert a new memory region into the memory set.
    fn insert(&mut self, region: MemoryRegion) -> (res: Result<(), ()>)
        requires
            old(self).invariants(),
            region.spec_valid(),
        ensures
            // self.invariants(),
            // if res is Err {
            //     &&& self@ == old(self)@
            // } else {
            //     &&& self@ == old(self)@.push(region)
            //     &&& self.invariants()
            // },
            if exists|i: int|
                0 <= i < old(self)@.len() && #[trigger] old(self)@[i].spec_overlaps(region) {
                &&& res is Err
                &&& self@ == old(self)@
            } else {
                &&& res is Ok
                &&& self@ == old(self)@.push(region)
                &&& self.invariants()
            },
    ;

    /// Remove a memory region from the memory set by its starting virtual address.
    fn remove(&mut self, start: VAddr) -> (res: Result<(), ()>)
        requires
            old(self).invariants(),
        ensures
            // self.invariants(),
            if exists|i: int|
                0 <= i < old(self)@.len() && #[trigger] old(self)@[i].start@ == start@ {
                let i = choose|i: int|
                    0 <= i < old(self)@.len() && #[trigger] old(self)@[i].start@ == start@;
                &&& res is Ok
                &&& self@ == old(self)@.remove(i)
                &&& self.invariants()
            } else {
                &&& res is Err
                &&& self@ == old(self)@
            },
    ;
}

/// Memory set implementation using a vector of memory regions.
pub struct VecMemorySet<M, PT> where PT: PageTable<M>, M: PageTableMem {
    /// The list of memory regions in the memory set.
    pub regions: Vec<MemoryRegion>,
    /// Page table managing the mappings.
    pub pt: PT,
    /// Phantom data for the page table memory type.
    pub phantom: PhantomData<M>,
}

impl<M, PT> VecMemorySet<M, PT> where PT: PageTable<M>, M: PageTableMem {
    /// If a region is mapped in the page table.
    pub open spec fn has_mapping_for(self, region: MemoryRegion) -> bool {
        forall|page_idx: nat|
            page_idx < region.pages ==> #[trigger] self.pt@.has_mapping_for(
                region.start@.offset(page_idx * PAGE_SIZE as nat),
            )
    }

    /// Spec-mode overlap check.
    pub open spec fn spec_overlaps(self, region: MemoryRegion) -> bool {
        exists|i: int|
            0 <= i < self.regions.len() && #[trigger] self.regions[i].spec_overlaps(region)
    }

    /// Check if a region overlaps with any existing region.
    pub fn overlaps(&self, region: &MemoryRegion) -> (res: bool)
        requires
            self.invariants(),
            region.spec_valid(),
        ensures
            res == self.spec_overlaps(*region),
    {
        for i in 0..self.regions.len()
            invariant
                0 <= i <= self.regions.len(),
                region.spec_valid(),
                self.invariants(),
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
    proof fn lemma_overlaps_equiv(self, region: MemoryRegion)
        requires
            self.invariants(),
            region.spec_valid(),
        ensures
            self.spec_overlaps(region) == exists|i: int|
                0 <= i < self@.len() && #[trigger] self@[i].spec_overlaps(region),
    {
        if self.spec_overlaps(region) {
            let i = choose|i: int|
                {
                    &&& 0 <= i < self.regions.len()
                    &&& #[trigger] self.regions[i].spec_overlaps(region)
                };
            assert(self@[i] == self.regions[i]);
        }
    }
}

impl<M, PT> MemorySet for VecMemorySet<M, PT> where PT: PageTable<M>, M: PageTableMem {
    open spec fn view(self) -> Seq<MemoryRegion> {
        Seq::new(self.regions.len() as nat, |i| self.regions[i])
    }

    open spec fn invariants(self) -> bool {
        &&& self.pt@.constants.valid()
        // Frame size is 4K
        &&& self.pt.view().constants.arch.leaf_frame_size() == FrameSize::Size4K
        // Page table invariants
        &&& self.pt.invariants()
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
        // &&& forall|vaddr: SpecVAddr|
        //     self.pt@.has_mapping_for(vaddr) ==> exists|i: int|
        //         {
        //             &&& 0 <= i < self.regions.len()
        //             &&& #[trigger] vaddr.within(
        //                 self.regions[i].start@,
        //                 self.regions[i].pages as nat * PAGE_SIZE as nat,
        //             )
        //         }
        &&& forall|vbase: SpecVAddr, frame: SpecFrame|
            self.pt@.mappings.contains_pair(vbase, frame) ==>
                (exists|i: int|
                    0 <= i < self.regions.len()
                    && #[trigger] SpecVAddr::interval_subset(
                        vbase,
                        frame.size.as_nat(),
                        self.regions[i].start@,
                        self.regions[i].pages as nat * PAGE_SIZE as nat,
                    )
                )
        // All regions are mapped in the page table
        &&& forall|i: int|
            0 <= i < self.regions.len() ==> #[trigger] self.has_mapping_for(self.regions[i])
    }

    fn insert(&mut self, region: MemoryRegion) -> (res: Result<(), ()>) {
        proof {
            self.lemma_overlaps_equiv(region);
        }
        if self.overlaps(&region) {
            return Err(());
        }
        assert(!self.spec_overlaps(region));
        assert(forall|j:int|
                0 <= j < self.regions.len() ==>
                    !self.regions[j].spec_overlaps(region)); // old_regions not overlap new region
        assert forall|j:int|
                0 <= j < self.regions.len() implies
                    !region.spec_overlaps(self.regions[j]) by{
                        self.regions[j].lemma_overlaps_symmetric(region);
                    };                                       // new region not overlap old regions
        
        // Map the region in the page table
        let mut i:usize = 0;
        while i < region.pages
            invariant
                region.spec_valid(),
                self.pt.invariants(),
                self.pt@.constants == old(self).pt@.constants,
                self.pt@.constants.valid(),
                self.pt@.constants.arch.leaf_frame_size() == FrameSize::Size4K,
                self@ == old(self)@,
                // self.invariants(), 对pt做了map的更新，所以这里不再满足
                old(self).invariants(),
                forall|j:int|
                    0 <= j < self.regions.len() ==>
                    !region.spec_overlaps(#[trigger] self.regions[j]),
                !self.spec_overlaps(region),
                forall|vbase2: SpecVAddr, frame2: SpecFrame|
                    self.pt@.mappings.contains_pair(vbase2, frame2) ==>
                        (exists|j: int|
                            0 <= j < self.regions.len()
                            && #[trigger] SpecVAddr::interval_subset(
                                vbase2,
                                frame2.size.as_nat(),
                                self.regions[j].start@,
                                self.regions[j].pages as nat * PAGE_SIZE as nat,
                            )
                        )
                    || SpecVAddr::interval_subset(
                        vbase2,
                        frame2.size.as_nat(),
                        region.start@,
                        i as nat * PAGE_SIZE as nat,
                    ),
            decreases
                region.pages - i,
        {
            let vaddr = VAddr(region.start.0 + i * PAGE_SIZE);

            assert(vaddr@.within(
                region.start@,
                region.pages as nat * PAGE_SIZE as nat,
            ));
            assert forall|j:int| 0 <= j < self.regions.len() implies // vaddr 不在旧 regions 里
                !vaddr@.within(
                    self.regions[j].start@,
                    self.regions[j].pages as nat * PAGE_SIZE as nat
                ) by {
                    let r = self.regions[j];
                    assert(!region.spec_overlaps(r));
                    if vaddr@.within(r.start@, r.pages as nat * PAGE_SIZE as nat) {
                        assert(region.spec_overlaps(r));
                    }
            };

            if i == 0 {                                             // vaddr不与新region中已经映射的页重叠
                assert(!vaddr@.within(region.start@, 0 as nat * PAGE_SIZE as nat));
            } else {
                assert(!vaddr@.within(region.start@, (i-1) as nat * PAGE_SIZE as nat));
            }

            
            
            let paddr = region.mapper.map(vaddr);
            // TODO: support huge pages
            let frame = Frame { base: paddr, size: FrameSize::Size4K, attr: region.attr.clone() };

            assert forall|j:int| 0 <= j < self.regions.len() implies
                #[trigger] SpecVAddr::overlap(
                    vaddr@,
                    frame.size.as_nat(),
                    self.regions[j].start@,
                    self.regions[j].pages as nat * PAGE_SIZE as nat
                ) == false by {
                    let r = self.regions[j];
                    assert(!region.spec_overlaps(r));
                    if SpecVAddr::overlap(
                        vaddr@,
                        frame.size.as_nat(),
                        r.start@,
                        r.pages as nat * PAGE_SIZE as nat
                    ) {
                        assert(region.spec_overlaps(r));
                    }
                };
            
            if i == 0 {
                assert(forall|v2: SpecVAddr|
                    self.pt@.has_mapping_for(v2) ==>
                        (exists|j:int| 0 <= j < self.regions.len()
                            && v2.within(#[trigger] self.regions[j].start@,
                                    self.regions[j].pages as nat * PAGE_SIZE as nat)));
                
                assert(forall|v2: SpecVAddr| self.pt@.has_mapping_for(v2) ==>
                    (exists|vbase: SpecVAddr, frame2: SpecFrame| {
                        &&& #[trigger] self.pt@.mappings.contains_pair(vbase, frame2)
                        &&& v2.within(vbase, frame2.size.as_nat())
                        &&& self.pt@.mappings.contains_key(vbase)
                    }));
            
                

                assert(forall|j:int| 0 <= j < self.regions.len() ==>
                    #[trigger] SpecVAddr::overlap(
                        vaddr@,
                        frame.size.as_nat(),
                        self.regions[j].start@,
                        self.regions[j].pages as nat * PAGE_SIZE as nat
                    ) == false);

                assert forall|vbase2: SpecVAddr| self.pt@.mappings.contains_key(vbase2) implies
                    !SpecVAddr::overlap(vbase2, self.pt@.mappings[vbase2].size.as_nat(), vaddr@, frame.size.as_nat())
                by {
                    assert(self.pt@.mappings.contains_pair(vbase2, self.pt@.mappings[vbase2]));
                    assert(self.pt@.has_mapping_for(vbase2));
                    assert((exists|j:int|
                        0 <= j < self.regions.len() // 证明 vbase2到frame2 在某个 region 内部
                        && #[trigger] SpecVAddr::interval_subset(vbase2, self.pt@.mappings[vbase2].size.as_nat(), self.regions[j].start@, self.regions[j].pages as nat * PAGE_SIZE as nat)));
                    assert(forall|j:int| 0 <= j < self.regions.len() ==>
                        #[trigger] SpecVAddr::overlap(  // 证明 vaddr@到frame 不与 region 重叠
                            vaddr@,                     
                            frame.size.as_nat(),
                            self.regions[j].start@,
                            self.regions[j].pages as nat * PAGE_SIZE as nat
                        ) == false);                    
                    assert(self.pt@.mappings.contains_key(vbase2) ==>
                        !SpecVAddr::overlap(vbase2, self.pt@.mappings[vbase2].size.as_nat(), vaddr@, frame.size.as_nat())
                    );
                };

                assert(!self.pt@.overlaps_vmem(vaddr@, frame@));

            } else {
                assert(SpecVAddr::overlap(
                    vaddr@,
                    frame@.size.as_nat(),
                    region.start@,
                    (i-1) as nat * PAGE_SIZE as nat
                ) == false);

                assert(forall|j:int| 0 <= j < self.regions.len() ==>
                    #[trigger] SpecVAddr::overlap(
                        vaddr@,
                        frame.size.as_nat(),
                        self.regions[j].start@,
                        self.regions[j].pages as nat * PAGE_SIZE as nat
                    ) == false);

                assert forall|vbase2: SpecVAddr| self.pt@.mappings.contains_key(vbase2) implies
                    !SpecVAddr::overlap(vbase2, self.pt@.mappings[vbase2].size.as_nat(), vaddr@, frame.size.as_nat())
                by {
                    assert(self.pt@.mappings.contains_pair(vbase2, self.pt@.mappings[vbase2]));

                    assert(self.pt@.has_mapping_for(vbase2));
                    
                    assert((exists|j:int|
                            0 <= j < self.regions.len() // 证明 vbase2到frame2 在某个 region 内部
                            && #[trigger] SpecVAddr::interval_subset(vbase2, self.pt@.mappings[vbase2].size.as_nat(), self.regions[j].start@, self.regions[j].pages as nat * PAGE_SIZE as nat))
                            || SpecVAddr::interval_subset(
                                    vbase2,
                                    self.pt@.mappings[vbase2].size.as_nat(),
                                    region.start@,
                                    i as nat * PAGE_SIZE as nat,
                                )
                            );
                    assert(forall|j:int| 0 <= j < self.regions.len() ==>
                        #[trigger] SpecVAddr::overlap(  // 证明 vaddr@到frame 不与 region 重叠
                            vaddr@,                     
                            frame.size.as_nat(),
                            self.regions[j].start@,
                            self.regions[j].pages as nat * PAGE_SIZE as nat
                        ) == false);                    
                    assert(self.pt@.mappings.contains_key(vbase2) ==>
                        !SpecVAddr::overlap(vbase2, self.pt@.mappings[vbase2].size.as_nat(), vaddr@, frame.size.as_nat())
                    );
                };

                assert(!self.pt@.overlaps_vmem(vaddr@, frame@));
            }
            
            assert(!self.spec_overlaps(region));
            assert(!self.pt@.overlaps_vmem(vaddr@, frame@));
            

            assert(self.pt.view().map_pre(vaddr@, frame@));

            let ghost old_pt = self.pt@;
            let res = self.pt.map(vaddr, frame);
            assert(self.pt@.mappings == old_pt.mappings.insert(vaddr@, frame@));
            assert(self.pt.invariants());
            assert(self.pt@.mappings.contains_pair(vaddr@, frame@));
            assert(SpecVAddr::interval_subset(
                        vaddr@,
                        frame@.size.as_nat(),
                        region.start@,
                        (i + 1) as nat * PAGE_SIZE as nat,
                    ));
            assert(res.is_ok());
            i += 1;
            assert(SpecVAddr::interval_subset(
                        vaddr@,
                        frame@.size.as_nat(),
                        region.start@,
                        i as nat * PAGE_SIZE as nat,
                    ));
            assert(forall|vbase2: SpecVAddr, frame2: SpecFrame|
                    old_pt.mappings.contains_pair(vbase2, frame2) ==>
                        (exists|j: int|
                            0 <= j < self.regions.len()
                            && #[trigger] SpecVAddr::interval_subset(
                                vbase2,
                                frame2.size.as_nat(),
                                self.regions[j].start@,
                                self.regions[j].pages as nat * PAGE_SIZE as nat,
                            )
                        )
                    || SpecVAddr::interval_subset(
                        vbase2,
                        frame2.size.as_nat(),
                        region.start@,
                        (i -1) as nat * PAGE_SIZE as nat,
                    ));
            assert forall|vbase2: SpecVAddr, frame2: SpecFrame|
                    self.pt@.mappings.contains_pair(vbase2, frame2) implies
                        (exists|j: int|
                            0 <= j < self.regions.len()
                            && #[trigger] SpecVAddr::interval_subset(
                                vbase2,
                                frame2.size.as_nat(),
                                self.regions[j].start@,
                                self.regions[j].pages as nat * PAGE_SIZE as nat,
                            )
                        )
                    || SpecVAddr::interval_subset(
                        vbase2,
                        frame2.size.as_nat(),
                        region.start@,
                        i as nat * PAGE_SIZE as nat,
                    ) by{
                        assert(
                            old_pt.mappings.contains_pair(vbase2, frame2) ==>
                                (exists|j: int|
                                    0 <= j < self.regions.len()
                                    && #[trigger] SpecVAddr::interval_subset(
                                        vbase2,
                                        frame2.size.as_nat(),
                                        self.regions[j].start@,
                                        self.regions[j].pages as nat * PAGE_SIZE as nat,
                                    )
                                )
                            || SpecVAddr::interval_subset(
                                vbase2,
                                frame2.size.as_nat(),
                                region.start@,
                                (i -1) as nat * PAGE_SIZE as nat,
                            ));
                        assert(self.pt@.mappings == old_pt.mappings.insert(vaddr@, frame@));
                        assert(self.pt@.mappings.contains_pair(vaddr@, frame@));
                        assert(SpecVAddr::interval_subset(
                                    vaddr@,
                                    frame@.size.as_nat(),
                                    region.start@,
                                    i as nat * PAGE_SIZE as nat,
                                ));
                    }
        }

        assert(self.has_mapping_for(region));
        // Push the region into the list
        self.regions.push(region);

        proof {
            assert(self@ == old(self)@.push(region));
            // All regions are still valid
            assert forall|i: int|
                0 <= i < self.regions.len() implies #[trigger] self.regions[i].spec_valid() by {
                if i < self.regions.len() - 1 {
                    assert(self.regions[i] == old(self)@[i]);
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
                        assert(!old(self)@[i].spec_overlaps(old(self)@[j]));
                    };
                }
            }
            // All regions are mapped in the page table
            assert(forall|i: int|
                0 <= i < self.regions.len() ==> #[trigger] self.has_mapping_for(
                self.regions[i]
            )) by {
                assert(forall|i: int|
                    0 <= i < old(self).regions.len() ==> #[trigger] old(self).has_mapping_for(
                        old(self).regions[i]));
            }
            assume(self@ == old(self)@.push(region));
            assume(self.invariants());
            // assert forall|i: int|
            //     0 <= i < self.regions.len() implies #[trigger] self.has_mapping_for(
            //     self.regions[i],
            // ) by {
            //     if i < self.regions.len() - 1 {
            //         assert(self.regions[i] == old(self)@[i]);
            //         assert forall|page_idx: nat|
            //             page_idx < self.regions[i].pages implies #[trigger] self.pt@.has_mapping_for(
            //             self.regions[i].start@.offset(page_idx * PAGE_SIZE as nat),
            //         ) by {
            //             assert(self.pt@.has_mapping_for(
            //                 old(self)@[i].start@.offset(page_idx * PAGE_SIZE as nat),
            //             ));
            //         };
            //     } else {
            //         assert(self.regions[i] == region);
            //         assert forall|page_idx: nat|
            //             page_idx < region.pages implies #[trigger] self.pt@.has_mapping_for(
            //             region.start@.offset(page_idx * PAGE_SIZE as nat),
            //         ) by {
            //             assert(self.pt@.has_mapping_for(
            //                 region.start@.offset(page_idx * PAGE_SIZE as nat),
            //             ));
            //         };
            //     }
            // }
        }

        Ok(())
    }

    fn remove(&mut self, start: VAddr) -> (res: Result<(), ()>) {
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
}

proof fn lemma_regions_not_overlaps_implies_pages_disjoint(region1: MemoryRegion, region2: MemoryRegion, p: nat, q: nat)
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
                &&& self.invariants(old(allocator))
            },
    ;
}
} // verus!
