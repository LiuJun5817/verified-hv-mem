//! `VecMemorySet`: the concrete `MemorySet` implementation backed by a `Vec` of
//! regions and a hierarchical page table `PT`.  It discharges the `MemorySet`
//! contract from `super` — in particular the region <-> mapping consistency the
//! higher-level security proof relies on.
//!
//! View-expression convention: `self@` is the abstract [`SpecMemorySet`] (used in
//! the `MemorySet` postconditions), while `self.pt@` is the concrete page table
//! (used inside the proofs).  Because `self@.mappings` is *defined* as
//! `self.pt@.mappings`, the two coincide on `mappings`; we deliberately keep both
//! spellings to mark which layer each statement is reasoning about.
use super::tlb::gpa_of_vaddr;
use super::*;
use crate::address::addr::{PAddr, SpecVAddr};
use crate::bitmap_allocator::bitmap_trait::BitmapAllocator;
use crate::hardware::{HardwareInst, MmuHardware};
use crate::machine::hardware::mmu::lemma_invalidate_clears_page;
use crate::machine::types::{CpuId, GuestPage, TlbKey, VmId};
use crate::page_table::{PTConstants, PageTable};
use vstd::prelude::*;

verus! {

broadcast use crate::page_table::PageTable::lemma_invariants_implies_wf;

/// Memory set implementation using a vector of memory regions.
pub struct VecMemorySet<PT, A, I> where PT: PageTable<A>, A: BitmapAllocator, I: HardwareInst {
    /// The list of memory regions in the memory set.
    pub regions: Vec<MemoryRegion>,
    /// Page table managing the mappings.
    pub pt: PT,
    /// Phantom data for the page table memory type.
    pub phantom: PhantomData<(A, I)>,
}

impl<PT, A, I> VecMemorySet<PT, A, I> where PT: PageTable<A>, A: BitmapAllocator, I: HardwareInst {
    /// If a region is mapped in the page table.
    ///
    /// TODO: For now we only support 4KB pages, so we use `mappings.contains_key` to simplify the proof.
    /// In the future if we want to support huge pages, we may use `pt.has_mapping_for` instead.
    pub open spec fn has_mapping_for(&self, region: MemoryRegion) -> bool {
        forall|i: nat|
            i < region.pages ==> #[trigger] self.pt@.mappings.contains_pair(
                region.spec_page_vaddr(i),
                region.spec_frame(i),
            )
    }

    /// If there is region contains the given virtual frame.
    pub open spec fn has_region_for(&self, vbase: SpecVAddr, frame: SpecFrame) -> bool {
        exists|i: int, j: nat|
            0 <= i < self.regions.len() && j < self.regions[i].pages && vbase
                == self.regions[i].spec_page_vaddr(j) && frame == self.regions[i].spec_frame(j)
    }

    /// If there is region other than `ridx` contains the given virtual frame.
    pub open spec fn has_region_for_except(
        &self,
        vbase: SpecVAddr,
        frame: SpecFrame,
        ridx: int,
    ) -> bool {
        exists|i: int, j: nat|
            0 <= i < self.regions.len() && i != ridx && j < self.regions[i].pages && vbase
                == self.regions[i].spec_page_vaddr(j) && frame == self.regions[i].spec_frame(j)
    }

    /// Lemma: two regions cannot have the same starting virtual address.
    proof fn lemma_region_start_unique(self)
        requires
            self.invariants(),
        ensures
            forall|i: int, j: int|
                #![auto]
                0 <= i < self.regions.len() && 0 <= j < self.regions.len() && i != j
                    ==> self.regions[i].vstart@ != self.regions[j].vstart@,
    {
        if exists|i: int, j: int|
            #![auto]
            0 <= i < self.regions.len() && 0 <= j < self.regions.len() && i != j
                && self.regions[i].vstart@ == self.regions[j].vstart@ {
            let (i, j) = choose|i: int, j: int|
                #![auto]
                0 <= i < self.regions.len() && 0 <= j < self.regions.len() && i != j
                    && self.regions[i].vstart@ == self.regions[j].vstart@;
            assert(self.regions[i].spec_valid());
            assert(self.regions[j].spec_valid());
            assert(self.regions[i].spec_overlaps_vmem(self.regions[j]));
        }
    }
}

impl<PT, A, I> MemorySet<PT, A, I> for VecMemorySet<PT, A, I> where
    PT: PageTable<A>,
    A: BitmapAllocator,
    I: HardwareInst,
 {
    open spec fn view(&self) -> SpecMemorySet {
        SpecMemorySet {
            regions: Set::new(
                |r: MemoryRegion|
                    exists|i: int| 0 <= i < self.regions.len() && self.regions[i] == r,
            ),
            // The real page-table state; `invariants()` (and the `has_mapping_for`
            // / `has_region_for` clauses) constrain it to be region-dense.
            mappings: self.pt@.mappings,
        }
    }

    open spec fn inst_id(&self) -> InstanceId {
        self.pt.inst_id()
    }

    open spec fn invariants(&self) -> bool {
        &&& self.pt@.constants.valid()
        // Frame size is 4K
        &&& self.pt@.constants.arch.leaf_frame_size()
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
            // Exact-dense consistency (completeness): every region page is mapped to
            // exactly its frame.
        &&& forall|r: MemoryRegion| #[trigger]
            self.regions@.contains(r) ==> self.has_mapping_for(
                r,
            )
        // Exact-dense consistency (soundness): every mapping is exactly some
        // region page's frame.
        &&& forall|v: SpecVAddr, f: SpecFrame| #[trigger]
            self.pt@.mappings.contains_pair(v, f) ==> self.has_region_for(v, f)
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
                forall|j: int| #![auto] 0 <= j < i ==> self.regions[j].vstart@ != v@,
        {
            let r = &self.regions[i];
            if r.vstart.0 == v.0 {
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
        // (completeness trigger) every existing region is in `regions@`, so
        // `invariants()` gives `has_mapping_for` for each — establishes the loop
        // invariant's completeness clause.
        assert forall|j: int| 0 <= j < self.regions.len() implies #[trigger] self.has_mapping_for(
            self.regions[j],
        ) by {
            assert(self.regions@.contains(self.regions[j]));
        }
        let mut i: usize = 0;
        while i < region.pages
            invariant
                region.spec_valid(),
                i <= region.pages,
                i == 0 ==> self.invariants(),
                self.pt.invariants(),
                self.pt.inst_id() == allocator.inst_id(),
                allocator.invariants(),
                self.pt@.constants == old(self).pt@.constants,
                self.pt@.constants.valid(),
                self.pt@.constants.arch.leaf_frame_size() == FrameSize::Size4K,
                self.regions == old(self).regions,
                // Old regions do not overlap with each other
                forall|j: int|
                    0 <= j < self.regions.len() ==> !region.spec_overlaps_vmem(
                        #[trigger] self.regions[j],
                    ),
                // New region does not overlap with any old region
                !self@.overlaps_vmem(region),
                // (completeness) old regions are mapped in the page table
                forall|j: int|
                    0 <= j < self.regions.len() ==> #[trigger] self.has_mapping_for(
                        self.regions[j],
                    ),
                // (completeness) the first `i` pages map to their frames
                forall|k: nat|
                    k < i ==> #[trigger] self.pt@.mappings.contains_pair(
                        region.spec_page_vaddr(k),
                        region.spec_frame(k),
                    ),
                // (soundness) old mappings are preserved
                forall|vb: SpecVAddr, fr: SpecFrame|
                    old(self).pt@.mappings.contains_pair(vb, fr)
                        ==> #[trigger] self.pt@.mappings.contains_pair(vb, fr),
                // (soundness) every mapping is an old region's page or one of `region`'s first `i` pages
                forall|vb: SpecVAddr, fr: SpecFrame| #[trigger]
                    self.pt@.mappings.contains_pair(vb, fr) ==> self.has_region_for(vb, fr) || (
                    exists|k: nat|
                        0 <= k < i && vb == region.spec_page_vaddr(k) && fr == region.spec_frame(
                            k,
                        )),
            decreases region.pages - i,
        {
            let vbase = VAddr(region.vstart.0 + i * PAGE_SIZE);
            let paddr = PAddr(region.pstart.0 + i * PAGE_SIZE);
            // TODO: support huge pages
            let frame = Frame { base: paddr, size: FrameSize::Size4K, attr: region.attr.clone() };

            proof {
                assert(vbase@.within(region.vstart@, region.pages as nat * SPEC_PAGE_SIZE));
                // vbase not within any existing region
                assert forall|j: int| #![auto] 0 <= j < self.regions.len() implies !vbase@.within(
                    self.regions[j].vstart@,
                    self.regions[j].pages as nat * SPEC_PAGE_SIZE,
                ) by {
                    let r = self.regions[j];
                    assert(!region.spec_overlaps_vmem(r));
                    if vbase@.within(r.vstart@, r.pages as nat * SPEC_PAGE_SIZE) {
                        assert(region.spec_overlaps_vmem(r));
                    }
                };
                // (vbase, frame) does not overlap with any existing region
                assert(forall|j: int|
                    #![auto]
                    0 <= j < self.regions.len() ==> !SpecVAddr::overlap(
                        vbase@,
                        frame.size.as_nat(),
                        self.regions[j].vstart@,
                        self.regions[j].pages as nat * SPEC_PAGE_SIZE,
                    ));
                if i > 0 {
                    // vbase not within the already mapped part of the new region
                    assert(!vbase@.within(region.vstart@, (i - 1) as nat * SPEC_PAGE_SIZE));
                    // (vbase, frame) does not overlap with the already mapped part of the new region
                    assert(!SpecVAddr::overlap(
                        vbase@,
                        frame.size.as_nat(),
                        region.vstart@,
                        (i - 1) as nat * SPEC_PAGE_SIZE,
                    ));
                }
                let mappings = self.pt@.mappings;
                // (vbase, frame) does not overlap with any existing mapping
                assert forall|vbase2: SpecVAddr| #[trigger]
                    mappings.contains_key(vbase2) implies !SpecVAddr::overlap(
                    vbase2,
                    mappings[vbase2].size.as_nat(),
                    vbase@,
                    frame.size.as_nat(),
                ) by {
                    let frame2 = mappings[vbase2];
                    assert(mappings.contains_pair(vbase2, frame2));
                    // every existing mapping is within an old region or the first `i` pages'
                    // interval, both vmem-disjoint from page `i`, so they cannot overlap `vbase`.
                }
                assert(!self.pt@.overlaps_vmem(vbase@, frame@));
                // `vbase`/`frame` are exactly region page `i` and its frame.
                assert(vbase@ == region.spec_page_vaddr(i as nat));
                assert(frame@ == region.spec_frame(i as nat));

                // TODO: edit precondition to require the new region is within the address space limit
                assume(vbase@.0 < self.pt@.constants.arch.vspace_size());
            }

            let ghost self_before_map = *self;
            let ghost old_mappings = self.pt@.mappings;
            let res = self.pt.map(allocator, vbase, frame);
            let ghost mappings = self.pt@.mappings;
            i += 1;

            proof {
                // Prove loop invariants
                assert(self.pt.invariants());
                assert(res.is_ok());
                assert(mappings == old_mappings.insert(vbase@, frame@));
                assert(mappings.contains_pair(vbase@, frame@));
                // (completeness) old regions are still mapped in the page table (the map only adds)
                assert forall|j: int|
                    0 <= j < self.regions.len() implies #[trigger] self.has_mapping_for(
                    self.regions[j],
                ) by {
                    let r2 = self.regions[j];
                    assert(self_before_map.has_mapping_for(r2));
                    assert forall|ii: nat|
                        ii < r2.pages implies #[trigger] self.pt@.mappings.contains_pair(
                        r2.spec_page_vaddr(ii),
                        r2.spec_frame(ii),
                    ) by {
                        assert(old_mappings.contains_pair(
                            r2.spec_page_vaddr(ii),
                            r2.spec_frame(ii),
                        ));
                    }
                }
                // (completeness) the first `i` pages map to their frames
                assert forall|k: nat| k < i implies #[trigger] self.pt@.mappings.contains_pair(
                    region.spec_page_vaddr(k),
                    region.spec_frame(k),
                ) by {
                    if k == i - 1 {
                        assert(region.spec_page_vaddr(k) == vbase@ && region.spec_frame(k)
                            == frame@);
                    } else {
                        assert(old_mappings.contains_pair(
                            region.spec_page_vaddr(k),
                            region.spec_frame(k),
                        ));
                    }
                }
                // (soundness) old mappings are preserved
                assert forall|vb: SpecVAddr, fr: SpecFrame|
                    old(self).pt@.mappings.contains_pair(
                        vb,
                        fr,
                    ) implies #[trigger] mappings.contains_pair(vb, fr) by {
                    assert(old_mappings.contains_pair(vb, fr));
                }
                // (soundness) every mapping is an old region's page or a first-`i` page of `region`
                assert forall|vb: SpecVAddr, fr: SpecFrame| #[trigger]
                    mappings.contains_pair(vb, fr) implies self.has_region_for(vb, fr) || (exists|
                    k: nat,
                |
                    0 <= k < i && vb == region.spec_page_vaddr(k) && fr == region.spec_frame(
                        k,
                    )) by {
                    if !old_mappings.contains_pair(vb, fr) {
                        assert(vb == vbase@ && fr == frame@);
                        assert(vb == region.spec_page_vaddr((i - 1) as nat) && fr
                            == region.spec_frame((i - 1) as nat));
                    }
                }
            }
        }

        // After the loop, the whole region is mapped in the page table
        assert(self.has_mapping_for(region));
        // Push the region into the list
        let ghost self_before_push = *self;
        self.regions.push(region);

        proof {
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
                    assert(self_before_push.has_mapping_for(self.regions[i]));
                }
            }
            // All mappings are within these regions: from the loop soundness (page
            // table unchanged by the push), every mapping is an old region's page
            // (still present) or a `region` page (now present).
            assert forall|vb: SpecVAddr, fr: SpecFrame| #[trigger]
                self.pt@.mappings.contains_pair(vb, fr) implies self.has_region_for(vb, fr) by {
                assert(self_before_push.pt@.mappings.contains_pair(vb, fr));
                if self_before_push.has_region_for(vb, fr) {
                    let (idx, j) = choose|idx: int, j: nat|
                        0 <= idx < self_before_push.regions.len() && j
                            < self_before_push.regions[idx].pages && vb
                            == self_before_push.regions[idx].spec_page_vaddr(j) && fr
                            == self_before_push.regions[idx].spec_frame(j);
                    assert(self.regions[idx] == self_before_push.regions[idx]);
                } else {
                    let k = choose|k: nat|
                        0 <= k < region.pages && vb == region.spec_page_vaddr(k) && fr
                            == region.spec_frame(k);
                    assert(self.regions[self.regions.len() - 1] == region);
                }
            }
            assert(self.invariants());

            // Prove the postcondition. The region set is exactly old regions + `region`.
            assert(self@.regions == old(self)@.regions.insert(region)) by {
                assert forall|r: MemoryRegion| #[trigger]
                    self@.regions.contains(r) <==> old(self)@.regions.insert(region).contains(
                        r,
                    ) by {
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
            }
            // Prove postcondition: the page table grew by exactly `region.spec_mappings()`.
            assert(self@.mappings =~= old(self)@.mappings.union_prefer_right(
                region.spec_mappings(),
            )) by {
                let old_pt_maps = old(self).pt@.mappings;
                let region_maps = region.spec_mappings();

                assert forall|v: SpecVAddr, f: SpecFrame|
                    #![trigger self.pt@.mappings.contains_pair(v, f)]
                    self.pt@.mappings.contains_pair(v, f) <==> old_pt_maps.union_prefer_right(
                        region_maps,
                    ).contains_pair(v, f) by {
                    // ==>
                    if self.pt@.mappings.contains_pair(v, f) {
                        assert(self_before_push.pt@.mappings.contains_pair(v, f));
                        if self_before_push.has_region_for(v, f) {
                            let (idx, j) = choose|idx: int, j: nat|
                                0 <= idx < self_before_push.regions.len() && j
                                    < self_before_push.regions[idx].pages && v
                                    == self_before_push.regions[idx].spec_page_vaddr(j) && f
                                    == self_before_push.regions[idx].spec_frame(j);
                            assert(old(self).regions@.contains(self_before_push.regions[idx]));
                            assert(old(self).has_mapping_for(self_before_push.regions[idx]));
                            assert(old_pt_maps.contains_pair(v, f));
                            assert(!region_maps.contains_key(v)) by {
                                if region_maps.contains_key(v) {
                                    let kk = choose|kk: nat|
                                        0 <= kk < region.pages && v == region.spec_page_vaddr(kk);
                                    MemoryRegion::lemma_pages_disjoint(
                                        region,
                                        self_before_push.regions[idx],
                                        kk,
                                        j,
                                    );
                                }
                            }
                        } else {
                            let k = choose|k: nat|
                                0 <= k < region.pages && v == region.spec_page_vaddr(k) && f
                                    == region.spec_frame(k);
                            region.lemma_mappings_contains_pair(k);
                        }
                    }
                    // <==

                    if old_pt_maps.union_prefer_right(region_maps).contains_pair(v, f) {
                        if region_maps.contains_key(v) {
                            region.lemma_mappings_sound(v);
                        } else {
                            assert(old_pt_maps.contains_pair(v, f));
                        }
                    }
                }
                lemma_map_eq_pair(old_pt_maps.union_prefer_right(region_maps), self.pt@.mappings);
            }
        }
    }

    fn remove(
        &mut self,
        allocator: &GlobalAllocator<A>,
        start: VAddr,
        vm: Ghost<VmId>,
        mmu: &mut MmuHardware<I>,
    ) {
        let len = self.regions.len();
        let mut i = 0;
        // Find the region with the given start address
        while i < len
            invariant
                len == self.regions.len(),
                0 <= i <= self.regions.len(),
                *self == *old(self),
                forall|j: int| 0 <= j < i ==> #[trigger] self.regions[j].vstart@ != start@,
            ensures
                i < len ==> self.regions[i as int].vstart@ == start@,
            decreases len - i,
        {
            if self.regions[i].vstart.0 == start.0 {
                break ;
            }
            i += 1;
        }
        if i == len {
            assert(false);  // contradicts precondition
        }
        proof {
            self.lemma_region_start_unique();
            assert(i == choose|i: int|
                0 <= i < self.regions.len() && #[trigger] self.regions[i].vstart@ == start@);
        }

        let ridx = i;
        let region = &self.regions[ridx];
        assert(region.vstart@ == start@);
        assert(self.regions@.contains(*region));  // regions[ridx] ∈ regions@ (completeness trigger)
        assert(self.has_mapping_for(*region));

        // (completeness trigger) every existing region is in `regions@`, so
        // `invariants()` gives `has_mapping_for` for each.
        assert forall|j: int| 0 <= j < self.regions.len() implies #[trigger] self.has_mapping_for(
            self.regions[j],
        ) by {
            assert(self.regions@.contains(self.regions[j]));
        }
        let mut i = 0;
        // Unmap + flush the region page by page
        while i < region.pages
            invariant
                region.spec_valid(),
                i <= region.pages,
                self.pt.invariants(),
                self.pt.inst_id() == allocator.inst_id(),
                allocator.invariants(),
                self.pt@.constants == old(self).pt@.constants,
                self.pt@.constants.valid(),
                self.pt@.constants.arch.leaf_frame_size() == FrameSize::Size4K,
                self.regions == old(self).regions,
                // No new mapping is added
                forall|vbase: SpecVAddr, frame: SpecFrame| #[trigger]
                    self.pt@.mappings.contains_pair(vbase, frame) ==> old(
                        self,
                    ).pt@.mappings.contains_pair(vbase, frame),
                // Region do not overlap with other regions
                forall|j: int|
                    0 <= j < self.regions.len() && j != ridx ==> !region.spec_overlaps_vmem(
                        #[trigger] self.regions[j],
                    ),
                // (completeness) Pages [i, region.pages) of the removed region are mapped
                forall|j: nat|
                    i <= j < region.pages ==> #[trigger] self.pt@.mappings.contains_pair(
                        region.spec_page_vaddr(j),
                        region.spec_frame(j),
                    ),
                // (completeness) Other regions are mapped in the page table
                forall|j: int|
                    0 <= j < self.regions.len() && j != ridx ==> #[trigger] self.has_mapping_for(
                        self.regions[j],
                    ),
                // (soundness) All mappings are within old regions or pages [i, region.pages)
                forall|vbase2: SpecVAddr, frame2: SpecFrame| #[trigger]
                    self.pt@.mappings.contains_pair(vbase2, frame2) ==> self.has_region_for_except(
                        vbase2,
                        frame2,
                        ridx as int,
                    ) || exists|j: nat|
                        i <= j < region.pages && vbase2 == region.spec_page_vaddr(j) && frame2
                            == region.spec_frame(j),
                // MMU forcing: the hardware TLB is clean for every page flushed so far.
                mmu.wf(),
                mmu.inst_id() == old(mmu).inst_id(),
                forall|j: nat, cpu: CpuId|
                    j < i ==> !(#[trigger] mmu.tlb_view().contains_key(
                        TlbKey::new(cpu, vm@, gpa_of_vaddr(region.spec_page_vaddr(j))),
                    )),
            decreases region.pages - i,
        {
            let vaddr = VAddr(region.vstart.0 + i * PAGE_SIZE);
            proof {
                assert(vaddr@.0 % SPEC_PAGE_SIZE == 0);
                assert(self.pt@.mappings.contains_pair(
                    region.spec_page_vaddr(i as nat),
                    region.spec_frame(i as nat),
                ));
                assume(vaddr@.0 < self.pt@.constants.arch.vspace_size());
            }

            let ipa_page = vaddr.0 / PAGE_SIZE;
            let ghost self_before_unmap = *self;
            let ghost old_mappings = self.pt@.mappings;
            let res = self.pt.unmap(allocator, vaddr);
            // FORCED stage-2 invalidation of this page on the tokenized MMU.  The
            // post-state TLB cleanliness below is provable only because this real
            // `TLBI` runs (the encapsulated instance is the sole TLB mutator).
            let ghost view_before = mmu.tlb_view();
            mmu.tlbi(ipa_page, vm, Ghost(GuestPage(ipa_page as nat)));
            let ghost mappings = self.pt@.mappings;
            i += 1;

            proof {
                // ── Mapping invariants (verbatim from `MemorySet::remove`) ──
                assert(self.pt.invariants());
                assert(res.is_ok());
                assert(mappings == old_mappings.remove(vaddr@));
                assert forall|vbase: SpecVAddr, frame: SpecFrame| #[trigger]
                    self.pt@.mappings.contains_pair(vbase, frame) implies old(
                    self,
                ).pt@.mappings.contains_pair(vbase, frame) by {
                    assert(old_mappings.contains_pair(vbase, frame));
                }
                assert forall|j: nat|
                    i <= j < region.pages implies #[trigger] self.pt@.mappings.contains_pair(
                    region.spec_page_vaddr(j),
                    region.spec_frame(j),
                ) by {
                    if j == i - 1 {
                        assert(region.spec_page_vaddr(j) == vaddr@ && region.spec_frame(j)
                            == old_mappings[vaddr@]);
                    } else {
                        assert(old_mappings.contains_pair(
                            region.spec_page_vaddr(j),
                            region.spec_frame(j),
                        ));
                    }
                }
                assert forall|j: int|
                    0 <= j < self.regions.len() && j
                        != ridx implies #[trigger] self.has_mapping_for(self.regions[j]) by {
                    let r2 = self.regions[j];
                    assert(self_before_unmap.has_mapping_for(r2));
                    assert forall|ii: nat|
                        ii < r2.pages implies #[trigger] self.pt@.mappings.contains_pair(
                        r2.spec_page_vaddr(ii),
                        r2.spec_frame(ii),
                    ) by {
                        assert(old_mappings.contains_pair(
                            r2.spec_page_vaddr(ii),
                            r2.spec_frame(ii),
                        ));
                    }
                }
                assert forall|vbase2: SpecVAddr, frame2: SpecFrame| #[trigger]
                    mappings.contains_pair(vbase2, frame2) implies self.has_region_for_except(
                    vbase2,
                    frame2,
                    ridx as int,
                ) || exists|j: nat|
                    i <= j < region.pages && vbase2 == region.spec_page_vaddr(j) && frame2
                        == region.spec_frame(j) by {
                    if !self.has_region_for_except(vbase2, frame2, ridx as int) {
                        assert(old_mappings.contains_pair(vbase2, frame2));
                        assert(!self_before_unmap.has_region_for_except(
                            vbase2,
                            frame2,
                            ridx as int,
                        ));
                    }
                }
                // ── MMU forcing (the per-page stage-2 TLBI) ──
                assert(PAGE_SIZE as nat == SPEC_PAGE_SIZE);
                assert(GuestPage(ipa_page as nat) == gpa_of_vaddr(vaddr@));
                // Maintenance: the page just flushed (index i-1) is clean,
                // and earlier pages stay clean (a `TLBI` only removes entries).
                lemma_invalidate_clears_page(view_before, vm@, GuestPage(ipa_page as nat));
                assert(region.spec_page_vaddr((i - 1) as nat) == vaddr@);
                assert(gpa_of_vaddr(vaddr@) == GuestPage(ipa_page as nat));
                assert forall|j: nat, cpu: CpuId| j < i implies !(
                #[trigger] mmu.tlb_view().contains_key(
                    TlbKey::new(cpu, vm@, gpa_of_vaddr(region.spec_page_vaddr(j))),
                )) by {
                    if j < (i - 1) as nat {
                        assert(!view_before.contains_key(
                            TlbKey::new(cpu, vm@, gpa_of_vaddr(region.spec_page_vaddr(j))),
                        ));
                    } else {
                        assert(region.spec_page_vaddr(j) == vaddr@);
                    }
                }
            }
        }

        // Capture the loop's TLB-clean result over a ghost copy of `region`, since the
        // `region` borrow ends at the `self.regions.remove` below (and the MMU is not
        // touched after this, so the fact survives to the post-condition).
        let ghost rr = *region;
        assert forall|j: nat, cpu: CpuId| j < rr.pages implies !(
        #[trigger] mmu.tlb_view().contains_key(
            TlbKey::new(cpu, vm@, gpa_of_vaddr(rr.spec_page_vaddr(j))),
        )) by {
            assert(region.spec_page_vaddr(j) == rr.spec_page_vaddr(j));
        }

        // Remove the region from the list (does not touch the page table or TLB).
        let ghost self_before_remove = *self;
        self.regions.remove(ridx);

        proof {
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
                    assert(self_before_remove.has_mapping_for(self.regions[i]));
                } else {
                    assert(self.regions[i] == old(self).regions[i + 1]);
                    assert(self_before_remove.has_mapping_for(self.regions[i]));
                }
            }
            // All mappings in the page table are within these regions
            assert forall|vbase2: SpecVAddr, frame2: SpecFrame| #[trigger]
                self.pt@.mappings.contains_pair(vbase2, frame2) implies self.has_region_for(
                vbase2,
                frame2,
            ) by {
                assert(self_before_remove.has_region_for_except(vbase2, frame2, ridx as int));
                let (j, _) = choose|j: int, k: nat|
                    0 <= j < self_before_remove.regions.len() && k
                        < self_before_remove.regions[j].pages && vbase2
                        == self_before_remove.regions[j].spec_page_vaddr(k) && frame2
                        == self_before_remove.regions[j].spec_frame(k);
                if j < ridx {
                    assert(self_before_remove.regions[j] == self.regions[j]);
                } else {
                    assert(self_before_remove.regions[j] == self.regions[j - 1]);
                }
            }
            assert(self.invariants());

            // Postcondition: region set is old regions - `region`.
            let removed = old(self).regions[ridx as int];
            assert(self@.regions =~= old(self)@.regions.remove(removed)) by {
                assert forall|r: MemoryRegion| #[trigger]
                    self@.regions.contains(r) <==> old(self)@.regions.remove(removed).contains(
                        r,
                    ) by {
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
                }
            }
            // Postcondition: the page table shrinks by exactly `region.spec_mappings()`.
            assert(self@.mappings =~= old(self)@.mappings.remove_keys(
                removed.spec_mappings().dom(),
            )) by {
                let old_pt_maps = old(self).pt@.mappings;
                let region_maps = region.spec_mappings();

                assert forall|v: SpecVAddr, f: SpecFrame|
                    #![trigger self.pt@.mappings.contains_pair(v, f)]
                    self.pt@.mappings.contains_pair(v, f) <==> old_pt_maps.remove_keys(
                        region_maps.dom(),
                    ).contains_pair(v, f) by {
                    if self.pt@.mappings.contains_pair(v, f) {
                        assert(old_pt_maps.contains_pair(v, f));
                        assert(!region_maps.contains_key(v)) by {
                            if region_maps.contains_key(v) {
                                region.lemma_mappings_sound(v);
                            }
                        };
                        assert(old_pt_maps.remove_keys(region_maps.dom()).contains_pair(v, f));
                    }
                    if old_pt_maps.remove_keys(region_maps.dom()).contains_pair(v, f) {
                        assert(old(self)@.mappings.contains_pair(v, f));
                        if self.has_region_for(v, f) {
                            let (j, k) = choose|j: int, k: nat|
                                0 <= j < self.regions.len() && k < self.regions[j].pages && v
                                    == self.regions[j].spec_page_vaddr(k) && f
                                    == self.regions[j].spec_frame(k);
                            assert(self.regions@.contains(self.regions[j]));
                            assert(self@.mappings.contains_pair(v, f));
                        } else {
                            let (j, k) = choose|j: int, k: nat|
                                0 <= j < old(self).regions.len() && k < old(self).regions[j].pages
                                    && v == old(self).regions[j].spec_page_vaddr(k) && f == old(
                                    self,
                                ).regions[j].spec_frame(k);
                            if j < ridx {
                                assert(old(self).regions[j] == self.regions[j]);
                            } else if j > ridx {
                                assert(old(self).regions[j] == self.regions[j - 1]);
                            } else {
                                assert(old(self).regions[j] == removed);
                                assert(region_maps.contains_pair(v, f));
                            }
                        }
                    }
                }
                lemma_map_eq_pair(old_pt_maps.remove_keys(region_maps.dom()), self.pt@.mappings);
            }
            // FORCED tlb-clean post: each removed mapping is a page of `removed`, and
            // every page of `removed` was flushed by the per-page `TLBI` above.
            assert(rr == removed);
            assert forall|va: SpecVAddr, cpu: CpuId|
                old(self)@.mappings.contains_key(va) && !self@.mappings.contains_key(
                    va,
                ) implies !mmu.tlb_view().contains_key(TlbKey::new(cpu, vm@, gpa_of_vaddr(va))) by {
                // `self@.mappings == old@.mappings.remove_keys(removed.spec_mappings().dom())`,
                // so a removed key lies in `removed.spec_mappings().dom()`.
                assert(removed.spec_mappings().dom().contains(va));
                removed.lemma_mappings_sound(va);
                let j = choose|k: nat| 0 <= k < removed.pages && va == removed.spec_page_vaddr(k);
                assert(!mmu.tlb_view().contains_key(
                    TlbKey::new(cpu, vm@, gpa_of_vaddr(removed.spec_page_vaddr(j))),
                ));
            }
        }
    }

    proof fn lemma_invariants_implies_wf(self) {
        assert forall|r: MemoryRegion| #[trigger]
            self@.regions.contains(r) implies r.spec_valid() by {
            let i = choose|i: int| 0 <= i < self.regions.len() && self.regions[i] == r;
            assert(self.regions[i].spec_valid());
        };
        assert forall|r1: MemoryRegion, r2: MemoryRegion|
            self@.regions.contains(r1) && self@.regions.contains(r2) && r1
                != r2 implies !r1.spec_overlaps_vmem(r2) by {
            let i = choose|i: int| 0 <= i < self.regions.len() && self.regions[i] == r1;
            let j = choose|j: int| 0 <= j < self.regions.len() && self.regions[j] == r2;
            assert(i != j);
            assert(!self.regions[i].spec_overlaps_vmem(self.regions[j]));
        };
        // completeness: a region of the view is one of the `regions` (so
        // `invariants()`'s `has_mapping_for` applies) and gives the frame.
        assert forall|r: MemoryRegion, i: nat|
            #![trigger self@.regions.contains(r), r.spec_page_vaddr(i)]
            self@.regions.contains(r) && 0 <= i < r.pages implies self@.mappings.contains_pair(
            r.spec_page_vaddr(i),
            r.spec_frame(i),
        ) by {
            assert(self.regions@.contains(r));
            assert(self.has_mapping_for(r));
        }
        // soundness: a mapping is some `regions[idx]`'s page (from `has_region_for`),
        // and `regions[idx]` is a region of the view.
        assert forall|v: SpecVAddr, f: SpecFrame| #[trigger]
            self@.mappings.contains_pair(v, f) implies exists|r: MemoryRegion, i: nat|
            #![trigger self@.regions.contains(r), r.spec_page_vaddr(i)]
            self@.regions.contains(r) && 0 <= i < r.pages && v == r.spec_page_vaddr(i) && f
                == r.spec_frame(i) by {
            assert(self.has_region_for(v, f));
            let (idx, j) = choose|idx: int, j: nat|
                0 <= idx < self.regions.len() && j < self.regions[idx].pages && v
                    == self.regions[idx].spec_page_vaddr(j) && f == self.regions[idx].spec_frame(j);
            assert(self@.regions.contains(self.regions[idx]));
        }
    }
}

/// Lemma. The equality of two maps. Two maps are equal if
/// - they have the same keys
/// - they have the same values for the same keys
pub proof fn lemma_map_eq_key_value<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    requires
        forall|k| m1.contains_key(k) ==> m2.contains_key(k),
        forall|k| m2.contains_key(k) ==> m1.contains_key(k),
        forall|k| #[trigger] m1.contains_key(k) ==> m1[k] === m2[k],
    ensures
        m1 === m2,
{
    assert(m1 === m2)
}

/// Lemma. The equality of two maps. Two maps are equal if they have the same (key, value) pairs.
pub proof fn lemma_map_eq_pair<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    requires
        forall|k, v| m1.contains_pair(k, v) ==> m2.contains_pair(k, v),
        forall|k, v| m2.contains_pair(k, v) ==> m1.contains_pair(k, v),
    ensures
        m1 === m2,
{
    assert forall|k| m1.contains_key(k) implies m2.contains_key(k) by {
        assert(m2.contains_pair(k, m1[k]));
    };
    assert forall|k| m2.contains_key(k) implies m1.contains_key(k) by {
        assert(m1.contains_pair(k, m2[k]));
    };
    assert forall|k| #[trigger] m1.contains_key(k) implies m1[k] === m2[k] by {
        let v = m1.index(k);
        assert(m1.contains_pair(k, v));
        assert(m2.contains_pair(k, v));
    }
    assert(m1 === m2) by {
        lemma_map_eq_key_value(m1, m2);
    }
}

} // verus!
