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
use super::{MemorySet, SpecMemorySet};

extern crate alloc;

use crate::address::{
    addr::{PAddr, SpecPAddr, SpecVAddr, VAddr},
    frame::{Frame, FrameSize, MemAttr, SpecFrame},
};
use crate::bitmap_allocator::bitmap_trait::BitmapAllocator;
use crate::constants::*;
use crate::global_allocator::GlobalAllocator;
use crate::hardware::spec::MmuVmToken;
use crate::hardware::{HardwareInstr, MmuHardware};
use crate::model::types::{GuestPage, PhysPage, S2Entry, VmId};
use crate::page_table::{PTConstants, PageTable, SpecPTConstants};
use alloc::vec::Vec;
use core::marker::PhantomData;
use vstd::prelude::*;

verus! {

use crate::address::region::*;
use crate::model::convert::*;

broadcast use crate::page_table::PageTable::lemma_invariants_implies_wf;

/// Memory set implementation using a vector of memory regions.
pub struct VecMemorySet<PT, A, I> where PT: PageTable<A>, A: BitmapAllocator, I: HardwareInstr {
    /// The list of memory regions in the memory set.
    pub regions: Vec<MemoryRegion>,
    /// Page table managing the mappings.
    pub pt: PT,
    /// Phantom data for the page table memory type.
    pub phantom: PhantomData<(A, I)>,
}

impl<PT, A, I> VecMemorySet<PT, A, I> where PT: PageTable<A>, A: BitmapAllocator, I: HardwareInstr {
    /// Whether mappings in this memory set cover the given region.
    pub open spec fn has_mapping_for_region(&self, r: MemoryRegion) -> bool {
        forall|i: nat|
            i < r.pages ==> #[trigger] Self::mappings_cover_region_page(self.pt@.mappings, r, i)
    }

    /// Whether the given mapping is covered by some region in this memory set.
    pub open spec fn has_region_for_mapping(&self, vbase: SpecVAddr, frame: SpecFrame) -> bool {
        exists|i: int|
            #![auto]
            {
                &&& 0 <= i < self.regions.len()
                &&& self.regions[i].vstart@.0 <= vbase.0
                &&& vbase.0 + frame.size.as_nat() <= self.regions[i].vstart@.0
                    + self.regions[i].pages * SPEC_PAGE_SIZE
                &&& self.regions[i].pstart@.0 <= frame.base.0
                &&& frame.base.0 + frame.size.as_nat() <= self.regions[i].pstart@.0
                    + self.regions[i].pages * SPEC_PAGE_SIZE
                &&& frame.attr == self.regions[i].attr
            }
    }

    /// If there is region other than `ridx` contains the given virtual frame.
    pub open spec fn has_region_for_mapping_except(
        &self,
        vbase: SpecVAddr,
        frame: SpecFrame,
        ridx: int,
    ) -> bool {
        exists|i: int|
            #![auto]
            {
                &&& 0 <= i < self.regions.len()
                &&& i != ridx
                &&& self.regions[i].vstart@.0 <= vbase.0
                &&& vbase.0 + frame.size.as_nat() <= self.regions[i].vstart@.0
                    + self.regions[i].pages * SPEC_PAGE_SIZE
                &&& self.regions[i].pstart@.0 <= frame.base.0
                &&& frame.base.0 + frame.size.as_nat() <= self.regions[i].pstart@.0
                    + self.regions[i].pages * SPEC_PAGE_SIZE
                &&& frame.attr == self.regions[i].attr
            }
    }

    /// Select the unique region whose dense mapping contains `v`.
    pub open spec fn region_index_for_vaddr(&self, v: SpecVAddr) -> int
        recommends
            exists|i: int|
                0 <= i < self.regions.len()
                    && #[trigger] self.regions[i].spec_mappings().contains_key(v),
    {
        choose|i: int|
            0 <= i < self.regions.len() && #[trigger] self.regions[i].spec_mappings().contains_key(
                v,
            )
    }

    /// The abstract view of mappings in this memory set.
    pub open spec fn mappings_view(&self) -> Map<SpecVAddr, SpecFrame> {
        Map::new(
            |v: SpecVAddr|
                exists|i: int|
                    0 <= i < self.regions.len()
                        && #[trigger] self.regions[i].spec_mappings().contains_key(v),
            |v: SpecVAddr|
                {
                    let i = self.region_index_for_vaddr(v);
                    self.regions[i].spec_mappings()[v]
                },
        )
    }

    pub(crate) open spec fn mapping_within_region_prefix(
        vbase: SpecVAddr,
        frame: SpecFrame,
        region: MemoryRegion,
        pages: nat,
    ) -> bool {
        &&& region.vstart@.0 <= vbase.0
        &&& vbase.0 + frame.size.as_nat() <= region.vstart@.0 + pages * SPEC_PAGE_SIZE
        &&& region.pstart@.0 <= frame.base.0
        &&& frame.base.0 + frame.size.as_nat() <= region.pstart@.0 + pages * SPEC_PAGE_SIZE
        &&& frame.attr == region.attr
    }

    pub open spec fn mappings_cover_region_page(
        mappings: Map<SpecVAddr, SpecFrame>,
        region: MemoryRegion,
        page: nat,
    ) -> bool {
        exists|vbase: SpecVAddr, frame: SpecFrame| #[trigger]
            mappings.contains_pair(vbase, frame) && region.spec_page_vaddr(page).within(
                vbase,
                frame.size.as_nat(),
            ) && region.spec_page_paddr(page).within(frame.base, frame.size.as_nat()) && frame.attr
                == region.attr
    }

    pub(crate) open spec fn block_s2_entries(vbase: SpecVAddr, frame: SpecFrame) -> Map<
        GuestPage,
        S2Entry,
    > {
        let gbase = gpa_of_vaddr(vbase);
        Map::new(
            |g: GuestPage| gbase.0 <= g.0 < gbase.0 + frame.size.as_nat() / SPEC_PAGE_SIZE,
            |g: GuestPage|
                {
                    let page_offset = (g.0 - gbase.0) as nat;
                    S2Entry {
                        page: PhysPage(frame.base.0 / SPEC_PAGE_SIZE + page_offset),
                        access: attr_to_perms(frame.attr),
                        generation: 0,
                    }
                },
        )
    }

    pub(crate) open spec fn region_s2_prefix(region: MemoryRegion, end: nat) -> Map<
        GuestPage,
        S2Entry,
    > {
        let gbase = gpa_of_vaddr(region.vstart@);
        Map::new(
            |g: GuestPage| gbase.0 <= g.0 < gbase.0 + end,
            |g: GuestPage|
                {
                    let page_offset = (g.0 - gbase.0) as nat;
                    S2Entry {
                        page: PhysPage(region.pstart@.0 / SPEC_PAGE_SIZE + page_offset),
                        access: attr_to_perms(region.attr),
                        generation: 0,
                    }
                },
        )
    }

    /// A region's dense page mappings equal its complete modeled S2 prefix.
    proof fn lemma_pt_s2map_inner_region(region: MemoryRegion)
        requires
            region.spec_valid(),
        ensures
            pt_s2map_inner(region.spec_mappings()) == Self::region_s2_prefix(
                region,
                region.pages as nat,
            ),
    {
        let lhs = pt_s2map_inner(region.spec_mappings());
        let rhs = Self::region_s2_prefix(region, region.pages as nat);
        lemma_vaddr_gpa_roundtrip(region.vstart@);
        // Prove that both maps contain exactly the region's guest pages.
        assert forall|g: GuestPage| #[trigger] lhs.contains_key(g) <==> rhs.contains_key(g) by {
            if lhs.contains_key(g) {
                region.lemma_mappings_sound(vaddr_of_gpa(g));
                let page = choose|page: nat|
                    page < region.pages && vaddr_of_gpa(g) == region.spec_page_vaddr(page)
                        && region.spec_mappings()[vaddr_of_gpa(g)] == region.spec_frame(page);
                assert(g.0 == gpa_of_vaddr(region.vstart@).0 + page) by (nonlinear_arith)
                    requires
                        g.0 * SPEC_PAGE_SIZE == gpa_of_vaddr(region.vstart@).0 * SPEC_PAGE_SIZE
                            + page * SPEC_PAGE_SIZE,
                        SPEC_PAGE_SIZE == 0x1000nat,
                ;
            } else if rhs.contains_key(g) {
                let page = (g.0 - gpa_of_vaddr(region.vstart@).0) as nat;
                assert(page < region.pages);
                assert(vaddr_of_gpa(g) == region.spec_page_vaddr(page));
                region.lemma_mappings_contains_pair(page);
            }
        }
        // Prove that corresponding guest pages contain equal S2 entries.
        assert forall|g: GuestPage| #[trigger] lhs.contains_key(g) implies lhs[g] == rhs[g] by {
            region.lemma_mappings_sound(vaddr_of_gpa(g));
            let page = choose|page: nat|
                page < region.pages && vaddr_of_gpa(g) == region.spec_page_vaddr(page)
                    && region.spec_mappings()[vaddr_of_gpa(g)] == region.spec_frame(page);
            assert(g.0 == gpa_of_vaddr(region.vstart@).0 + page) by (nonlinear_arith)
                requires
                    g.0 * SPEC_PAGE_SIZE == gpa_of_vaddr(region.vstart@).0 * SPEC_PAGE_SIZE + page
                        * SPEC_PAGE_SIZE,
                    SPEC_PAGE_SIZE == 0x1000nat,
            ;
            assert(region.pstart@.0 / SPEC_PAGE_SIZE + page == region.spec_page_paddr(page).0
                / SPEC_PAGE_SIZE);
        }
        assert(lhs =~= rhs);
    }

    /// Pairwise virtual disjointness makes the region vector duplicate-free.
    proof fn lemma_regions_no_duplicates(self)
        requires
            self.invariants(),
        ensures
            self.regions@.no_duplicates(),
    {
        // Equal entries describe the same nonempty virtual range, contradicting disjointness.
        assert forall|i: int, j: int|
            #![auto]
            0 <= i < self.regions.len() && 0 <= j < self.regions.len() && i
                != j implies self.regions[i] != self.regions[j] by {
            if self.regions[i] == self.regions[j] {
                assert(self.regions[i].spec_valid());
                assert(self.regions[j].spec_valid());
                assert(self.regions[i].spec_overlaps_vmem(self.regions[j]));
            }
        }
    }

    /// Pick a supported frame size for the next part of `region`.
    /// The executable code scans levels greedily.
    fn select_frame_size(&self, vaddr: VAddr, paddr: PAddr, remaining_pages: usize) -> (res:
        FrameSize)
        requires
            self.pt.invariants(),
            self.pt@.constants.valid(),
            self.pt@.constants.arch.leaf_frame_size() == FrameSize::Size4K,
            0 < remaining_pages <= usize::MAX / PAGE_SIZE,
            vaddr@.aligned(SPEC_PAGE_SIZE),
            paddr@.aligned(SPEC_PAGE_SIZE),
        ensures
            self.pt@.constants.arch.is_valid_frame_size(res),
            vaddr@.aligned(res.as_nat()),
            paddr@.aligned(res.as_nat()),
            res.as_nat() <= remaining_pages * SPEC_PAGE_SIZE,
            res != FrameSize::Size4K ==> self.pt@.constants.huge_pages,
    {
        let c = self.pt.constants();
        let level_count = c.arch.level_count();
        let leaf_level = level_count - 1;
        let mut level: usize = 0;
        while level < leaf_level
            invariant
                0 <= level <= leaf_level,
                self.pt.invariants(),
                0 < remaining_pages <= usize::MAX / PAGE_SIZE,
                self.pt@.constants == c@,
                self.pt@.constants.valid(),
                self.pt@.constants.arch.leaf_frame_size() == FrameSize::Size4K,
                level_count == self.pt@.constants.arch.level_count(),
                leaf_level + 1 == level_count,
            decreases leaf_level - level,
        {
            let size = c.arch.frame_size(level);
            if c.huge_pages && level + 1 < level_count && size.as_usize() <= remaining_pages
                * PAGE_SIZE && vaddr.0 % size.as_usize() == 0 && paddr.0 % size.as_usize() == 0 {
                return size;
            }
            level += 1;
        }
        FrameSize::Size4K
    }

    /// An empty region vector cannot have concrete page-table mappings.
    proof fn lemma_pt_empty_if_regions_empty(self)
        requires
            self.invariants(),
            self@.regions == Set::<MemoryRegion>::empty(),
        ensures
            self.pt@.mappings == Map::<SpecVAddr, SpecFrame>::empty(),
    {
        // Mapping soundness gives an owner, contradicting the empty region view.
        assert forall|v: SpecVAddr, f: SpecFrame|
            self.pt@.mappings.contains_pair(v, f) implies false by {
            assert(self.has_region_for_mapping(v, f));
            let idx = choose|idx: int|
                #![auto]
                0 <= idx < self.regions.len() && self.regions[idx].vstart@.0 <= v.0 && v.0
                    + f.size.as_nat() <= self.regions[idx].vstart@.0 + self.regions[idx].pages
                    * SPEC_PAGE_SIZE && self.regions[idx].pstart@.0 <= f.base.0 && f.base.0
                    + f.size.as_nat() <= self.regions[idx].pstart@.0 + self.regions[idx].pages
                    * SPEC_PAGE_SIZE && f.attr == self.regions[idx].attr;
            assert(self@.regions.contains(self.regions[idx]));
        }
        lemma_map_eq_pair(Map::<SpecVAddr, SpecFrame>::empty(), self.pt@.mappings);
    }
}

impl<PT, A, I> MemorySet<PT, A, I> for VecMemorySet<PT, A, I> where
    PT: PageTable<A>,
    A: BitmapAllocator,
    I: HardwareInstr,
 {
    open spec fn view(&self) -> SpecMemorySet {
        SpecMemorySet { regions: self.regions@.to_set(), mappings: self.mappings_view() }
    }

    open spec fn inst_id(&self) -> InstanceId {
        self.pt.inst_id()
    }

    open spec fn pt_constants(&self) -> SpecPTConstants {
        self.pt@.constants
    }

    open spec fn spec_pt_root(&self) -> SpecPAddr {
        self.pt.spec_root()
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
        // Region page bases are inside the backing page-table virtual space.
        &&& forall|i: int|
            0 <= i < self.regions.len() ==> #[trigger] self.regions[i].spec_within_vspace(
                self.pt@.constants.arch.vspace_size(),
            )
        // Regions do not overlap in vmem.
        &&& forall|i: int, j: int|
            0 <= i < self.regions.len() && 0 <= j < self.regions.len() && i != j
                ==> !self.regions[i].spec_overlaps_vmem(
                self.regions[j],
            )
            // Exact-dense consistency (completeness): every region page is covered by a mapping.
        &&& forall|r: MemoryRegion| #[trigger]
            self.regions@.contains(r) ==> self.has_mapping_for_region(
                r,
            )
        // Exact-dense consistency (soundness): every mapping is exactly within some region.
        &&& forall|v: SpecVAddr, f: SpecFrame| #[trigger]
            self.pt@.mappings.contains_pair(v, f) ==> self.has_region_for_mapping(v, f)
    }

    fn new(allocator: &GlobalAllocator<A>, pt_constants: PTConstants) -> (res: Self) {
        let pt = PT::new(allocator, pt_constants);
        VecMemorySet { regions: Vec::new(), pt, phantom: PhantomData }
    }

    fn drop(self, allocator: &GlobalAllocator<A>) {
        let ghost old_self = self;
        proof {
            // Prove `pt.drop`'s empty-mapping precondition from the abstract empty view.
            old_self.lemma_pt_empty_if_regions_empty();
        }
        let VecMemorySet { regions: _, pt, phantom: _ } = self;
        pt.drop(allocator);
    }

    fn is_empty(&self) -> (res: bool) {
        if self.regions.len() == 0 {
            assert(self@.regions =~= Set::<MemoryRegion>::empty());
            assert(self@.mappings =~= Map::<SpecVAddr, SpecFrame>::empty());
            true
        } else {
            assert(self@.regions.contains(self.regions[0]));
            false
        }
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

    fn pt_root(&self) -> (res: PAddr) {
        self.pt.root()
    }

    fn query_vaddr(&self, vaddr: VAddr) -> (res: Result<(PAddr, MemAttr), ()>) {
        let mut i: usize = 0;
        while i < self.regions.len()
            invariant
                self.invariants(),
                0 <= i <= self.regions.len(),
                forall|j: int| #![auto] 0 <= j < i ==> !self.regions[j].spec_contains_vaddr(vaddr@),
            decreases self.regions.len() - i,
        {
            let region = &self.regions[i];
            let vend = region.vend();
            if region.vstart.0 <= vaddr.0 && vaddr.0 < vend.0 {
                let paddr = region.translate(vaddr);
                proof {
                    // Prove the successful result is witnessed by this region in `self@`.
                    assert(self@.regions.contains(*region));
                    assert(region.spec_contains_vaddr(vaddr@));
                    assert(exists|r: MemoryRegion|
                        self@.regions.contains(r) && #[trigger] r.spec_contains_vaddr(vaddr@)
                            && paddr@ == r.spec_translate(vaddr@) && region.attr == r.attr);
                }
                return Ok((paddr, region.attr));
            }
            i += 1;
        }
        proof {
            // Prove the error result: no region in the abstract view contains `vaddr`.
            assert forall|region: MemoryRegion| #[trigger]
                self@.regions.contains(region) implies !region.spec_contains_vaddr(vaddr@) by {
                let j = choose|j: int| 0 <= j < self.regions.len() && self.regions[j] == region;
            }
        }
        Err(())
    }

    fn insert(
        &mut self,
        allocator: &GlobalAllocator<A>,
        region: MemoryRegion,
        zone_id: usize,
        mmu: &MmuHardware<I>,
        s2_tok: Tracked<MmuVmToken>,
        iommu: bool,
    ) -> (res: Tracked<MmuVmToken>) {
        let mut s2 = s2_tok;
        let mut i: usize = 0;
        proof {
            // Supply mapping-owner witnesses used by the disjoint-suffix proof below.
            old(self).lemma_invariants_implies_wf();
            // Prove the loop's S2-prefix equation for the initial prefix `i == 0`.
            assert(s2@.value().s2map == pt_s2map_inner(old(self)@.mappings).union_prefer_right(
                Self::region_s2_prefix(region, 0),
            ));
            lemma_vaddr_gpa_roundtrip(region.vstart@);
            // Prove the loop's untouched-suffix predicate for the entire new region.
            assert forall|g: GuestPage| #[trigger] s2@.value().s2map.contains_key(g) implies !(
            gpa_of_vaddr(region.vstart@).0 <= g.0 < gpa_of_vaddr(region.vstart@).0
                + region.pages) by {
                if gpa_of_vaddr(region.vstart@).0 <= g.0 < gpa_of_vaddr(region.vstart@).0
                    + region.pages {
                    assert(pt_s2map_inner(old(self)@.mappings).contains_key(g));
                    assert(old(self)@.mappings.contains_key(vaddr_of_gpa(g)));
                    let frame = old(self)@.mappings[vaddr_of_gpa(g)];
                    assert(old(self)@.mappings.contains_pair(vaddr_of_gpa(g), frame));
                    let (r, page) = choose|r: MemoryRegion, page: nat|
                        #![trigger old(self)@.regions.contains(r), r.spec_page_vaddr(page)]
                        old(self)@.regions.contains(r) && page < r.pages && vaddr_of_gpa(g)
                            == r.spec_page_vaddr(page) && frame == r.spec_frame(page);
                    assert(r.spec_valid());
                    let new_page = (g.0 - gpa_of_vaddr(region.vstart@).0) as nat;
                    assert(new_page < region.pages);
                    assert(vaddr_of_gpa(g) == region.spec_page_vaddr(new_page));
                    assert(!r.spec_overlaps_vmem(region));
                    MemoryRegion::lemma_pages_disjoint(r, region, page, new_page);
                }
            }
        }
        while i < region.pages
            invariant
                0 <= i <= region.pages,
                region.spec_valid(),
                region.spec_within_vspace(self.pt@.constants.arch.vspace_size()),
                i == 0 ==> self.invariants(),
                self.pt.invariants(),
                allocator.invariants(),
                self.pt.inst_id() == allocator.inst_id(),
                self.pt@.constants == old(self).pt@.constants,
                self.pt@.constants.valid(),
                self.pt@.constants.arch.leaf_frame_size() == FrameSize::Size4K,
                old(self).invariants(),
                !old(self)@.overlaps_vmem(region),
                self.regions == old(self).regions,
                forall|vb: SpecVAddr, fr: SpecFrame| #[trigger]
                    old(self).pt@.mappings.contains_pair(vb, fr)
                        ==> self.pt@.mappings.contains_pair(vb, fr),
                forall|vb: SpecVAddr, fr: SpecFrame| #[trigger]
                    self.pt@.mappings.contains_pair(vb, fr) ==> old(
                        self,
                    ).pt@.mappings.contains_pair(vb, fr) || Self::mapping_within_region_prefix(
                        vb,
                        fr,
                        region,
                        i as nat,
                    ),
                forall|page: nat|
                    page < i ==> #[trigger] Self::mappings_cover_region_page(
                        self.pt@.mappings,
                        region,
                        page,
                    ),
                mmu.wf(),
                I::valid_zone_id(zone_id),
                s2@.instance_id() == mmu.inst_id(),
                s2@.key() == VmId(zone_id as nat),
                s2@.value().coherent(VmId(zone_id as nat)),
                s2@.value().s2map == pt_s2map_inner(old(self)@.mappings).union_prefer_right(
                    Self::region_s2_prefix(region, i as nat),
                ),
                forall|g: GuestPage| #[trigger]
                    s2@.value().s2map.contains_key(g) ==> !(gpa_of_vaddr(region.vstart@).0 + i
                        <= g.0 < gpa_of_vaddr(region.vstart@).0 + region.pages),
            decreases region.pages - i,
        {
            let vbase = VAddr(region.vstart.0 + i * PAGE_SIZE);
            let paddr = PAddr(region.pstart.0 + i * PAGE_SIZE);
            proof {
                // Prove `select_frame_size`'s validity, size, alignment, and vspace preconditions.
                assert(self.pt@.constants.valid());
                assert(self.pt@.constants.arch.leaf_frame_size() == FrameSize::Size4K);
                assert(region.pages - i <= usize::MAX / PAGE_SIZE);
                assert(vbase@.aligned(SPEC_PAGE_SIZE));
                assert(paddr@.aligned(SPEC_PAGE_SIZE));
                assert(vbase@ == region.spec_page_vaddr(i as nat));
                assert(vbase@.0 < self.pt@.constants.arch.vspace_size());
            }
            let size = self.select_frame_size(vbase, paddr, region.pages - i);
            let chunk_pages = size.as_usize() / PAGE_SIZE;
            let frame = Frame { base: paddr, size, attr: region.attr.clone() };
            proof {
                // Prove the frame-validity, alignment, and physical-bound clauses of `map_pre`.
                assert(self.pt@.constants.arch.is_valid_frame_size(size));
                assert(vbase@.aligned(size.as_nat()));
                assert(frame.base@.aligned(size.as_nat()));
                assert(frame.base@.0 + size.as_nat() <= PADDR_UPPER_BOUND);
                // Prove the non-overlap clause of `self.pt@.map_pre`.
                assert(!self.pt@.overlaps_vmem(vbase@, frame@)) by {
                    assert forall|vb: SpecVAddr| #[trigger]
                        self.pt@.mappings.contains_key(vb) implies !SpecVAddr::overlap(
                        vb,
                        self.pt@.mappings[vb].size.as_nat(),
                        vbase@,
                        frame.size.as_nat(),
                    ) by {
                        let fr = self.pt@.mappings[vb];
                        assert(self.pt@.mappings.contains_pair(vb, fr));
                        if old(self).pt@.mappings.contains_pair(vb, fr) {
                            assert(old(self).has_region_for_mapping(vb, fr));
                            let owner = choose|owner: int|
                                #![auto]
                                0 <= owner < old(self).regions.len() && old(
                                    self,
                                ).regions[owner].vstart@.0 <= vb.0 && vb.0 + fr.size.as_nat()
                                    <= old(self).regions[owner].vstart@.0 + old(
                                    self,
                                ).regions[owner].pages * SPEC_PAGE_SIZE && old(
                                    self,
                                ).regions[owner].pstart@.0 <= fr.base.0 && fr.base.0
                                    + fr.size.as_nat() <= old(self).regions[owner].pstart@.0 + old(
                                    self,
                                ).regions[owner].pages * SPEC_PAGE_SIZE && fr.attr == old(
                                    self,
                                ).regions[owner].attr;
                            assert(old(self)@.regions.contains(old(self).regions[owner]));
                            assert(!old(self).regions[owner].spec_overlaps_vmem(region));
                            assert(fr.size.as_nat() > 0);
                            assert(frame.size.as_nat() > 0);
                        } else {
                            assert(Self::mapping_within_region_prefix(vb, fr, region, i as nat));
                            assert(vb.0 + fr.size.as_nat() <= vbase@.0);
                        }
                    }
                }
                assert(self.pt@.map_pre(vbase@, frame@));
                // Prove the MMU range is nonempty, bounded, and disjoint from the current S2 map.
                assert(chunk_pages > 0);
                assert(i + chunk_pages <= region.pages);
                lemma_vaddr_gpa_roundtrip(region.vstart@);
                lemma_vaddr_gpa_roundtrip(vbase@);
                assert(gpa_of_vaddr(vbase@).0 == gpa_of_vaddr(region.vstart@).0 + i);
                assert(s2@.value().s2map.dom().disjoint(
                    Self::block_s2_entries(vbase@, frame@).dom(),
                )) by {
                    assert forall|g: GuestPage| #[trigger]
                        s2@.value().s2map.dom().contains(g) implies !Self::block_s2_entries(
                        vbase@,
                        frame@,
                    ).dom().contains(g) by {
                        if Self::block_s2_entries(vbase@, frame@).dom().contains(g) {
                            assert(gpa_of_vaddr(vbase@).0 <= g.0);
                            assert(g.0 < gpa_of_vaddr(vbase@).0 + frame.size.as_nat()
                                / SPEC_PAGE_SIZE);
                            assert(frame.size.as_nat() / SPEC_PAGE_SIZE == chunk_pages);
                            assert(g.0 < gpa_of_vaddr(region.vstart@).0 + region.pages);
                        }
                    }
                }
                // Prove the ghost block domain matches the MMU API's guest-page range.
                assert(Self::block_s2_entries(vbase@, frame@).dom()
                    =~= crate::hardware::spec::guest_page_range(
                    GuestPage((vbase.0 / PAGE_SIZE) as nat),
                    chunk_pages as nat,
                ));
            }
            let ghost prefix_pages = i as nat;
            let ghost mappings_before = self.pt@.mappings;
            let map_res = self.pt.map(allocator, vbase, frame);

            let ipa_page = vbase.0 / PAGE_SIZE;
            let ghost old_s2map = s2@.value().s2map;
            // Synchronize the MMU's S2 map with the newly inserted mapping.
            s2 =
            if iommu {
                mmu.iommu_map_range_sync(
                    s2,
                    ipa_page,
                    chunk_pages,
                    zone_id,
                    Ghost(Self::block_s2_entries(vbase@, frame@)),
                )
            } else {
                mmu.map_range_dsb(
                    s2,
                    ipa_page,
                    chunk_pages,
                    zone_id,
                    Ghost(Self::block_s2_entries(vbase@, frame@)),
                )
            };
            i += chunk_pages;
            proof {
                // Identify the inserted block and prove that it belongs to the extended prefix.
                assert(frame.size.as_nat() == chunk_pages as nat * SPEC_PAGE_SIZE);
                assert(frame.base@ == region.spec_page_paddr(prefix_pages));
                assert(self.pt@.mappings == mappings_before.insert(vbase@, frame@));
                assert(Self::mapping_within_region_prefix(vbase@, frame@, region, i as nat));
                // Prove that every original mapping remains present after insertion.
                assert forall|vb: SpecVAddr, fr: SpecFrame| #[trigger]
                    old(self).pt@.mappings.contains_pair(
                        vb,
                        fr,
                    ) implies self.pt@.mappings.contains_pair(vb, fr) by {
                    assert(mappings_before.contains_pair(vb, fr));
                }
                // Prove that every current mapping is original or belongs to the new prefix.
                assert forall|vb: SpecVAddr, fr: SpecFrame| #[trigger]
                    self.pt@.mappings.contains_pair(vb, fr) implies old(
                    self,
                ).pt@.mappings.contains_pair(vb, fr) || Self::mapping_within_region_prefix(
                    vb,
                    fr,
                    region,
                    i as nat,
                ) by {
                    if vb == vbase@ {
                        assert(fr == frame@);
                    } else {
                        assert(mappings_before.contains_pair(vb, fr));
                        if Self::mapping_within_region_prefix(vb, fr, region, prefix_pages) {
                            assert(Self::mapping_within_region_prefix(vb, fr, region, i as nat));
                        }
                    }
                }
                // Prove mapping completeness for every page in the extended prefix.
                assert forall|page: nat|
                    page < i implies #[trigger] Self::mappings_cover_region_page(
                    self.pt@.mappings,
                    region,
                    page,
                ) by {
                    if page < prefix_pages {
                        assert(Self::mappings_cover_region_page(mappings_before, region, page));
                        let (vb, fr) = choose|vb: SpecVAddr, fr: SpecFrame| #[trigger]
                            mappings_before.contains_pair(vb, fr) && region.spec_page_vaddr(
                                page,
                            ).within(vb, fr.size.as_nat()) && region.spec_page_paddr(page).within(
                                fr.base,
                                fr.size.as_nat(),
                            ) && fr.attr == region.attr;
                        assert(self.pt@.mappings.contains_pair(vb, fr));
                    } else {
                        assert(region.spec_page_vaddr(page).within(vbase@, frame.size.as_nat()));
                        assert(region.spec_page_paddr(page).within(
                            frame.base@,
                            frame.size.as_nat(),
                        ));
                        assert(self.pt@.mappings.contains_pair(vbase@, frame@));
                    }
                }
                // Prove the S2-prefix equality invariant after extending the token map.
                assert(s2@.value().s2map == pt_s2map_inner(old(self)@.mappings).union_prefer_right(
                    Self::region_s2_prefix(region, i as nat),
                )) by {
                    assert(old_s2map == pt_s2map_inner(old(self)@.mappings).union_prefer_right(
                        Self::region_s2_prefix(region, prefix_pages),
                    ));
                    assert(s2@.value().s2map =~= pt_s2map_inner(
                        old(self)@.mappings,
                    ).union_prefer_right(Self::region_s2_prefix(region, i as nat)));
                }
                // Prove that the token has no entry in the still-unmapped suffix.
                assert forall|g: GuestPage| #[trigger] s2@.value().s2map.contains_key(g) implies !(
                gpa_of_vaddr(region.vstart@).0 + i <= g.0 < gpa_of_vaddr(region.vstart@).0
                    + region.pages) by {
                    if gpa_of_vaddr(region.vstart@).0 + i <= g.0 < gpa_of_vaddr(region.vstart@).0
                        + region.pages {
                        if old_s2map.contains_key(g) {
                            assert(gpa_of_vaddr(region.vstart@).0 + (i - chunk_pages) <= g.0);
                        } else {
                            assert(Self::block_s2_entries(vbase@, frame@).contains_key(g));
                            assert(g.0 < gpa_of_vaddr(vbase@).0 + frame.size.as_nat()
                                / SPEC_PAGE_SIZE);
                            assert(gpa_of_vaddr(vbase@).0 == gpa_of_vaddr(region.vstart@).0 + (i
                                - chunk_pages));
                            assert(frame.size.as_nat() / SPEC_PAGE_SIZE == chunk_pages);
                        }
                    }
                }
                // Re-establish the token-coherence and page-table invariant clauses.
                assert(s2@.value().coherent(VmId(zone_id as nat)));
                assert(self.pt.invariants());
            }
        }

        let ghost self_before_push = *self;
        self.regions.push(region);
        proof {
            // Prove the loop completed and that `push` did not change the page table.
            assert(i == region.pages);
            assert(self.pt@ == self_before_push.pt@);

            // Prove the region-validity clause of `self.invariants()` after `push`.
            assert forall|idx: int|
                0 <= idx < self.regions.len() implies #[trigger] self.regions[idx].spec_valid() by {
                if idx < old(self).regions.len() {
                    assert(self.regions[idx] == old(self).regions[idx]);
                } else {
                    assert(idx == old(self).regions.len());
                    assert(self.regions[idx] == region);
                }
            }
            // Prove the region-vspace clause of `self.invariants()` after `push`.
            assert forall|idx: int|
                0 <= idx
                    < self.regions.len() implies #[trigger] self.regions[idx].spec_within_vspace(
                self.pt@.constants.arch.vspace_size(),
            ) by {
                if idx < old(self).regions.len() {
                    assert(self.regions[idx] == old(self).regions[idx]);
                } else {
                    assert(idx == old(self).regions.len());
                    assert(self.regions[idx] == region);
                }
            }
            // Prove the pairwise region non-overlap clause of `self.invariants()`.
            assert forall|idx: int, jdx: int|
                0 <= idx < self.regions.len() && 0 <= jdx < self.regions.len() && idx
                    != jdx implies !self.regions[idx].spec_overlaps_vmem(self.regions[jdx]) by {
                if idx < old(self).regions.len() && jdx < old(self).regions.len() {
                    assert(self.regions[idx] == old(self).regions[idx]);
                    assert(self.regions[jdx] == old(self).regions[jdx]);
                } else if idx == old(self).regions.len() {
                    assert(self.regions[idx] == region);
                    assert(self.regions[jdx] == old(self).regions[jdx]);
                    assert(!old(self).regions[jdx].spec_overlaps_vmem(region));
                    old(self).regions[jdx].lemma_overlaps_vmem_symmetric(region);
                } else {
                    assert(jdx == old(self).regions.len());
                    assert(self.regions[jdx] == region);
                    assert(self.regions[idx] == old(self).regions[idx]);
                    assert(!old(self).regions[idx].spec_overlaps_vmem(region));
                }
            }

            // Prove mapping completeness: every retained or inserted region is fully covered.
            assert forall|r: MemoryRegion| #[trigger]
                self.regions@.contains(r) implies self.has_mapping_for_region(r) by {
                let idx = choose|idx: int| 0 <= idx < self.regions.len() && self.regions[idx] == r;
                if idx == old(self).regions.len() {
                    assert(r == region);
                    assert forall|page: nat|
                        page < region.pages implies #[trigger] Self::mappings_cover_region_page(
                        self.pt@.mappings,
                        region,
                        page,
                    ) by {
                        assert(Self::mappings_cover_region_page(
                            self_before_push.pt@.mappings,
                            region,
                            page,
                        ));
                    }
                    assert(self.has_mapping_for_region(r));
                } else {
                    assert(idx < old(self).regions.len());
                    let old_region = old(self).regions[idx];
                    assert(r == old_region);
                    assert(old(self).regions@.contains(old_region));
                    assert(old(self).has_mapping_for_region(old_region));
                    assert forall|page: nat|
                        page < old_region.pages implies #[trigger] Self::mappings_cover_region_page(
                        self.pt@.mappings,
                        old_region,
                        page,
                    ) by {
                        assert(Self::mappings_cover_region_page(
                            old(self).pt@.mappings,
                            old_region,
                            page,
                        ));
                        let (vb, fr) = choose|vb: SpecVAddr, fr: SpecFrame| #[trigger]
                            old(self).pt@.mappings.contains_pair(vb, fr)
                                && old_region.spec_page_vaddr(page).within(vb, fr.size.as_nat())
                                && old_region.spec_page_paddr(page).within(
                                fr.base,
                                fr.size.as_nat(),
                            ) && fr.attr == old_region.attr;
                        assert(self_before_push.pt@.mappings.contains_pair(vb, fr));
                        assert(self.pt@.mappings.contains_pair(vb, fr));
                    }
                    assert(self.has_mapping_for_region(r));
                }
            }

            // Prove mapping soundness: every page-table mapping has an owner in `regions`.
            assert forall|vb: SpecVAddr, fr: SpecFrame| #[trigger]
                self.pt@.mappings.contains_pair(vb, fr) implies self.has_region_for_mapping(
                vb,
                fr,
            ) by {
                assert(self_before_push.pt@.mappings.contains_pair(vb, fr));
                if old(self).pt@.mappings.contains_pair(vb, fr) {
                    assert(old(self).has_region_for_mapping(vb, fr));
                    let owner = choose|owner: int|
                        #![auto]
                        0 <= owner < old(self).regions.len() && old(self).regions[owner].vstart@.0
                            <= vb.0 && vb.0 + fr.size.as_nat() <= old(self).regions[owner].vstart@.0
                            + old(self).regions[owner].pages * SPEC_PAGE_SIZE && old(
                            self,
                        ).regions[owner].pstart@.0 <= fr.base.0 && fr.base.0 + fr.size.as_nat()
                            <= old(self).regions[owner].pstart@.0 + old(self).regions[owner].pages
                            * SPEC_PAGE_SIZE && fr.attr == old(self).regions[owner].attr;
                    assert(self.regions[owner] == old(self).regions[owner]);
                } else {
                    assert(Self::mapping_within_region_prefix(vb, fr, region, region.pages as nat));
                    assert(self.regions[old(self).regions.len() as int] == region);
                }
            }
            assert(self.invariants());

            // Prove the region-set component of `self@ == old(self)@.insert_region(region)`.
            assert(self@.regions == old(self)@.regions.insert(region)) by {
                assert forall|r: MemoryRegion| #[trigger]
                    self@.regions.contains(r) <==> old(self)@.regions.insert(region).contains(
                        r,
                    ) by {
                    if self@.regions.contains(r) {
                        let idx = choose|idx: int|
                            0 <= idx < self.regions.len() && self.regions[idx] == r;
                        if idx < old(self).regions.len() {
                            assert(old(self).regions[idx] == r);
                        } else {
                            assert(r == region);
                        }
                    }
                    if old(self)@.regions.insert(region).contains(r) {
                        if old(self)@.regions.contains(r) {
                            let idx = choose|idx: int|
                                0 <= idx < old(self).regions.len() && old(self).regions[idx] == r;
                            assert(self.regions[idx] == r);
                        } else {
                            assert(r == region);
                            assert(self.regions[old(self).regions.len() as int] == region);
                        }
                    }
                }
            }
            assert(!old(self)@.regions.contains(region)) by {
                if old(self)@.regions.contains(region) {
                    assert(region.spec_overlaps_vmem(region));
                    assert(old(self)@.overlaps_vmem(region));
                }
            }
            old(self)@.lemma_insert_region_wf(region);
            self.lemma_invariants_implies_wf();
            let expected = old(self)@.insert_region(region);
            // Prove the mapping component by completeness and soundness in both views.
            assert(self@.mappings == expected.mappings) by {
                assert forall|v: SpecVAddr, f: SpecFrame| #[trigger]
                    self@.mappings.contains_pair(v, f) implies expected.mappings.contains_pair(
                    v,
                    f,
                ) by {
                    let (r, page) = choose|r: MemoryRegion, page: nat|
                        #![trigger self@.regions.contains(r), r.spec_page_vaddr(page)]
                        self@.regions.contains(r) && page < r.pages && v == r.spec_page_vaddr(page)
                            && f == r.spec_frame(page);
                    assert(expected.regions.contains(r));
                }
                assert forall|v: SpecVAddr, f: SpecFrame| #[trigger]
                    expected.mappings.contains_pair(v, f) implies self@.mappings.contains_pair(
                    v,
                    f,
                ) by {
                    let (r, page) = choose|r: MemoryRegion, page: nat|
                        #![trigger expected.regions.contains(r), r.spec_page_vaddr(page)]
                        expected.regions.contains(r) && page < r.pages && v == r.spec_page_vaddr(
                            page,
                        ) && f == r.spec_frame(page);
                    assert(self@.regions.contains(r));
                }
                lemma_map_eq_pair(self@.mappings, expected.mappings);
            }
            assert(self@ == expected);
            // Translate the inserted region to discharge the final S2-map postcondition.
            Self::lemma_pt_s2map_inner_region(region);
            assert(s2@.value().s2map == pt_s2map_inner(self@.mappings));
            assert(s2@.value().coherent(VmId(zone_id as nat)));
        }
        s2
    }

    fn remove(
        &mut self,
        allocator: &GlobalAllocator<A>,
        start: VAddr,
        zone_id: usize,
        mmu: &MmuHardware<I>,
        s2_tok: Tracked<MmuVmToken>,
        iommu: bool,
    ) -> (res: Tracked<MmuVmToken>) {
        let mut s2 = s2_tok;
        let mut ridx: usize = 0;
        while ridx < self.regions.len()
            invariant
                0 <= ridx <= self.regions.len(),
                self.regions.len() == old(self).regions.len(),
                *self == *old(self),
                self.pt.invariants(),
                forall|j: int| #![auto] 0 <= j < ridx ==> self.regions[j].vstart@ != start@,
            ensures
                ridx < self.regions.len() ==> self.regions[ridx as int].vstart@ == start@,
            decreases self.regions.len() - ridx,
        {
            if self.regions[ridx].vstart.0 == start.0 {
                break;
            }
            ridx += 1;
        }
        // `has_region_starting_at` ensures that the region exists.
        proof {
            // Instantiate existence to identify `ridx` with the requested region.
            assert(self@.has_region_starting_at(start@));
            assert(ridx < self.regions.len());
        }

        let region = &self.regions[ridx];
        proof {
            // Prove full coverage of the target and all non-target regions at `i == 0`.
            assert(self.regions@.contains(*region));
            assert(self.has_mapping_for_region(*region));
            assert forall|j: int|
                0 <= j < self.regions.len() && j
                    != ridx as int implies #[trigger] self.has_mapping_for_region(
                self.regions[j],
            ) by {
                assert(self.regions@.contains(self.regions[j]));
            }
            // Prove the removal loop's S2 equation for the empty removed prefix.
            assert(s2@.value().s2map == pt_s2map_inner(old(self)@.mappings).remove_keys(
                Self::region_s2_prefix(*region, 0).dom(),
            ));
        }
        let mut i: usize = 0;
        while i < region.pages
            invariant
                0 <= i <= region.pages,
                ridx < self.regions.len(),
                *region == old(self).regions[ridx as int],
                region.spec_valid(),
                region.spec_within_vspace(self.pt@.constants.arch.vspace_size()),
                i == 0 ==> self.invariants(),
                self.pt.invariants(),
                allocator.invariants(),
                self.pt.inst_id() == allocator.inst_id(),
                self.pt@.constants == old(self).pt@.constants,
                self.pt@.constants.valid(),
                self.pt@.constants.arch.leaf_frame_size() == FrameSize::Size4K,
                old(self).invariants(),
                self.regions == old(self).regions,
                forall|vb: SpecVAddr, fr: SpecFrame| #[trigger]
                    self.pt@.mappings.contains_pair(vb, fr) ==> old(
                        self,
                    ).pt@.mappings.contains_pair(vb, fr),
                forall|page: nat|
                    i <= page < region.pages ==> #[trigger] Self::mappings_cover_region_page(
                        self.pt@.mappings,
                        *region,
                        page,
                    ),
                forall|j: int|
                    0 <= j < self.regions.len() && j != ridx as int
                        ==> #[trigger] self.has_mapping_for_region(self.regions[j]),
                forall|vb: SpecVAddr, fr: SpecFrame| #[trigger]
                    self.pt@.mappings.contains_pair(vb, fr) ==> self.has_region_for_mapping_except(
                        vb,
                        fr,
                        ridx as int,
                    ) || region.spec_page_vaddr(i as nat).0 <= vb.0,
                mmu.wf(),
                I::valid_zone_id(zone_id),
                s2@.instance_id() == mmu.inst_id(),
                s2@.key() == VmId(zone_id as nat),
                s2@.value().coherent(VmId(zone_id as nat)),
                s2@.value().s2map == pt_s2map_inner(old(self)@.mappings).remove_keys(
                    Self::region_s2_prefix(*region, i as nat).dom(),
                ),
            decreases region.pages - i,
        {
            let vbase = VAddr(region.vstart.0 + i * PAGE_SIZE);
            let ghost old_mappings = self.pt@.mappings;
            let ghost self_before_unmap = *self;
            proof {
                // Use coverage plus region disjointness to prove `vbase` is a mapped block base.
                assert(Self::mappings_cover_region_page(old_mappings, *region, i as nat));
                let (mapped_vbase, covering_frame) = choose|
                    mapped_vbase: SpecVAddr,
                    covering_frame: SpecFrame,
                | #[trigger]
                    old_mappings.contains_pair(mapped_vbase, covering_frame)
                        && region.spec_page_vaddr(i as nat).within(
                        mapped_vbase,
                        covering_frame.size.as_nat(),
                    ) && region.spec_page_paddr(i as nat).within(
                        covering_frame.base,
                        covering_frame.size.as_nat(),
                    ) && covering_frame.attr == region.attr;
                assert(region.spec_page_vaddr(i as nat).0 >= mapped_vbase.0);
                assert(vbase@ == region.spec_page_vaddr(i as nat));
                assert(mapped_vbase.0 <= vbase@.0);
                if self.has_region_for_mapping_except(mapped_vbase, covering_frame, ridx as int) {
                    let owner = choose|owner: int|
                        #![auto]
                        0 <= owner < self.regions.len() && owner != ridx as int
                            && self.regions[owner].vstart@.0 <= mapped_vbase.0 && mapped_vbase.0
                            + covering_frame.size.as_nat() <= self.regions[owner].vstart@.0
                            + self.regions[owner].pages * SPEC_PAGE_SIZE
                            && self.regions[owner].pstart@.0 <= covering_frame.base.0
                            && covering_frame.base.0 + covering_frame.size.as_nat()
                            <= self.regions[owner].pstart@.0 + self.regions[owner].pages
                            * SPEC_PAGE_SIZE && covering_frame.attr == self.regions[owner].attr;
                    assert(!self.regions[owner].spec_overlaps_vmem(*region));
                    assert(self.regions[owner].spec_overlaps_vmem(*region));
                }
                assert(vbase@.0 <= mapped_vbase.0);
                assert(mapped_vbase == vbase@);
                assert(old_mappings.contains_key(vbase@));
            }
            let mapped_frame = self.pt.unmap(allocator, vbase).unwrap();
            let chunk_pages = mapped_frame.size.as_usize() / PAGE_SIZE;
            proof {
                // Prove the unmapped frame belongs to the target region, not another owner.
                assert(old_mappings.contains_pair(vbase@, mapped_frame@));
                assert(old(self).pt@.mappings.contains_pair(vbase@, mapped_frame@));
                assert(old(self).has_region_for_mapping(vbase@, mapped_frame@));
                let owner = choose|owner: int|
                    #![auto]
                    0 <= owner < old(self).regions.len() && old(self).regions[owner].vstart@.0
                        <= vbase@.0 && vbase@.0 + mapped_frame.size.as_nat() <= old(
                        self,
                    ).regions[owner].vstart@.0 + old(self).regions[owner].pages * SPEC_PAGE_SIZE
                        && old(self).regions[owner].pstart@.0 <= mapped_frame.base@.0
                        && mapped_frame.base@.0 + mapped_frame.size.as_nat() <= old(
                        self,
                    ).regions[owner].pstart@.0 + old(self).regions[owner].pages * SPEC_PAGE_SIZE
                        && mapped_frame.attr == old(self).regions[owner].attr;
                assert(mapped_frame.size.as_nat() > 0);
                assert(owner == ridx as int) by {
                    if owner != ridx as int {
                        assert(!old(self).regions[owner].spec_overlaps_vmem(
                            old(self).regions[ridx as int],
                        ));
                        assert(old(self).regions[owner].spec_overlaps_vmem(
                            old(self).regions[ridx as int],
                        ));
                    }
                }
                // Prove the chunk-size, physical-bound, and loop-progress clauses.
                assert(vbase@.0 == region.vstart@.0 + i as nat * SPEC_PAGE_SIZE);
                assert(vbase@.0 + mapped_frame.size.as_nat() <= region.vstart@.0
                    + region.pages as nat * SPEC_PAGE_SIZE);
                assert((region.pages - i) as nat == region.pages as nat - i as nat);
                assert(mapped_frame.size.as_nat() <= (region.pages - i) as nat * SPEC_PAGE_SIZE);
                assert(old(self).regions[owner].spec_valid());
                assert(mapped_frame.base@.0 + mapped_frame.size.as_nat() <= PADDR_UPPER_BOUND);
                assert(chunk_pages > 0);
                assert(i + chunk_pages <= region.pages);
            }
            let ipa_page = vbase.0 / PAGE_SIZE;
            let ghost prefix_pages = i as nat;
            let ghost old_s2map = s2@.value().s2map;
            // Synchronize the MMU's S2 map with the newly removed mapping.
            s2 =
            if iommu {
                mmu.iommu_unmap_range_invalidate(s2, ipa_page, chunk_pages, zone_id)
            } else {
                mmu.unmap_range_dsb_tlbi(s2, ipa_page, chunk_pages, zone_id)
            };
            i += chunk_pages;
            proof {
                // Prove that this block extends the removed guest-page prefix exactly.
                assert(mapped_frame.size.as_nat() == chunk_pages as nat * SPEC_PAGE_SIZE);
                let removed = crate::hardware::spec::guest_page_range(
                    GuestPage(ipa_page as nat),
                    chunk_pages as nat,
                );
                assert(removed =~= Self::block_s2_entries(vbase@, mapped_frame@).dom());
                // Prove the token's S2 map equals the original map minus the extended prefix.
                assert(s2@.value().s2map == pt_s2map_inner(old(self)@.mappings).remove_keys(
                    Self::region_s2_prefix(*region, i as nat).dom(),
                )) by {
                    assert(old_s2map == pt_s2map_inner(old(self)@.mappings).remove_keys(
                        Self::region_s2_prefix(*region, prefix_pages).dom(),
                    ));
                    assert(s2@.value().s2map =~= pt_s2map_inner(old(self)@.mappings).remove_keys(
                        Self::region_s2_prefix(*region, i as nat).dom(),
                    ));
                }
                // Prove that every surviving mapping came from the original page table.
                assert forall|vb: SpecVAddr, fr: SpecFrame| #[trigger]
                    self.pt@.mappings.contains_pair(vb, fr) implies old(
                    self,
                ).pt@.mappings.contains_pair(vb, fr) by {
                    assert(old_mappings.contains_pair(vb, fr));
                    assert(old(self).pt@.mappings.contains_pair(vb, fr));
                }
                // Prove that every page in the target's remaining suffix stays covered.
                assert forall|page: nat|
                    i <= page < region.pages implies #[trigger] Self::mappings_cover_region_page(
                    self.pt@.mappings,
                    *region,
                    page,
                ) by {
                    assert(Self::mappings_cover_region_page(old_mappings, *region, page));
                    let (vb, fr) = choose|vb: SpecVAddr, fr: SpecFrame| #[trigger]
                        old_mappings.contains_pair(vb, fr) && region.spec_page_vaddr(page).within(
                            vb,
                            fr.size.as_nat(),
                        ) && region.spec_page_paddr(page).within(fr.base, fr.size.as_nat())
                            && fr.attr == region.attr;
                    assert(vb != vbase@) by {
                        if vb == vbase@ {
                            assert(region.spec_page_vaddr(page).0 < vbase@.0
                                + mapped_frame.size.as_nat());
                            assert(vbase@.0 + mapped_frame.size.as_nat() == region.spec_page_vaddr(
                                i as nat,
                            ).0);
                        }
                    }
                    assert(self.pt@.mappings.contains_pair(vb, fr));
                }
                // Prove mapping completeness for every non-target region.
                assert forall|j: int|
                    0 <= j < self.regions.len() && j
                        != ridx as int implies #[trigger] self.has_mapping_for_region(
                    self.regions[j],
                ) by {
                    let other = self.regions[j];
                    assert(self_before_unmap.has_mapping_for_region(other));
                    assert forall|page: nat|
                        page < other.pages implies #[trigger] Self::mappings_cover_region_page(
                        self.pt@.mappings,
                        other,
                        page,
                    ) by {
                        assert(Self::mappings_cover_region_page(old_mappings, other, page));
                        let (vb, fr) = choose|vb: SpecVAddr, fr: SpecFrame| #[trigger]
                            old_mappings.contains_pair(vb, fr) && other.spec_page_vaddr(
                                page,
                            ).within(vb, fr.size.as_nat()) && other.spec_page_paddr(page).within(
                                fr.base,
                                fr.size.as_nat(),
                            ) && fr.attr == other.attr;
                        assert(vb != vbase@) by {
                            if vb == vbase@ {
                                assert(fr == mapped_frame@);
                                assert(!other.spec_overlaps_vmem(*region));
                                assert(SpecVAddr::overlap(
                                    vbase@,
                                    mapped_frame.size.as_nat(),
                                    other.spec_page_vaddr(page),
                                    SPEC_PAGE_SIZE,
                                ));
                            }
                        }
                        assert(self.pt@.mappings.contains_pair(vb, fr));
                    }
                }
                // Prove surviving mappings are owned elsewhere or lie in the target suffix.
                assert forall|vb: SpecVAddr, fr: SpecFrame| #[trigger]
                    self.pt@.mappings.contains_pair(
                        vb,
                        fr,
                    ) implies self.has_region_for_mapping_except(vb, fr, ridx as int)
                    || region.spec_page_vaddr(i as nat).0 <= vb.0 by {
                    assert(old_mappings.contains_pair(vb, fr));
                    if !self.has_region_for_mapping_except(vb, fr, ridx as int) {
                        assert(region.spec_page_vaddr(prefix_pages).0 <= vb.0);
                        if vb.0 < region.spec_page_vaddr(i as nat).0 {
                            assert(vb != vbase@);
                            assert(self_before_unmap.pt@.wf());
                            assert(!SpecVAddr::overlap(
                                vbase@,
                                mapped_frame.size.as_nat(),
                                vb,
                                fr.size.as_nat(),
                            ));
                            assert(SpecVAddr::overlap(
                                vbase@,
                                mapped_frame.size.as_nat(),
                                vb,
                                fr.size.as_nat(),
                            ));
                        }
                    }
                }
                // Re-establish the token-coherence and page-table invariant clauses.
                assert(s2@.value().coherent(VmId(zone_id as nat)));
                assert(self.pt.invariants());
            }
        }

        proof {
            // At `i == region.pages`, prove no surviving mapping is owned by the target region.
            assert(ridx < self.regions.len());
            assert(i == region.pages);
            assert forall|vb: SpecVAddr, fr: SpecFrame| #[trigger]
                self.pt@.mappings.contains_pair(vb, fr) implies self.has_region_for_mapping_except(
                vb,
                fr,
                ridx as int,
            ) by {
                if !self.has_region_for_mapping_except(vb, fr, ridx as int) {
                    assert(region.spec_page_vaddr(i as nat).0 <= vb.0);
                    assert(old(self).pt@.mappings.contains_pair(vb, fr));
                    assert(old(self).has_region_for_mapping(vb, fr));
                    let owner = choose|owner: int|
                        #![auto]
                        0 <= owner < old(self).regions.len() && old(self).regions[owner].vstart@.0
                            <= vb.0 && vb.0 + fr.size.as_nat() <= old(self).regions[owner].vstart@.0
                            + old(self).regions[owner].pages * SPEC_PAGE_SIZE && old(
                            self,
                        ).regions[owner].pstart@.0 <= fr.base.0 && fr.base.0 + fr.size.as_nat()
                            <= old(self).regions[owner].pstart@.0 + old(self).regions[owner].pages
                            * SPEC_PAGE_SIZE && fr.attr == old(self).regions[owner].attr;
                    if owner != ridx as int {
                        assert(self.has_region_for_mapping_except(vb, fr, ridx as int));
                    }
                    assert(owner == ridx as int);
                    assert(old(self).regions[owner] == *region);
                    assert(fr.size.as_nat() > 0);
                    assert(region.spec_page_vaddr(i as nat).0 == region.vstart@.0
                        + region.pages as nat * SPEC_PAGE_SIZE);
                    assert(false);
                }
            }
        }
        let ghost removed_region = *region;
        let ghost self_before_remove = *self;
        self.regions.remove(ridx);
        proof {
            // Prove the region-validity clause of `self.invariants()` after reindexing.
            assert forall|idx: int|
                0 <= idx < self.regions.len() implies #[trigger] self.regions[idx].spec_valid() by {
                if idx < ridx as int {
                    assert(self.regions[idx] == self_before_remove.regions[idx]);
                } else {
                    assert(self.regions[idx] == self_before_remove.regions[idx + 1]);
                }
            }
            // Prove the region-vspace clause of `self.invariants()` after reindexing.
            assert forall|idx: int|
                0 <= idx
                    < self.regions.len() implies #[trigger] self.regions[idx].spec_within_vspace(
                self.pt@.constants.arch.vspace_size(),
            ) by {
                if idx < ridx as int {
                    assert(self.regions[idx] == self_before_remove.regions[idx]);
                } else {
                    assert(self.regions[idx] == self_before_remove.regions[idx + 1]);
                }
            }
            // Prove the pairwise region non-overlap clause after reindexing.
            assert forall|idx: int, jdx: int|
                0 <= idx < self.regions.len() && 0 <= jdx < self.regions.len() && idx
                    != jdx implies !self.regions[idx].spec_overlaps_vmem(self.regions[jdx]) by {
                let old_idx = if idx < ridx as int {
                    idx
                } else {
                    idx + 1
                };
                let old_jdx = if jdx < ridx as int {
                    jdx
                } else {
                    jdx + 1
                };
                assert(old_idx != old_jdx);
                assert(self.regions[idx] == self_before_remove.regions[old_idx]);
                assert(self.regions[jdx] == self_before_remove.regions[old_jdx]);
            }
            // Prove mapping completeness for every surviving region.
            assert forall|r: MemoryRegion| #[trigger]
                self.regions@.contains(r) implies self.has_mapping_for_region(r) by {
                let idx = choose|idx: int| 0 <= idx < self.regions.len() && self.regions[idx] == r;
                let old_idx = if idx < ridx as int {
                    idx
                } else {
                    idx + 1
                };
                assert(old_idx != ridx as int);
                assert(self_before_remove.regions[old_idx] == r);
                assert(self_before_remove.has_mapping_for_region(r));
                assert(self.pt@ == self_before_remove.pt@);
            }
            // Prove mapping soundness by translating each old owner to its new index.
            assert forall|vb: SpecVAddr, fr: SpecFrame| #[trigger]
                self.pt@.mappings.contains_pair(vb, fr) implies self.has_region_for_mapping(
                vb,
                fr,
            ) by {
                assert(self_before_remove.has_region_for_mapping_except(vb, fr, ridx as int));
                let owner = choose|owner: int|
                    #![auto]
                    0 <= owner < self_before_remove.regions.len() && owner != ridx as int
                        && self_before_remove.regions[owner].vstart@.0 <= vb.0 && vb.0
                        + fr.size.as_nat() <= self_before_remove.regions[owner].vstart@.0
                        + self_before_remove.regions[owner].pages * SPEC_PAGE_SIZE
                        && self_before_remove.regions[owner].pstart@.0 <= fr.base.0 && fr.base.0
                        + fr.size.as_nat() <= self_before_remove.regions[owner].pstart@.0
                        + self_before_remove.regions[owner].pages * SPEC_PAGE_SIZE && fr.attr
                        == self_before_remove.regions[owner].attr;
                let new_owner = if owner < ridx as int {
                    owner
                } else {
                    owner - 1
                };
                assert(self.regions[new_owner] == self_before_remove.regions[owner]);
            }
            assert(self.invariants());

            // Prove the region-set component of exact abstract removal.
            assert(self@.regions == old(self)@.regions.remove(removed_region)) by {
                assert forall|r: MemoryRegion| #[trigger]
                    self@.regions.contains(r) <==> old(self)@.regions.remove(
                        removed_region,
                    ).contains(r) by {
                    if self@.regions.contains(r) {
                        let idx = choose|idx: int|
                            0 <= idx < self.regions.len() && self.regions[idx] == r;
                        let old_idx = if idx < ridx as int {
                            idx
                        } else {
                            idx + 1
                        };
                        assert(old(self).regions[old_idx] == r);
                        assert(old_idx != ridx as int);
                        assert(r != removed_region) by {
                            if r == removed_region {
                                assert(old(self).regions[old_idx].spec_valid());
                                assert(old(self).regions[ridx as int].spec_valid());
                                assert(old(self).regions[old_idx].spec_overlaps_vmem(
                                    old(self).regions[ridx as int],
                                ));
                            }
                        }
                    }
                    if old(self)@.regions.remove(removed_region).contains(r) {
                        let old_idx = choose|old_idx: int|
                            0 <= old_idx < old(self).regions.len() && old(self).regions[old_idx]
                                == r;
                        assert(old_idx != ridx as int);
                        let idx = if old_idx < ridx as int {
                            old_idx
                        } else {
                            old_idx - 1
                        };
                        assert(self.regions[idx] == r);
                    }
                }
            }
            old(self).lemma_invariants_implies_wf();
            old(self)@.lemma_remove_region_exact_wf(removed_region);
            self.lemma_invariants_implies_wf();
            let expected = old(self)@.remove_region_exact(removed_region);
            // Prove the mapping component by completeness and soundness in both views.
            assert(self@.mappings == expected.mappings) by {
                assert forall|v: SpecVAddr, f: SpecFrame| #[trigger]
                    self@.mappings.contains_pair(v, f) implies expected.mappings.contains_pair(
                    v,
                    f,
                ) by {
                    let (r, page) = choose|r: MemoryRegion, page: nat|
                        #![trigger self@.regions.contains(r), r.spec_page_vaddr(page)]
                        self@.regions.contains(r) && page < r.pages && v == r.spec_page_vaddr(page)
                            && f == r.spec_frame(page);
                    assert(expected.regions.contains(r));
                }
                assert forall|v: SpecVAddr, f: SpecFrame| #[trigger]
                    expected.mappings.contains_pair(v, f) implies self@.mappings.contains_pair(
                    v,
                    f,
                ) by {
                    let (r, page) = choose|r: MemoryRegion, page: nat|
                        #![trigger expected.regions.contains(r), r.spec_page_vaddr(page)]
                        expected.regions.contains(r) && page < r.pages && v == r.spec_page_vaddr(
                            page,
                        ) && f == r.spec_frame(page);
                    assert(self@.regions.contains(r));
                }
                lemma_map_eq_pair(self@.mappings, expected.mappings);
            }
            assert(self@ == expected);

            // Translate removed mappings to discharge the final S2-map postcondition.
            Self::lemma_pt_s2map_inner_region(removed_region);
            let removed = choose|r: MemoryRegion| #[trigger]
                old(self)@.regions.contains(r) && r.vstart@ == start@;
            // Prove the spec-selected region is the concrete region removed at `ridx`.
            assert(removed == removed_region) by {
                let removed_idx = choose|j: int|
                    0 <= j < old(self).regions.len() && old(self).regions[j] == removed;
                assert(old(self).regions[removed_idx].vstart@ == start@);
                assert(old(self).regions[ridx as int].vstart@ == start@);
                assert(removed_idx == ridx as int) by {
                    if removed_idx != ridx as int {
                        assert(old(self).regions[removed_idx].spec_valid());
                        assert(old(self).regions[ridx as int].spec_valid());
                        assert(old(self).regions[removed_idx].spec_overlaps_vmem(
                            old(self).regions[ridx as int],
                        ));
                    }
                }
            }
            assert(old(self)@.remove_region(start@) == expected);
            assert(self@ == old(self)@.remove_region(start@));
            assert(s2@.value().s2map == pt_s2map_inner(self@.mappings));
            assert(s2@.value().coherent(VmId(zone_id as nat)));
        }
        s2
    }

    fn clear(
        &mut self,
        allocator: &GlobalAllocator<A>,
        zone_id: usize,
        mmu: &MmuHardware<I>,
        s2_tok: Tracked<MmuVmToken>,
        iommu: bool,
    ) -> (res: Tracked<MmuVmToken>) {
        let ghost old_inst_id = self.inst_id();
        let ghost old_pt_constants = self.pt_constants();
        let mut s2 = s2_tok;
        while !self.regions.is_empty()
            invariant
                self.invariants(),
                self.inst_id() == old_inst_id,
                self.pt_constants() == old_pt_constants,
                allocator.invariants(),
                self.inst_id() == allocator.inst_id(),
                mmu.wf(),
                I::valid_zone_id(zone_id),
                s2@.instance_id() == mmu.inst_id(),
                s2@.key() == VmId(zone_id as nat),
                s2@.value().s2map == pt_s2map_inner(self@.mappings),
                s2@.value().coherent(VmId(zone_id as nat)),
            decreases self.regions.len(),
        {
            let start = self.regions[0].vstart;
            let ghost region = self.regions@[0];
            let ghost regions_before = self.regions@;
            let ghost view_before = self@;
            proof {
                assert(self@.regions.contains(region));
                assert(self@.has_region_starting_at(region.vstart@));
                self.lemma_regions_no_duplicates();
                regions_before.unique_seq_to_set();
                self.lemma_invariants_implies_wf();
            }
            s2 = self.remove(allocator, start, zone_id, mmu, s2, iommu);
            proof {
                // Prove list removal is equivalent to the abstract set removal.
                view_before.lemma_remove_region_eq_exact(region);
                self.lemma_regions_no_duplicates();
                self.regions@.unique_seq_to_set();
                assert(self@.regions == view_before.regions.remove(region));
                assert(self.regions.len() < regions_before.len());
            }
        }
        proof {
            assert(self@.regions =~= Set::<MemoryRegion>::empty());
            self.lemma_pt_empty_if_regions_empty();
            assert(self@.mappings =~= Map::<SpecVAddr, SpecFrame>::empty());
            assert(self@ == old(self)@.clear());
        }
        s2
    }

    /// Converts the concrete vector/page-table invariants into abstract well-formedness.
    proof fn lemma_invariants_implies_wf(self) {
        // Prove `wf`'s region-validity predicate by choosing each region's vector index.
        assert forall|r: MemoryRegion| #[trigger]
            self@.regions.contains(r) implies r.spec_valid() by {
            let i = choose|i: int| 0 <= i < self.regions.len() && self.regions[i] == r;
        }
        // Prove `wf`'s pairwise non-overlap predicate from the indexed invariant.
        assert forall|r1: MemoryRegion, r2: MemoryRegion| #[trigger]
            self@.regions.contains(r1) && #[trigger] self@.regions.contains(r2) && r1
                != r2 implies !r1.spec_overlaps_vmem(r2) by {
            let i = choose|i: int| 0 <= i < self.regions.len() && self.regions[i] == r1;
            let j = choose|j: int| 0 <= j < self.regions.len() && self.regions[j] == r2;
            assert(i != j);
        }
        // Prove mapping completeness: every abstract region page has its expected frame.
        assert forall|r: MemoryRegion, page: nat|
            #![trigger self@.regions.contains(r), r.spec_page_vaddr(page)]
            self@.regions.contains(r) && page < r.pages implies self@.mappings.contains_pair(
            r.spec_page_vaddr(page),
            r.spec_frame(page),
        ) by {
            let i = choose|i: int| 0 <= i < self.regions.len() && self.regions[i] == r;
            let v = r.spec_page_vaddr(page);
            r.lemma_mappings_contains_pair(page);
            assert(self@.mappings.contains_key(v));
            let j = self.region_index_for_vaddr(v);
            assert(0 <= j < self.regions.len());
            if i != j {
                self.regions[j].lemma_mappings_sound(v);
                let other_page = choose|k: nat|
                    k < self.regions[j].pages && v == self.regions[j].spec_page_vaddr(k)
                        && self.regions[j].spec_mappings()[v] == self.regions[j].spec_frame(k);
                MemoryRegion::lemma_pages_disjoint(r, self.regions[j], page, other_page);
                assert(false);
            }
            assert(self@.mappings.contains_pair(v, r.spec_frame(page)));
        }
        // Prove mapping soundness: every abstract mapping is a page of an owned region.
        assert forall|v: SpecVAddr, f: SpecFrame| #[trigger]
            self@.mappings.contains_pair(v, f) implies exists|r: MemoryRegion, page: nat|
            #![trigger self@.regions.contains(r), r.spec_page_vaddr(page)]
            self@.regions.contains(r) && page < r.pages && v == r.spec_page_vaddr(page) && f
                == r.spec_frame(page) by {
            let i = self.region_index_for_vaddr(v);
            self.regions[i].lemma_mappings_sound(v);
            let page = choose|page: nat|
                page < self.regions[i].pages && v == self.regions[i].spec_page_vaddr(page)
                    && self.regions[i].spec_mappings()[v] == self.regions[i].spec_frame(page);
            assert(self@.regions.contains(self.regions[i]));
            assert(f == self.regions[i].spec_mappings()[v]);
        }
    }
}

/// Lemma. The equality of two maps. Two maps are equal if they have the same (key, value) pairs.
pub proof fn lemma_map_eq_pair<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    requires
        forall|k, v| m1.contains_pair(k, v) ==> m2.contains_pair(k, v),
        forall|k, v| m2.contains_pair(k, v) ==> m1.contains_pair(k, v),
    ensures
        m1 === m2,
{
    // Prove the maps have the same domain from pair inclusion in both directions.
    assert forall|k| m1.contains_key(k) <==> m2.contains_key(k) by {
        if m1.contains_key(k) {
            assert(m2.contains_pair(k, m1[k]));
        }
        if m2.contains_key(k) {
            assert(m1.contains_pair(k, m2[k]));
        }
    }
    // Prove equal values on that shared domain, completing map extensionality.
    assert forall|k| #[trigger] m1.contains_key(k) implies m1[k] === m2[k] by {
        let v = m1.index(k);
        assert(m1.contains_pair(k, v));
        assert(m2.contains_pair(k, v));
    }
    assert(m1 =~= m2);
}

} // verus!
