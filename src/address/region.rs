use super::{
    addr::{PAddr, SpecPAddr, SpecVAddr, VAddr},
    frame::{FrameSize, MemAttr, SpecFrame},
};
use vstd::prelude::*;

verus! {

/// Page size in bytes (4KB).
pub const PAGE_SIZE: usize = 0x1000;

/// Page size in spec mode
pub spec const SPEC_PAGE_SIZE: nat = 0x1000;

/// A memory region represents a contiguous range of virtual addresses with specific properties.
pub struct MemoryRegion {
    /// The starting virtual address of the region.
    pub start: VAddr,
    /// The number of 4KB pages in the region.
    pub pages: usize,
    /// The memory attributes of the region.
    pub attr: MemAttr,
    /// The mapping strategy for the region.
    pub mapper: Mapper,
}

impl MemoryRegion {
    /// Spec-mode validation check.
    pub open spec fn spec_valid(self) -> bool {
        &&& 0 < self.pages <= usize::MAX as nat / SPEC_PAGE_SIZE
        &&& self.start@.aligned(SPEC_PAGE_SIZE)
        &&& self.start@.0 <= usize::MAX as nat - (self.pages as nat * SPEC_PAGE_SIZE)
        &&& self.mapper.valid(self.start@.0 + (self.pages as nat * SPEC_PAGE_SIZE))
    }

    /// Spec-mode Calculate the end.
    pub open spec fn spec_end(&self) -> SpecVAddr
        recommends
            self.spec_valid(),
    {
        self.start@.offset(self.pages as nat * SPEC_PAGE_SIZE)
    }

    /// Spec-mode check if a virtual address is within the region.
    pub open spec fn spec_contains_vaddr(self, vaddr: SpecVAddr) -> bool {
        self.start@.0 <= vaddr.0 < self.start@.0 + (self.pages as nat) * SPEC_PAGE_SIZE
    }

    /// Spec-mode check if two regions overlap in virtual address space.
    pub open spec fn spec_overlaps_vmem(self, other: MemoryRegion) -> bool {
        SpecVAddr::overlap(
            self.start@,
            self.pages as nat * SPEC_PAGE_SIZE,
            other.start@,
            other.pages as nat * SPEC_PAGE_SIZE,
        )
    }

    /// Spec-mode translate a virtual address to physical address using the region's mapper.
    pub open spec fn spec_translate(self, vaddr: SpecVAddr) -> SpecPAddr
        recommends
            self.spec_valid(),
            self.spec_contains_vaddr(vaddr),
    {
        self.mapper.spec_map(vaddr)
    }

    /// Spec-mode check if a physical address is within the region.
    pub open spec fn spec_contains_paddr(self, paddr: SpecPAddr) -> bool {
        let start = self.mapper.spec_map(self.start@);
        let end = self.mapper.spec_map(self.spec_end());
        start.0 <= paddr.0 < end.0
    }

    /// Spec-mode check if two regions overlap in physical address space.
    pub open spec fn spec_overlaps_pmem(self, other: MemoryRegion) -> bool {
        let self_start = self.mapper.spec_map(self.start@);
        let self_end = self.mapper.spec_map(self.spec_end());
        let other_start = other.mapper.spec_map(other.start@);
        let other_end = other.mapper.spec_map(other.spec_end());

        if self_start.0 <= other_start.0 {
            self_end.0 > other_start.0
        } else {
            other_end.0 > self_start.0
        }
    }

    // ---------------------------------------------------------------------------
    // Region geometry: which page / frame a region maps each of its pages to.
    //
    // These spec functions live at the contract level (not in the security
    // refinement) because the page-level mapping a region induces is a property of
    // the region, and the trait below promises that a memory set's page table
    // realizes exactly these mappings (the "exact-dense" consistency).
    // ---------------------------------------------------------------------------
    /// Virtual byte address of page `i` (0-based) of region `r`.
    pub open spec fn spec_page_vaddr(self, i: nat) -> SpecVAddr {
        self.start@.offset(i * SPEC_PAGE_SIZE)
    }

    /// The (4 KiB) frame that region `r` maps its page `i` to.
    pub open spec fn spec_frame(self, i: nat) -> SpecFrame {
        SpecFrame {
            base: self.mapper.spec_map(self.spec_page_vaddr(i)),
            size: FrameSize::Size4K,
            attr: self.attr,
        }
    }

    /// The complete page table a single region induces (one frame per page).
    ///
    /// A vaddr is a key iff it is some page of `r`; `i` is determined by the vaddr,
    /// so the value `choose` is unique.
    pub open spec fn spec_mappings(self) -> Map<SpecVAddr, SpecFrame> {
        Map::new(
            |v: SpecVAddr| exists|i: nat| 0 <= i < self.pages && v == self.spec_page_vaddr(i),
            |v: SpecVAddr|
                {
                    let i = choose|i: nat| 0 <= i < self.pages && v == self.spec_page_vaddr(i);
                    self.spec_frame(i)
                },
        )
    }

    // ── facts about region geometry / spec_mappings ──────────────────────
    /// Distinct page indices of a region give distinct vaddrs.
    pub proof fn lemma_page_vaddr_injective(self, i: nat, j: nat)
        requires
            self.spec_page_vaddr(i) == self.spec_page_vaddr(j),
        ensures
            i == j,
    {
        assert(self.start@.0 + i * SPEC_PAGE_SIZE == self.start@.0 + j * SPEC_PAGE_SIZE);
        assert(i * SPEC_PAGE_SIZE == j * SPEC_PAGE_SIZE);
        assert(i == j) by (nonlinear_arith)
            requires
                i * SPEC_PAGE_SIZE == j * SPEC_PAGE_SIZE,
                SPEC_PAGE_SIZE == 0x1000nat,
        ;
    }

    /// Every page of a region is in its dense map, mapped to exactly its frame.
    pub proof fn lemma_mappings_contains_pair(self, i: nat)
        requires
            0 <= i < self.pages,
        ensures
            self.spec_mappings().contains_pair(self.spec_page_vaddr(i), self.spec_frame(i)),
    {
        let v = self.spec_page_vaddr(i);
        assert(self.spec_mappings().contains_key(v));  // witness i
        let k = choose|k: nat| 0 <= k < self.pages && v == self.spec_page_vaddr(k);
        assert(v == self.spec_page_vaddr(k));
        self.lemma_page_vaddr_injective(i, k);  // i == k
    }

    /// Every key of a region's dense map is one of its pages, mapped to its frame.
    pub proof fn lemma_mappings_sound(self, v: SpecVAddr)
        requires
            self.spec_mappings().contains_key(v),
        ensures
            exists|i: nat|
                0 <= i < self.pages && v == self.spec_page_vaddr(i) && self.spec_mappings()[v]
                    == self.spec_frame(i),
    {
        let i = choose|k: nat| 0 <= k < self.pages && v == self.spec_page_vaddr(k);
        assert(0 <= i < self.pages && v == self.spec_page_vaddr(i));
    }

    /// Two vmem-disjoint regions never share a page vaddr.
    pub proof fn lemma_pages_disjoint(r1: MemoryRegion, r2: MemoryRegion, i1: nat, i2: nat)
        requires
            r1.spec_valid(),
            r2.spec_valid(),
            !r1.spec_overlaps_vmem(r2),
            0 <= i1 < r1.pages,
            0 <= i2 < r2.pages,
        ensures
            r1.spec_page_vaddr(i1) != r2.spec_page_vaddr(i2),
    {
    }

    /// Check if the region is within valid virtual address space.
    pub fn valid(&self) -> (res: bool)
        ensures
            res == self.spec_valid(),
    {
        if self.pages == 0 || self.pages > usize::MAX / PAGE_SIZE {
            return false;
        }
        if !self.start.aligned(PAGE_SIZE) {
            return false;
        }
        if self.start.0 > usize::MAX - self.pages * PAGE_SIZE {
            return false;
        }
        match self.mapper {
            Mapper::Offset(off) => off % PAGE_SIZE == 0,
            Mapper::Fixed(paddr) => paddr % PAGE_SIZE == 0,
        }
    }

    /// Calculate the end virtual address of the region.
    pub fn end(&self) -> (res: VAddr)
        requires
            self.spec_valid(),
        ensures
            res@ == self.start@.offset(self.pages as nat * SPEC_PAGE_SIZE),
    {
        VAddr(self.start.0 + self.pages * PAGE_SIZE)
    }

    /// If two regions overlap in virtual address space.
    pub fn overlaps_vmem(&self, other: &MemoryRegion) -> (res: bool)
        requires
            self.spec_valid(),
            other.spec_valid(),
        ensures
            res == self.spec_overlaps_vmem(*other),
    {
        if self.start.0 <= other.start.0 {
            self.start.0 + self.pages * PAGE_SIZE > other.start.0
        } else {
            other.start.0 + other.pages * PAGE_SIZE > self.start.0
        }
    }

    /// If two regions overlap in physical address space.
    pub fn overlaps_pmem(&self, other: &MemoryRegion) -> (res: bool)
        requires
            self.spec_valid(),
            other.spec_valid(),
        ensures
            res == self.spec_overlaps_pmem(*other),
    {
        let self_start = self.mapper.map(self.start);
        let self_end = self.mapper.map(self.end());
        let other_start = other.mapper.map(other.start);
        let other_end = other.mapper.map(other.end());

        if self_start.0 <= other_start.0 {
            self_end.0 > other_start.0
        } else {
            other_end.0 > self_start.0
        }
    }

    /// Lemma: overlaps is symmetric.
    pub proof fn lemma_overlaps_vmem_symmetric(self, other: MemoryRegion)
        requires
            self.spec_valid(),
            other.spec_valid(),
        ensures
            self.spec_overlaps_vmem(other) == other.spec_overlaps_vmem(self),
    {
    }

    /// Lemma: If a region contains a virtual address, then it also contains the corresponding physical address.
    pub proof fn lemma_contains_vaddr_implies_contains_paddr(self, vaddr: SpecVAddr)
        requires
            self.spec_valid(),
            self.spec_contains_vaddr(vaddr),
        ensures
            self.spec_contains_paddr(self.spec_translate(vaddr)),
    {
        // TODO
        assume(false);
    }
}

/// The mapping strategy for a memory region.
#[derive(Clone, Copy, Debug)]
pub enum Mapper {
    Offset(usize),
    Fixed(usize),
}

impl Mapper {
    pub open spec fn valid(self, max_vaddr: nat) -> bool {
        match self {
            Self::Offset(off) => {
                &&& off % PAGE_SIZE == 0
                &&& max_vaddr <= usize::MAX as nat
            },
            Self::Fixed(paddr) => paddr % PAGE_SIZE == 0,
        }
    }

    pub open spec fn spec_map(self, vaddr: SpecVAddr) -> SpecPAddr
        recommends
            self.valid(vaddr.0),
    {
        match self {
            Self::Offset(off) => SpecPAddr(
                vstd::wrapping::usize_specs::wrapping_sub(vaddr.0 as usize, off) as nat,
            ),
            Self::Fixed(paddr) => SpecPAddr(paddr as nat),
        }
    }

    pub fn map(&self, vaddr: VAddr) -> (res: PAddr)
        requires
            self.valid(vaddr.0 as nat),
        ensures
            self.spec_map(vaddr@) == res@,
            vaddr.0 % PAGE_SIZE == 0 ==> res.0 % PAGE_SIZE == 0,
    {
        match self {
            Self::Offset(off) => PAddr(vaddr.0.wrapping_sub(*off)),
            Self::Fixed(paddr) => PAddr(*paddr),
        }
    }
}

} // verus!
