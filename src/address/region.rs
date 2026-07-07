use vstd::prelude::*;

verus! {
use core::prelude::rust_2021::derive;
use core::fmt::Debug;
use core::marker::Copy;
use core::clone::Clone;

use super::{
    addr::{PAddr, SpecPAddr, SpecVAddr, VAddr},
    frame::{FrameSize, MemAttr, SpecFrame},
};

/// Page size in bytes (4KB).
pub const PAGE_SIZE: usize = 0x1000;

/// Page size in spec mode
pub spec const SPEC_PAGE_SIZE: nat = 0x1000;

/// A memory region represents a contiguous range of virtual addresses with specific properties.
pub struct MemoryRegion {
    /// The starting virtual address of the region.
    pub vstart: VAddr,
    /// The starting physical address of the region.
    pub pstart: PAddr,
    /// The number of 4KB pages in the region.
    pub pages: usize,
    /// The memory attributes of the region.
    pub attr: MemAttr,
}

impl MemoryRegion {
    /// Spec-mode validation check.
    pub open spec fn spec_valid(self) -> bool {
        &&& 0 < self.pages <= usize::MAX as nat / SPEC_PAGE_SIZE
        &&& self.vstart@.aligned(SPEC_PAGE_SIZE)
        &&& self.vstart@.0 + self.pages * SPEC_PAGE_SIZE <= usize::MAX
        &&& self.pstart@.aligned(SPEC_PAGE_SIZE)
        &&& self.pstart@.0 + self.pages * SPEC_PAGE_SIZE <= usize::MAX
    }

    /// Spec-mode Calculate the end.
    pub open spec fn spec_vend(&self) -> SpecVAddr
        recommends
            self.spec_valid(),
    {
        self.vstart@.offset(self.pages as nat * SPEC_PAGE_SIZE)
    }

    /// Spec-mode check if a virtual address is within the region.
    pub open spec fn spec_contains_vaddr(self, vaddr: SpecVAddr) -> bool {
        self.vstart@.0 <= vaddr.0 < self.vstart@.0 + (self.pages as nat) * SPEC_PAGE_SIZE
    }

    /// Spec-mode check if two regions overlap in virtual address space.
    pub open spec fn spec_overlaps_vmem(self, other: MemoryRegion) -> bool {
        SpecVAddr::overlap(
            self.vstart@,
            self.pages as nat * SPEC_PAGE_SIZE,
            other.vstart@,
            other.pages as nat * SPEC_PAGE_SIZE,
        )
    }

    /// Spec-mode translate a virtual address to physical address.
    pub open spec fn spec_translate(self, vaddr: SpecVAddr) -> SpecPAddr
        recommends
            self.spec_valid(),
            self.spec_contains_vaddr(vaddr),
    {
        SpecPAddr((vaddr.0 - self.vstart.0 + self.pstart.0) as nat)
    }

    /// Spec-mode check if a physical address is within the region.
    pub open spec fn spec_contains_paddr(self, paddr: SpecPAddr) -> bool {
        self.pstart@.0 <= paddr.0 < self.pstart@.0 + (self.pages as nat) * SPEC_PAGE_SIZE
    }

    /// Spec-mode check if two regions overlap in physical address space.
    pub open spec fn spec_overlaps_pmem(self, other: MemoryRegion) -> bool {
        SpecPAddr::overlap(
            self.pstart@,
            self.pages as nat * SPEC_PAGE_SIZE,
            other.pstart@,
            other.pages as nat * SPEC_PAGE_SIZE,
        )
    }

    /// Virtual byte address of page `i` (0-based) of region `r`.
    pub open spec fn spec_page_vaddr(self, i: nat) -> SpecVAddr {
        self.vstart@.offset(i * SPEC_PAGE_SIZE)
    }

    /// Physical byte address of page `i` (0-based) of region `r`.
    pub open spec fn spec_page_paddr(self, i: nat) -> SpecPAddr {
        self.pstart@.offset(i * SPEC_PAGE_SIZE)
    }

    /// The (4 KiB) frame that region `r` maps its page `i` to.
    pub open spec fn spec_frame(self, i: nat) -> SpecFrame {
        SpecFrame { base: self.spec_page_paddr(i), size: FrameSize::Size4K, attr: self.attr }
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
        assert(self.vstart@.0 + i * SPEC_PAGE_SIZE == self.vstart@.0 + j * SPEC_PAGE_SIZE);
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
        if !self.vstart.aligned(PAGE_SIZE) {
            return false;
        }
        if self.vstart.0 > usize::MAX - self.pages * PAGE_SIZE {
            return false;
        }
        if !self.pstart.aligned(PAGE_SIZE) {
            return false;
        }
        if self.pstart.0 > usize::MAX - self.pages * PAGE_SIZE {
            return false;
        }
        true
    }

    /// Calculate the end virtual address of the region.
    pub fn vend(&self) -> (res: VAddr)
        requires
            self.spec_valid(),
        ensures
            res@ == self.vstart@.offset(self.pages as nat * SPEC_PAGE_SIZE),
    {
        VAddr(self.vstart.0 + self.pages * PAGE_SIZE)
    }

    /// If two regions overlap in virtual address space.
    pub fn overlaps_vmem(&self, other: &MemoryRegion) -> (res: bool)
        requires
            self.spec_valid(),
            other.spec_valid(),
        ensures
            res == self.spec_overlaps_vmem(*other),
    {
        if self.vstart.0 <= other.vstart.0 {
            self.vstart.0 + self.pages * PAGE_SIZE > other.vstart.0
        } else {
            other.vstart.0 + other.pages * PAGE_SIZE > self.vstart.0
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
        if self.pstart.0 <= other.pstart.0 {
            self.pstart.0 + self.pages * PAGE_SIZE > other.pstart.0
        } else {
            other.pstart.0 + other.pages * PAGE_SIZE > self.pstart.0
        }
    }

    /// Translate a virtual address to physical address.
    pub fn translate(&self, vaddr: VAddr) -> (res: PAddr)
        requires
            self.spec_valid(),
            self.spec_contains_vaddr(vaddr@),
        ensures
            res@ == self.spec_translate(vaddr@),
    {
        PAddr((vaddr.0 - self.vstart.0 + self.pstart.0) as usize)
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
    }
}

} // verus!
