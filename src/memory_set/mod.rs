//! A memory set is a collection of memory areas that can be mapped into the virtual address
//! space of a zone (process). It manages the page table for the zone, and provides methods to
//! insert, remove, and find memory areas.
use crate::model::convert::pt_s2map_inner;
use crate::hardware::{HardwareInstr, MmuHardware};
use crate::hardware::spec::MmuS2MapToken;
use crate::model::types::{AccessPerms, GuestPage, PhysPage, S2Entry, VmId, VmPageKey};
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
        exists|r: MemoryRegion| self.regions.contains(r) && #[trigger] r.vstart@ == v
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
            self.regions.contains(r) && r.vstart@ == start;
        Self {
            regions: self.regions.remove(removed),
            mappings: self.mappings.remove_keys(removed.spec_mappings().dom()),
        }
    }

    /// Remove a specific region (by value) from the memory set, returning the new memory set.
    ///
    /// `remove_region(start)` equals `remove_region_exact(r)` for the unique region `r`
    /// starting at `start` (regions are vmem-disjoint, so `start` determines `r`).
    pub open spec fn remove_region_exact(&self, region: MemoryRegion) -> Self {
        Self {
            regions: self.regions.remove(region),
            mappings: self.mappings.remove_keys(region.spec_mappings().dom()),
        }
    }

    /// Inserting a fresh non-overlapping valid region keeps the memory set well-formed:
    /// the page table grows by exactly the region's dense mappings, and the new
    /// region's pages are vmem-disjoint from all old ones, so the exact-dense
    /// consistency is preserved.
    pub proof fn lemma_insert_region_wf(self, region: MemoryRegion)
        requires
            self.wf(),
            region.spec_valid(),
            !self.overlaps_vmem(region),
            !self.regions.contains(region),
        ensures
            self.insert_region(region).wf(),
    {
        let new = self.insert_region(region);
        let old_maps = self.mappings;
        let region_maps = region.spec_mappings();
        assert(new.regions =~= self.regions.insert(region));
        assert(new.mappings == old_maps.union_prefer_right(region_maps));

        // 1. regions valid
        assert forall|r: MemoryRegion| #[trigger]
            new.regions.contains(r) implies r.spec_valid() by {
            if r != region {
                assert(self.regions.contains(r));
            }
        }
        // 2. regions non-overlapping (the new region vs each old one, both directions)
        assert forall|r1: MemoryRegion, r2: MemoryRegion| #[trigger]
            new.regions.contains(r1) && #[trigger] new.regions.contains(r2) && r1
                != r2 implies !r1.spec_overlaps_vmem(r2) by {
            if r1 == region {
                assert(self.regions.contains(r2) && !r2.spec_overlaps_vmem(region));
                r2.lemma_overlaps_vmem_symmetric(region);
            } else if r2 == region {
                assert(self.regions.contains(r1) && !r1.spec_overlaps_vmem(region));
            } else {
                assert(self.regions.contains(r1) && self.regions.contains(r2));
            }
        }
        // 3. completeness: every region page is mapped to its frame
        assert forall|r: MemoryRegion, i: nat|
            #![trigger new.regions.contains(r), r.spec_page_vaddr(i)]
            new.regions.contains(r) && 0 <= i
                < r.pages implies new.mappings.contains_pair(
            r.spec_page_vaddr(i),
            r.spec_frame(i),
        ) by {
            if r == region {
                region.lemma_mappings_contains_pair(i);
            } else {
                assert(self.regions.contains(r));
                assert(!region_maps.contains_key(r.spec_page_vaddr(i))) by {
                    if region_maps.contains_key(r.spec_page_vaddr(i)) {
                        let j = choose|j: nat|
                            0 <= j < region.pages && r.spec_page_vaddr(i) == region.spec_page_vaddr(
                                j,
                            );
                        MemoryRegion::lemma_pages_disjoint(r, region, i, j);
                    }
                }
            }
        }
        // 4. soundness: every mapping is some region page's frame
        assert forall|v: SpecVAddr, f: SpecFrame| #[trigger]
            new.mappings.contains_pair(v, f) implies exists|r: MemoryRegion, i: nat|
            #![trigger new.regions.contains(r), r.spec_page_vaddr(i)]
            new.regions.contains(r) && 0 <= i < r.pages && v == r.spec_page_vaddr(i) && f
                == r.spec_frame(i) by {
            if region_maps.contains_key(v) {
                region.lemma_mappings_sound(v);
                assert(new.regions.contains(region));
            } else {
                assert(self.mappings.contains_pair(v, f));
                let (r2, i2) = choose|r2: MemoryRegion, i2: nat|
                    self.regions.contains(r2) && 0 <= i2 < r2.pages && v == r2.spec_page_vaddr(i2)
                        && f == r2.spec_frame(i2);
                assert(new.regions.contains(r2));
            }
        }
    }

    /// Removing a present region keeps the memory set well-formed: its (vmem-disjoint)
    /// keys are deleted, leaving exactly the other regions' dense mappings.
    pub proof fn lemma_remove_region_exact_wf(self, region: MemoryRegion)
        requires
            self.wf(),
            self.regions.contains(region),
        ensures
            self.remove_region_exact(region).wf(),
    {
        let new = self.remove_region_exact(region);
        let region_maps = region.spec_mappings();
        assert(new.regions =~= self.regions.remove(region));
        assert(new.mappings == self.mappings.remove_keys(region_maps.dom()));
        assert(region.spec_valid());  // region ∈ regions, self.wf() ⇒ valid

        // 1 & 2: regions are a subset of the old ones.
        assert forall|r: MemoryRegion| #[trigger]
            new.regions.contains(r) implies r.spec_valid() by {
            assert(self.regions.contains(r));
        }
        assert forall|r1: MemoryRegion, r2: MemoryRegion| #[trigger]
            new.regions.contains(r1) && #[trigger] new.regions.contains(r2) && r1
                != r2 implies !r1.spec_overlaps_vmem(r2) by {
            assert(self.regions.contains(r1) && self.regions.contains(r2));
        }
        // 3. completeness: remaining region pages are not `region`'s pages, so they survive.
        assert forall|r: MemoryRegion, i: nat|
            #![trigger new.regions.contains(r), r.spec_page_vaddr(i)]
            new.regions.contains(r) && 0 <= i
                < r.pages implies new.mappings.contains_pair(
            r.spec_page_vaddr(i),
            r.spec_frame(i),
        ) by {
            assert(self.regions.contains(r) && r != region);
            assert(!region_maps.dom().contains(r.spec_page_vaddr(i))) by {
                if region_maps.contains_key(r.spec_page_vaddr(i)) {
                    let j = choose|j: nat|
                        0 <= j < region.pages && r.spec_page_vaddr(i) == region.spec_page_vaddr(j);
                    MemoryRegion::lemma_pages_disjoint(r, region, i, j);
                }
            }
        }
        // 4. soundness: surviving mappings come from a remaining region (not `region`).
        assert forall|v: SpecVAddr, f: SpecFrame| #[trigger]
            new.mappings.contains_pair(v, f) implies exists|r: MemoryRegion, i: nat|
            #![trigger new.regions.contains(r), r.spec_page_vaddr(i)]
            new.regions.contains(r) && 0 <= i < r.pages && v == r.spec_page_vaddr(i) && f
                == r.spec_frame(i) by {
            assert(self.mappings.contains_pair(v, f));
            let (r, i) = choose|r: MemoryRegion, i: nat|
                self.regions.contains(r) && 0 <= i < r.pages && v == r.spec_page_vaddr(i) && f
                    == r.spec_frame(i);
            if r == region {
                region.lemma_mappings_contains_pair(i);  // ⇒ v ∈ region's keys: contradiction
            }
            assert(new.regions.contains(r));
        }
    }
}

/// Specification of a memory set viewed by higher-level components.
pub trait MemorySet<PT, A, I> where
    PT: PageTable<A>,
    A: BitmapAllocator,
    I: HardwareInstr,
    Self: Sized,
 {
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

    /// Insert a new memory region, **forcing a per-page `DSB` (`map`)** via the
    /// tokenized MMU so the vm's `s2map` slice token tracks the new mappings.  The
    /// slice token is threaded in/out and ends equal to `pt_s2map_inner(self@.mappings)`
    /// — the zone's sync point, re-established for the lock invariant.
    fn insert(
        &mut self,
        allocator: &GlobalAllocator<A>,
        region: MemoryRegion,
        vm: Ghost<VmId>,
        mmu: &mut MmuHardware<I>,
        s2_tok: Tracked<MmuS2MapToken>,
        iommu: bool,
    ) -> (res: Tracked<MmuS2MapToken>)
        requires
            old(self).invariants(),
            allocator.invariants(),
            old(self).inst_id() == allocator.inst_id(),
            region.spec_valid(),
            !old(self)@.overlaps_vmem(region),
            old(mmu).wf(),
            s2_tok@.instance_id() == old(mmu).inst_id(),
            s2_tok@.key() == vm@,
            s2_tok@.value() == pt_s2map_inner(old(self)@.mappings),
        ensures
            self.inst_id() == old(self).inst_id(),
            self@ == old(self)@.insert_region(region),
            self.invariants(),
            mmu.wf(),
            mmu.inst_id() == old(mmu).inst_id(),
            mmu.live_vms() == old(mmu).live_vms(),
            res@.instance_id() == mmu.inst_id(),
            res@.key() == vm@,
            res@.value() == pt_s2map_inner(self@.mappings),
    ;

    /// Remove a memory region by its starting virtual address, **forcing a per-page
    /// `DSB`+`TLBI` (`unmap_invalidate`)** via the tokenized MMU.  `vm` is the owning
    /// zone's id, `mmu` issues the maintenance instructions, and `s2_tok` is the
    /// zone's `s2map` slice token (threaded in/out).  The slice token ends equal to
    /// `pt_s2map_inner(self@.mappings)` — provable only because the instructions run
    /// (the encapsulated instance is the sole way to advance the slice token), so the
    /// stale-TLB-reuse channel is closed by construction.
    fn remove(
        &mut self,
        allocator: &GlobalAllocator<A>,
        start: VAddr,
        vm: Ghost<VmId>,
        mmu: &mut MmuHardware<I>,
        s2_tok: Tracked<MmuS2MapToken>,
        iommu: bool,
    ) -> (res: Tracked<MmuS2MapToken>)
        requires
            old(self).invariants(),
            allocator.invariants(),
            old(self).inst_id() == allocator.inst_id(),
            old(self)@.has_region_starting_at(start@),
            old(mmu).wf(),
            s2_tok@.instance_id() == old(mmu).inst_id(),
            s2_tok@.key() == vm@,
            s2_tok@.value() == pt_s2map_inner(old(self)@.mappings),
        ensures
            self.inst_id() == old(self).inst_id(),
            self@ == old(self)@.remove_region(start@),
            self.invariants(),
            mmu.wf(),
            mmu.inst_id() == old(mmu).inst_id(),
            mmu.live_vms() == old(mmu).live_vms(),
            res@.instance_id() == mmu.inst_id(),
            res@.key() == vm@,
            res@.value() == pt_s2map_inner(self@.mappings),
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
