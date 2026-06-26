//! A memory set is a collection of memory areas that can be mapped into the virtual address
//! space of a zone (process). It manages the page table for the zone, and provides methods to
//! insert, remove, and find memory areas.
use crate::hardware::{HardwareInstr, MmuHardware};
use crate::machine::hardware::mmu::MmuS2MapToken;
use crate::machine::types::{AccessPerms, GuestPage, PhysPage, S2Entry, VmId, VmPageKey};
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

// ─────────────────── byte-view ↔ stage-2 (`s2_map`) projection ───────────────────
// These connect the page-table's `Map<SpecVAddr, SpecFrame>` (the software byte
// view) to the model's `Map<VmPageKey, S2Entry>` (the MMU-reachable stage-2 map).
// They are what the per-page unmap loop and the `MmuHardware::synced` contract are
// stated over.
/// The guest page (IPA page number) of a page-aligned virtual address.
pub open spec fn gpa_of_vaddr(v: SpecVAddr) -> GuestPage {
    GuestPage(v.0 / SPEC_PAGE_SIZE)
}

/// The page-aligned virtual address of a guest page (inverse of [`gpa_of_vaddr`]
/// on aligned addresses).
pub open spec fn vaddr_of_gpa(gpa: GuestPage) -> SpecVAddr {
    SpecVAddr(gpa.0 * SPEC_PAGE_SIZE)
}

/// The stage-2 entry a page-table frame projects to.
pub open spec fn frame_to_s2(f: SpecFrame) -> S2Entry {
    S2Entry {
        page: PhysPage(f.base.0 / SPEC_PAGE_SIZE),
        access: AccessPerms {
            read: f.attr.readable,
            write: f.attr.writable,
            execute: f.attr.executable,
        },
        generation: 0,
    }
}

/// One zone's MMU-reachable stage-2 slice (`gpa -> S2Entry`) induced by its
/// page-table mappings — the value a zone's per-vm `s2map` token must equal at a
/// sync point.
pub open spec fn pt_s2map_inner(mappings: Map<SpecVAddr, SpecFrame>) -> Map<GuestPage, S2Entry> {
    Map::new(
        |g: GuestPage| mappings.contains_key(vaddr_of_gpa(g)),
        |g: GuestPage| frame_to_s2(mappings[vaddr_of_gpa(g)]),
    )
}

/// Round-trip on page-aligned addresses: `vaddr_of_gpa ∘ gpa_of_vaddr = id`.
pub proof fn lemma_vaddr_gpa_roundtrip(v: SpecVAddr)
    requires
        v.0 % SPEC_PAGE_SIZE == 0,
    ensures
        vaddr_of_gpa(gpa_of_vaddr(v)) == v,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(v.0 as int, SPEC_PAGE_SIZE as int);
    assert((v.0 / SPEC_PAGE_SIZE) * SPEC_PAGE_SIZE == v.0) by (nonlinear_arith)
        requires
            v.0 % SPEC_PAGE_SIZE == 0,
            v.0 as int == (SPEC_PAGE_SIZE as int) * (v.0 as int / SPEC_PAGE_SIZE as int)
                + v.0 as int % SPEC_PAGE_SIZE as int,
            SPEC_PAGE_SIZE == 0x1000nat,
    ;
}

/// Removing a page-aligned `vaddr` from the byte map removes exactly its guest
/// page from the projected slice — so after `pt.unmap(vaddr)` the slice loses
/// precisely `gpa_of_vaddr(vaddr)`, matching the `unmap_dsb_tlbi` token effect.
pub proof fn lemma_pt_s2map_inner_remove(mappings: Map<SpecVAddr, SpecFrame>, vaddr: SpecVAddr)
    requires
        vaddr.0 % SPEC_PAGE_SIZE == 0,
    ensures
        pt_s2map_inner(mappings.remove(vaddr)) == pt_s2map_inner(mappings).remove(
            gpa_of_vaddr(vaddr),
        ),
{
    let g0 = gpa_of_vaddr(vaddr);
    let lhs = pt_s2map_inner(mappings.remove(vaddr));
    let rhs = pt_s2map_inner(mappings).remove(g0);
    lemma_vaddr_gpa_roundtrip(vaddr);
    assert forall|g: GuestPage| #[trigger] lhs.contains_key(g) <==> rhs.contains_key(g) by {
        if vaddr_of_gpa(g) == vaddr {
            assert(vaddr_of_gpa(g) == vaddr_of_gpa(g0));
            assert(g == g0) by (nonlinear_arith)
                requires
                    g.0 * SPEC_PAGE_SIZE == g0.0 * SPEC_PAGE_SIZE,
                    SPEC_PAGE_SIZE == 0x1000nat,
            ;
        }
    }
    assert forall|g: GuestPage| #[trigger] lhs.contains_key(g) implies lhs[g] == rhs[g] by {}
    assert(lhs =~= rhs);
}

/// Inserting a page-aligned `vaddr => frame` into the byte map inserts exactly its
/// guest page into the projected slice — matching the `map_dsb` token effect.
pub proof fn lemma_pt_s2map_inner_insert(
    mappings: Map<SpecVAddr, SpecFrame>,
    vaddr: SpecVAddr,
    frame: SpecFrame,
)
    requires
        vaddr.0 % SPEC_PAGE_SIZE == 0,
    ensures
        pt_s2map_inner(mappings.insert(vaddr, frame)) == pt_s2map_inner(mappings).insert(
            gpa_of_vaddr(vaddr),
            frame_to_s2(frame),
        ),
{
    let g0 = gpa_of_vaddr(vaddr);
    let lhs = pt_s2map_inner(mappings.insert(vaddr, frame));
    let rhs = pt_s2map_inner(mappings).insert(g0, frame_to_s2(frame));
    lemma_vaddr_gpa_roundtrip(vaddr);
    assert forall|g: GuestPage| #[trigger] lhs.contains_key(g) <==> rhs.contains_key(g) by {
        if vaddr_of_gpa(g) == vaddr {
            assert(vaddr_of_gpa(g) == vaddr_of_gpa(g0));
            assert(g == g0) by (nonlinear_arith)
                requires
                    g.0 * SPEC_PAGE_SIZE == g0.0 * SPEC_PAGE_SIZE,
                    SPEC_PAGE_SIZE == 0x1000nat,
            ;
        }
    }
    assert forall|g: GuestPage| #[trigger] lhs.contains_key(g) implies lhs[g] == rhs[g] by {
        if g != g0 {
            assert(vaddr_of_gpa(g) != vaddr) by {
                if vaddr_of_gpa(g) == vaddr {
                    assert(g == g0) by (nonlinear_arith)
                        requires
                            g.0 * SPEC_PAGE_SIZE == g0.0 * SPEC_PAGE_SIZE,
                            SPEC_PAGE_SIZE == 0x1000nat,
                    ;
                }
            }
        }
    }
    assert(lhs =~= rhs);
}

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
