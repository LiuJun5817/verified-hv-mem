//! A memory set is a collection of memory areas that can be mapped into the virtual address
//! space of a zone (process). It manages the page table for the zone, and provides methods to
//! insert, remove, and find memory areas.
use crate::hardware::{HardwareInstr, MmuHardware};
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

/// The stage-2 map a single zone's page-table mappings induce, keyed like the
/// model's `s2_map`.
pub open spec fn pt_s2_map(mappings: Map<SpecVAddr, SpecFrame>, vm: VmId) -> Map<
    VmPageKey,
    S2Entry,
> {
    Map::new(
        |k: VmPageKey| k.vm == vm && mappings.contains_key(vaddr_of_gpa(k.gpa)),
        |k: VmPageKey| frame_to_s2(mappings[vaddr_of_gpa(k.gpa)]),
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

/// Removing a page-aligned `vaddr` from the byte-keyed `mappings` corresponds
/// exactly to removing its `VmPageKey` from the projected stage-2 map.  This is
/// what lets the per-page unmap loop carry `synced(pt_s2_map(self.pt@.mappings))`:
/// after `pt.unmap(vaddr)` the projection loses precisely `VmPageKey(vm, gpa)`.
pub proof fn lemma_pt_s2_map_remove(mappings: Map<SpecVAddr, SpecFrame>, vm: VmId, vaddr: SpecVAddr)
    requires
        vaddr.0 % SPEC_PAGE_SIZE == 0,
    ensures
        pt_s2_map(mappings.remove(vaddr), vm) == pt_s2_map(mappings, vm).remove(
            VmPageKey::new(vm, gpa_of_vaddr(vaddr)),
        ),
{
    let removed_key = VmPageKey::new(vm, gpa_of_vaddr(vaddr));
    let lhs = pt_s2_map(mappings.remove(vaddr), vm);
    let rhs = pt_s2_map(mappings, vm).remove(removed_key);
    lemma_vaddr_gpa_roundtrip(vaddr);
    assert forall|k: VmPageKey| #[trigger] lhs.contains_key(k) <==> rhs.contains_key(k) by {
        if k.vm == vm && vaddr_of_gpa(k.gpa) == vaddr {
            assert(vaddr_of_gpa(k.gpa) == vaddr_of_gpa(gpa_of_vaddr(vaddr)));
            assert(k.gpa == gpa_of_vaddr(vaddr)) by (nonlinear_arith)
                requires
                    k.gpa.0 * SPEC_PAGE_SIZE == gpa_of_vaddr(vaddr).0 * SPEC_PAGE_SIZE,
                    SPEC_PAGE_SIZE == 0x1000nat,
            ;
        }
    }
    assert forall|k: VmPageKey| #[trigger] lhs.contains_key(k) implies lhs[k] == rhs[k] by {}
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

    /// Lemma. Inserting a new region into the memory set preserves well-formedness.
    pub proof fn lemma_insert_region_preserves_wf(self, region: MemoryRegion)
        requires
            self.wf(),
            region.spec_valid(),
            !self.overlaps_vmem(region),
        ensures
            self.insert_region(region).wf(),
    {
        // TODO
        admit();
    }

    /// Lemma. Removing a region from the memory set preserves well-formedness.
    pub proof fn lemma_remove_region_preserves_wf(self, start: SpecVAddr)
        requires
            self.wf(),
            self.has_region_starting_at(start),
        ensures
            self.remove_region(start).wf(),
    {
        // TODO
        admit();
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
            self@ == old(self)@.insert_region(region),
            self.invariants(),
    ;

    /// Remove a memory region from the memory set by its starting virtual address,
    /// **forcing a stage-2 `TLBI` per page** via the tokenized MMU.  `vm` is the
    /// owning zone's id and `mmu` is the hardware handle that issues the `TLBI`s.
    ///
    /// The post-condition — every page this op removes is left clean in the hardware
    /// TLB — is provable only because each `TLBI` actually runs: only
    /// `MmuHardware::tlbi` can mutate the encapsulated TLB token, and the
    /// pre-condition does not assume the TLB is already clean, so the stale-TLB-reuse
    /// channel is closed by construction.
    fn remove(
        &mut self,
        allocator: &GlobalAllocator<A>,
        start: VAddr,
        vm: Ghost<VmId>,
        mmu: &mut MmuHardware<I>,
    )
        requires
            old(self).invariants(),
            allocator.invariants(),
            old(self).inst_id() == allocator.inst_id(),
            old(self)@.has_region_starting_at(start@),
            old(mmu).synced(vm@, pt_s2_map(old(self)@.mappings, vm@)),
        ensures
            self.inst_id() == old(self).inst_id(),
            self@ == old(self)@.remove_region(start@),
            self.invariants(),
            mmu.inst_id() == old(mmu).inst_id(),
            mmu.synced(vm@, pt_s2_map(self@.mappings, vm@)),
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
