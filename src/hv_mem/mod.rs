//! Abstract top-level hvisor memory model and specification.
//!
//! It is intended to serve as the top-level contract for memory safety:
//!   P1 RegionDisjoint   ——  static physical partitioning (region disjointness),
//!   P2 ZoneIsolated     ——  per-zone isolation enforced by page tables,
//!   P3 PTMemDisjoint    ——  page-table-memory discipline (PT pages allocated from pool, disjoint).
//!
//! Concrete implementations (mm.rs, page table code, allocators) should refine this model.
use crate::{
    address::{
        addr::{PAddr, SpecPAddr, SpecVAddr, VAddr},
        frame::{self, Frame, FrameSize, MemAttr, MemType, SpecFrame},
        region::{Mapper, MemoryRegion, PAGE_SIZE, SPEC_PAGE_SIZE},
    },
    bitmap_allocator::bitmap_trait::BitmapAllocator,
    global_allocator::GlobalAllocator,
    memory_set::{MemorySet, SpecMemorySet, VecMemorySet},
    page_table::{PTConstants, PageTable},
};
use std::marker::PhantomData;
use vstd::{prelude::*, tokens::InstanceId};

verus! {

/// Spec version of `HvConfigMemRegion`, used for specification and verification.
pub struct SpecHvConfigMemRegion {
    pub mem_type: MemType,
    pub pstart: SpecPAddr,
    pub vstart: SpecVAddr,
    pub size: nat,  // bytes
}

impl SpecHvConfigMemRegion {
    pub open spec fn vend(&self) -> SpecVAddr {
        SpecVAddr(self.vstart.0 + self.size)
    }

    pub open spec fn pend(&self) -> SpecPAddr {
        SpecPAddr(self.pstart.0 + self.size)
    }

    pub open spec fn valid(&self) -> bool {
        &&& self.size > 0
        &&& self.size % SPEC_PAGE_SIZE == 0
        &&& self.vstart.0 % SPEC_PAGE_SIZE == 0
        &&& self.pstart.0 % SPEC_PAGE_SIZE == 0
        &&& self.vstart.0 <= usize::MAX as nat - self.size
    }

    pub open spec fn contains_v(&self, v: SpecVAddr) -> bool {
        self.vstart.0 <= v.0 < self.vend().0
    }

    pub open spec fn contains_p(&self, p: SpecPAddr) -> bool {
        self.pstart.0 <= p.0 < self.pend().0
    }

    pub open spec fn phys_disjoint(&self, other: &SpecHvConfigMemRegion) -> bool {
        self.pend().0 <= other.pstart.0 || other.pend().0 <= self.pstart.0
    }

    /// A mapped region matches a config region if:
    ///
    /// - they have the same virtual interval;
    /// - for every page-aligned virtual address in the interval,
    ///   the mapped physical translation agrees with the config translation.
    pub open spec fn matches_region(&self, r: MemoryRegion) -> bool {
        &&& self.vstart == r.start@
        &&& self.size == (r.pages as nat) * SPEC_PAGE_SIZE
        // TODO

    }
}

/// A config type derived from `hvisor::config::HvConfigMemoryRegion`. It is used as the input to zone creation,
/// and carries both virtual and physical information for the initial memory regions of a zone.
#[derive(Clone, Copy)]
pub struct HvConfigMemRegion {
    pub mem_type: MemType,
    pub pstart: PAddr,
    pub vstart: VAddr,
    pub size: usize,
}

impl HvConfigMemRegion {
    pub open spec fn view(self) -> SpecHvConfigMemRegion {
        SpecHvConfigMemRegion {
            mem_type: self.mem_type,
            pstart: self.pstart@,
            vstart: self.vstart@,
            size: self.size as nat,
        }
    }

    /// Spec mode constructor for a `Mapper` from the config region.
    pub open spec fn spec_mapper(&self) -> Mapper
        recommends
            self.vstart.0 <= usize::MAX as nat,
            self.pstart.0 <= usize::MAX as nat,
    {
        Mapper::Offset(
            vstd::wrapping::usize_specs::wrapping_sub(
                self.vstart.0 as usize,
                self.pstart.0 as usize,
            ),
        )
    }

    /// Check if the config region is valid.
    pub fn valid(&self) -> (res: bool)
        ensures
            res == self@.valid(),
    {
        self.size > 0 && self.size % PAGE_SIZE == 0 && self.vstart.0 % PAGE_SIZE == 0
            && self.pstart.0 % PAGE_SIZE == 0 && self.vstart.0 <= usize::MAX - self.size
    }

    /// Construct a `Mapper` from the config region.
    pub fn mapper(&self) -> (res: Mapper)
        ensures
            res == self.spec_mapper(),
    {
        Mapper::Offset(self.vstart.0.wrapping_sub(self.pstart.0))
    }

    /// Construct a `MemoryRegion` from the config region.
    pub fn to_region(&self) -> (res: MemoryRegion)
        requires
            self@.valid(),
        ensures
            self@.matches_region(res),
            res.spec_valid(),
    {
        proof { lemma_wrapping_sub_preserves_page_alignment(self.vstart.0, self.pstart.0) }
        MemoryRegion {
            start: self.vstart,
            pages: self.size / PAGE_SIZE,
            attr: self.mem_type.to_attr(),
            mapper: self.mapper(),
        }
    }
}

/// A spec wrapper for one zone.
pub struct SpecZoneMem {
    pub zone_id: nat,
    pub inst_id: InstanceId,
    pub mem_set: SpecMemorySet,
}

impl SpecZoneMem {
    /// Well-formedness
    pub open spec fn wf(&self) -> bool {
        self.mem_set.wf()
    }
}

/// A concrete struct for one zone's memory, containing the zone id and the memory set.
pub struct ZoneMem<PT, M, A> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator {
    pub zone_id: usize,
    pub mem_set: M,
    pub _phantom: PhantomData<(PT, A)>,
}

impl<PT, M, A> ZoneMem<PT, M, A> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator {
    pub open spec fn view(&self) -> SpecZoneMem {
        SpecZoneMem {
            zone_id: self.zone_id as nat,
            inst_id: self.mem_set.inst_id(),
            mem_set: self.mem_set.view(),
        }
    }

    pub open spec fn invariants(&self) -> bool {
        &&& self.mem_set.invariants()
        &&& self.view().wf()
    }
}

/// The top-level abstract memory model of the hypervisor, consisting of multiple zones and
/// a global allocator instance id. The three key properties (P1, P2, P3) are defined as spec
/// functions on this struct.
pub struct SpecHvMem {
    /// All zones in the system.
    pub zones: Seq<SpecZoneMem>,
    /// Allocator instance id.
    pub inst_id: InstanceId,
}

impl SpecHvMem {
    /// Whether a zone id exists.
    pub open spec fn has_zone_id(&self, zid: nat) -> bool {
        exists|i: int| 0 <= i < self.zones.len() && #[trigger] self.zones[i].zone_id == zid
    }

    /// Index of a zone id, if it exists.
    pub open spec fn zone_index(&self, zid: nat) -> Option<int> {
        if self.has_zone_id(zid) {
            Some(
                choose|i: int| 0 <= i < self.zones.len() && #[trigger] self.zones[i].zone_id == zid,
            )
        } else {
            None
        }
    }

    /// Zone ids are unique.
    pub open spec fn zone_ids_unique(&self) -> bool {
        forall|i: int, j: int|
            0 <= i < j < self.zones.len() ==> #[trigger] self.zones[i].zone_id
                != #[trigger] self.zones[j].zone_id
    }

    /// Zone ids set
    pub open spec fn zone_id_set(&self) -> Set<nat> {
        Set::new(
            |zid: nat|
                exists|i: int| 0 <= i < self.zones.len() && #[trigger] self.zones[i].zone_id == zid,
        )
    }

    /// P1: static physical partitioning (region disjointness).
    pub open spec fn p1_region_disjoint(&self) -> bool {
        // Intra-zone disjointness.
        &&& forall|zi: int|
            0 <= zi < self.zones.len()
                ==> #[trigger] self.zones[zi].wf()
        // Inter-zone disjointness.
        &&& forall|z1: int, z2: int, i: int, j: int|
            0 <= z1 < self.zones.len() && 0 <= z2 < self.zones.len() && z1 != z2 && 0 <= i
                < self.zones[z1].mem_set.regions.len() && 0 <= j
                < self.zones[z2].mem_set.regions.len()
                ==> !self.zones[z1].mem_set.regions[i].spec_overlaps(
                self.zones[z2].mem_set.regions[j],
            )
    }

    /// P2: zone isolation enforced by page tables. If a virtual address is mapped in a zone, then its translation
    /// must be within the zone's physical regions.
    pub open spec fn p2_zone_isolated(&self) -> bool {
        forall|zi: int, v: SpecVAddr|
            0 <= zi < self.zones.len() && self.zones[zi].mem_set.contains_vaddr(v) ==> {
                let (i, paddr) = self.zones[zi].mem_set.translate(v);
                self.zones[zi].mem_set.regions[i].spec_contains_paddr(paddr)
            }
    }

    /// P3: page-table memory disjoint enforced by the global allocator.
    pub open spec fn p3_ptmem_disjoint(&self) -> bool {
        &&& self.zone_ids_unique()
        // All zones' instance id should be the same as the global allocator's instance id.
        // Then the invariant of AllocSpec ensures that page-table-memory disjointness is preserved.
        &&& forall|zi: int|
            0 <= zi < self.zones.len() ==> #[trigger] self.zones[zi].inst_id == self.inst_id
    }

    /// Full top-level memory invariant.
    pub open spec fn wf(&self) -> bool {
        &&& self.p1_region_disjoint()
        &&& self.p2_zone_isolated()
        &&& self.p3_ptmem_disjoint()
    }
}

/// The top-level memory manager struct of the hypervisor, containing all zones and the global allocator.
pub struct HvMem<PT, M, A> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator {
    /// All zones in the system.
    pub zone_mem_list: Vec<ZoneMem<PT, M, A>>,
    /// Global allocator.
    pub alloc: GlobalAllocator<A>,
}

impl<PT, M, A> HvMem<PT, M, A> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator {
    pub open spec fn view(&self) -> SpecHvMem {
        SpecHvMem {
            zones: Seq::new(self.zone_mem_list.len() as nat, |i: int| self.zone_mem_list[i].view()),
            inst_id: self.alloc.inst_id(),
        }
    }

    pub open spec fn invariants(&self) -> bool {
        // The high-level view invariants (P1, P2, P3) should hold.
        //
        // Note: P3 (page-table-memory disjoint) is actually implied by the state machine `AllocSpec` invariant,
        // but we still include it here for clarity.
        &&& self.view().wf()
        // Implementation-level invariants: each zone's invariant holds, and the allocator invariant holds.
        &&& forall|i: int|
            0 <= i < self.zone_mem_list.len() ==> #[trigger] self.zone_mem_list[i].invariants()
        &&& self.alloc.invariants()
    }

    /// init root zone
    pub fn init(
        alloc: GlobalAllocator<A>,
        pt_constants: PTConstants,
        root_cfg_regions: Vec<HvConfigMemRegion>,
    ) -> (res: Result<Self, ()>)
        requires
            alloc.invariants(),
            pt_constants@.valid(),
            forall|level: nat|
                level < pt_constants.arch@.level_count() ==> pt_constants.arch@.entry_count(level)
                    == 512,
            pt_constants.arch@.leaf_frame_size() == FrameSize::Size4K,
        ensures
            match res {
                Ok(hv) => {
                    &&& hv.zone_mem_list.len() == 1
                    &&& hv.zone_mem_list[0].zone_id == 0
                    &&& hv.invariants()
                },
                Err(()) => true,
            },
    {
        let mut hv = Self { zone_mem_list: Vec::new(), alloc };
        proof {
            assert(hv.alloc.invariants());
            assert(hv.view().zones == Seq::<SpecZoneMem>::empty());
            assert(hv.view().zone_id_set() =~= Set::<nat>::empty());
            assert(hv.invariants());
        }
        let r = hv.create_zone(pt_constants, 0usize, root_cfg_regions);
        if r.is_err() {
            return Err(());
        }
        Ok(hv)
    }

    /// Find the index of a zone by its id, if it exists.
    pub fn find_zone(&self, zone_id: usize) -> (res: Option<usize>)
        ensures
            match res {
                Some(i) => {
                    &&& i < self.zone_mem_list.len()
                    &&& self.zone_mem_list[i as int].zone_id == zone_id
                },
                None => {
                    &&& forall|i: int|
                        0 <= i < self.zone_mem_list.len()
                            ==> #[trigger] self.zone_mem_list[i].zone_id != zone_id
                },
            },
    {
        let mut i: usize = 0;
        while i < self.zone_mem_list.len()
            invariant
                i <= self.zone_mem_list.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] self.zone_mem_list[j].zone_id != zone_id,
            decreases self.zone_mem_list.len() - i,
        {
            if self.zone_mem_list[i].zone_id == zone_id {
                return Some(i);
            }
            i += 1;
        }
        None
    }

    /// Create a new zone with the given id and config regions, and insert it into the system.
    pub fn create_zone(
        &mut self,
        pt_constants: PTConstants,
        zone_id: usize,
        cfg_regions: Vec<HvConfigMemRegion>,
    ) -> (res: Result<(), ()>)
        requires
            old(self).invariants(),
            old(self).alloc.invariants(),
            pt_constants@.valid(),
            forall|level: nat|
                level < pt_constants.arch@.level_count() ==> pt_constants.arch@.entry_count(level)
                    == 512,
            pt_constants.arch@.leaf_frame_size() == FrameSize::Size4K,
        ensures
            match res {
                Ok(()) => {
                    &&& self.zone_mem_list.len() == old(self).zone_mem_list.len() + 1
                    &&& self.zone_mem_list[self.zone_mem_list.len() - 1].zone_id == zone_id
                    &&& self.invariants()
                },
                Err(()) => true,
            },
    {
        if self.find_zone(zone_id).is_some() {
            return Err(());
        }
        let mut i: usize = 0;
        // ensure every region is valid
        while i < cfg_regions.len()
            invariant
                i <= cfg_regions.len(),
                forall|j: int| 0 <= j < i ==> #[trigger] cfg_regions[j]@.valid(),
            decreases cfg_regions.len() - i,
        {
            if !cfg_regions[i].valid() {
                return Err(());
            }
            i += 1;
        }

        // Create an empty memory set for the new zone
        let mut mem_set = M::new(&self.alloc, pt_constants);
        let mut j: usize = 0;
        // TODO: add invariants about `cfg_regions`
        while j < cfg_regions.len()
            invariant
                j <= cfg_regions.len(),
                forall|k: int| 0 <= k < cfg_regions.len() ==> #[trigger] cfg_regions[k]@.valid(),
                mem_set.invariants(),
                mem_set.inst_id() == self.alloc.inst_id(),
                self.alloc.invariants(),
                self.zone_mem_list.len() == old(self).zone_mem_list.len(),
            decreases cfg_regions.len() - j,
        {
            assert(cfg_regions[j as int]@.valid());
            let region = cfg_regions[j].to_region();
            let insert_res = mem_set.insert(&self.alloc, region);
            if insert_res.is_err() {
                return Err(());
            }
            j += 1;
        }

        let zone_mem = ZoneMem { zone_id, mem_set, _phantom: PhantomData };
        proof {
            mem_set.lemma_invariants_implies_wf();
            assert(zone_mem.view().wf());
            assert(zone_mem.invariants());
        }
        self.zone_mem_list.push(zone_mem);
        proof {
            assert(forall|i: int|
                #![auto]
                0 <= i < self@.zones.len() ==> if i == self@.zones.len() - 1 {
                    self@.zones[i].mem_set == mem_set@
                } else {
                    self@.zones[i] == old(self)@.zones[i]
                });
            // TODO: need to add more constraints to `cfg_regions` to ensure that the new zone is disjoint
            // with existing zones, so that we can prove `self.view().p1_region_disjoint()` here.
            assume(self.view().p1_region_disjoint());
            assume(self.view().p2_zone_isolated());
            assert(self.view().p3_ptmem_disjoint());
            assert(self.invariants());
        }
        Ok(())
    }

    /// Remove a zone by its id, and return the removed zone's memory if successful.
    pub fn remove_zone(&mut self, zone_id: usize) -> (res: Result<ZoneMem<PT, M, A>, ()>)
        requires
            old(self).invariants(),
        ensures
            self.invariants(),
            match res {
                Ok(z) => {
                    &&& z.zone_id == zone_id
                    &&& self.zone_mem_list.len() + 1 == old(self).zone_mem_list.len()
                },
                Err(()) => { &&& self.zone_mem_list.len() == old(self).zone_mem_list.len() },
            },
    {
        let res = self.find_zone(zone_id);
        if res.is_none() {
            return Err(());
        }
        let idx = res.unwrap();
        let zone = self.zone_mem_list.swap_remove(idx);
        proof {
            assert(forall|i: int|
                0 <= i < self@.zones.len() ==> if i == idx {
                    self@.zones[i] == old(self)@.zones[old(self)@.zones.len() - 1]
                } else {
                    self@.zones[i] == old(self)@.zones[i]
                });
            assert(self.invariants());
        }
        Ok(zone)
    }
}

/// Lemma: wrapping_sub of two page-aligned addresses is still page-aligned.
proof fn lemma_wrapping_sub_preserves_page_alignment(x: usize, y: usize)
    requires
        x % PAGE_SIZE == 0,
        y % PAGE_SIZE == 0,
    ensures
        vstd::wrapping::usize_specs::wrapping_sub(x, y) % PAGE_SIZE == 0,
{
}

} // verus!
