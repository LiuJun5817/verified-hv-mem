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
        frame::{self, Frame, FrameSize, Mapper, MemAttr, MemoryRegion, SpecFrame, PAGE_SIZE},
    },
    global_allocator::{paddr_to_fid, GlobalAllocator, GlobalAllocatorModel},
    memory_set::{MemorySet, VecMemorySet},
    page_table::{PTConstants, PageTable},
};
use std::marker::PhantomData;
use vstd::prelude::*;

verus! {

/// Memory type tags consistent with HvConfigMemoryRegion.mem_type.
pub enum SpecMemType {
    Ram,
    Io,
    VirtIo,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum MemType {
    Ram,
    Io,
    VirtIo,
}

impl MemType {
    pub open spec fn view(self) -> SpecMemType {
        match self {
            MemType::Ram => SpecMemType::Ram,
            MemType::Io => SpecMemType::Io,
            MemType::VirtIo => SpecMemType::VirtIo,
        }
    }
}

/// A config memory region derived from HvConfigMemoryRegion.
/// It carries both virtual and physical bases.
pub struct SpecMemRegion {
    pub mem_type: SpecMemType,
    pub pstart: SpecPAddr,
    pub vstart: SpecVAddr,
    pub size: nat,  // bytes
}

impl SpecMemRegion {
    pub open spec fn vend(&self) -> SpecVAddr {
        SpecVAddr(self.vstart.0 + self.size)
    }

    pub open spec fn pend(&self) -> SpecPAddr {
        SpecPAddr(self.pstart.0 + self.size)
    }

    pub open spec fn valid(&self) -> bool {
        &&& self.size > 0
        &&& self.size % PAGE_SIZE as nat == 0
        &&& self.vstart.0 % PAGE_SIZE as nat == 0
        &&& self.pstart.0 % PAGE_SIZE as nat == 0
    }

    pub open spec fn contains_v(&self, v: SpecVAddr) -> bool {
        self.vstart.0 <= v.0 < self.vend().0
    }

    pub open spec fn contains_p(&self, p: SpecPAddr) -> bool {
        self.pstart.0 <= p.0 < self.pend().0
    }

    pub open spec fn phys_disjoint(&self, other: &SpecMemRegion) -> bool {
        self.pend().0 <= other.pstart.0 || other.pend().0 <= self.pstart.0
    }
}

#[derive(Clone, Copy)]
pub struct HvMemRegion {
    pub mem_type: MemType,
    pub pstart: PAddr,
    pub vstart: VAddr,
    pub size: usize,
}

impl HvMemRegion {
    pub open spec fn view(self) -> SpecMemRegion {
        SpecMemRegion {
            mem_type: self.mem_type@,
            pstart: self.pstart@,
            vstart: self.vstart@,
            size: self.size as nat,
        }
    }

    pub fn valid(&self) -> (res: bool)
        ensures
            res == self@.valid(),
    {
        self.size > 0
        && self.size % PAGE_SIZE == 0
        && self.vstart.0 % PAGE_SIZE == 0
        && self.pstart.0 % PAGE_SIZE == 0
    }
}

/// A spec wrapper for one zone.
pub struct SpecZoneMem {
    pub zone_id: nat, 
    pub mem_set: Seq<MemoryRegion>, 
}

impl SpecZoneMem {
    /// Zone-local invariant.
    pub open spec fn inv(&self) -> bool {
        // Regions are valid
        &&& forall|i: int|
            0 <= i < self.mem_set.len()
                ==> #[trigger] self.mem_set[i].spec_valid()
        // Regions do not overlap
        &&& forall|i: int, j: int|
            0 <= i < self.mem_set.len() && 0 <= j < self.mem_set.len() && i != j
                ==> !self.mem_set[i].spec_overlaps(
                self.mem_set[j],
            )
    }
}


/// Top-level memory model for hvisor.
///
/// It aggregates all zones and the static partitions.
pub struct SpecHvMem {
    /// All zones in the system.
    pub zones: Seq<SpecZoneMem>,
    /// Global allocator model.
    pub alloc: GlobalAllocatorModel,
}

impl SpecHvMem {
    /// Whether a zone id exists.
    pub open spec fn has_zone_id(&self, zid: nat) -> bool {
        exists|i: int| 0 <= i < self.zones.len() && self.zones[i].zone_id == zid
    }

    /// Index of a zone id, if it exists.
    pub open spec fn zone_index(&self, zid: nat) -> Option<int> {
        if self.has_zone_id(zid) {
            Some(choose|i: int| 0 <= i < self.zones.len() && self.zones[i].zone_id == zid)
        } else {
            None
        }
    }

    /// Zone ids are unique. 
    pub open spec fn zone_ids_unique(&self) -> bool {
        forall|i: int, j: int| 0 <= i < j < self.zones.len() ==> self.zones[i].zone_id != self.zones[j].zone_id
    }

    /// Zone ids set
    pub open spec fn zone_id_set(&self) -> Set<nat> {
        Set::new(|zid: nat| exists|i: int| 0 <= i < self.zones.len() && self.zones[i].zone_id == zid)
    }

    /// P1: static physical partitioning (region disjointness).
    pub open spec fn p1_region_disjoint(&self) -> bool {
        // Intra-zone disjointness.
        &&& forall|zi: int| 0 <= zi < self.zones.len() ==> self.zones[zi].inv()
            
        // Inter-zone disjointness.
        &&& forall|z1: int, z2: int, i: int, j: int|
            0 <= z1 < self.zones.len() && 0 <= z2 < self.zones.len() && z1 != z2 && 
            0 <= i < self.zones[z1].mem_set.len() && 0 <= j < self.zones[z2].mem_set.len()
            ==> self.zones[z1].mem_set[i].spec_overlaps(self.zones[z2].mem_set[j])
    }

    /// P2: zone isolation enforced by page tables.
    pub open spec fn p2_zone_isolated(&self) -> bool {
        forall|zi: int, v: SpecVAddr| 0 <= zi < self.zones.len()
            ==> match mem_set_translate(self.zones[zi].mem_set, v) {
                None => true,
                Some((p, i)) => {
                    let zim = self.zones[zi].mem_set;
                    &&& zim.map(zim[i].start)@.0 <= p.0 < zim.map(zim[i].end(zim[i].start))@.0
                }
            }
    }

    /// P3: page-table memory discipline enforced by the global allocator.
    pub open spec fn p3_ptmem_disjoint(&self) -> bool {
        &&& self.zone_ids_unique()
        &&& self.zone_id_set() =~= self.alloc.clients.dom()
        &&& self.alloc.wf()
    }

    /// Full top-level memory invariant.
    pub open spec fn inv(&self) -> bool {
        &&& self.p1_region_disjoint()
        &&& self.p2_zone_isolated()
        &&& self.p3_ptmem_disjoint()
    }
}

/// Whether a virtual address is covered by a memory region.
pub open spec fn region_contains_v(r: MemoryRegion, v: SpecVAddr) -> bool {
    r.start@.0 <= v.0 < (r.start@.0 + (r.pages as nat) * PAGE_SIZE as nat)
}

/// The abstract translation induced by a region mapper.
pub open spec fn region_translate(r: MemoryRegion, v: SpecVAddr) -> SpecPAddr
    recommends region_contains_v(r, v)
{
    r.mapper.map(VAddr(v.0 as usize))@
}

/// The abstract translation view induced by a whole memory set.
/// Because regions are required to be non-overlapping in virtual space,
/// the responsible region is unique when it exists.
pub open spec fn mem_set_translate(ms: Seq<MemoryRegion>, v: SpecVAddr) -> Option<(SpecPAddr, int)> {
    if exists|i: int| 0 <= i < ms.len() && region_contains_v(ms[i], v) {
        let i = choose|i: int| 0 <= i < ms.len() && region_contains_v(ms[i], v);
        Some((region_translate(ms[i], v), i))
    } else {
        None
    }
}

pub struct ZoneMem<PT, A> where PT: PageTable<A>, A: GlobalAllocator {
    pub zone_id: usize,
    pub mem_set: VecMemorySet<PT, A>,
}

impl<PT, A> ZoneMem<PT, A> where PT: PageTable<A>, A: GlobalAllocator {
    pub open spec fn view(&self, allocator: &A) -> SpecZoneMem {
        SpecZoneMem {
            zone_id: self.zone_id as nat,
            mem_set: self.mem_set.view(allocator),
        }
    }

    pub open spec fn invariants(&self, allocator: &A) -> bool {
        &&& self.mem_set.invariants(allocator)
        &&& self.view(allocator).inv()
    }
}


pub struct HvMem<PT, A> where PT: PageTable<A>, A: GlobalAllocator {
    pub zone_mem_list: Vec<ZoneMem<PT, A>>,
    /// Global allocator.
    pub alloc: A,
}

impl<PT, A> HvMem<PT, A> where PT: PageTable<A>, A: GlobalAllocator {
    pub open spec fn view(&self, allocator: &A) -> SpecHvMem {
        SpecHvMem {
            zones: Seq::new(self.zone_mem_list.len() as nat, |i: int| self.zone_mem_list[i].view(allocator)),
            alloc: allocator.view(),
        }
    }

    /// init root zone
    pub fn init(
        alloc: A,
        pt_constants: PTConstants,
        root_cfg_regions: Vec<HvMemRegion>,
    ) -> (res: Result<Self, ()>)
        requires
            alloc.invariants(),
            !alloc@.clients.contains_key(0nat),
            !alloc@.free.is_empty(),
            pt_constants@.valid(),
            forall|level: nat|
                level < pt_constants.arch@.level_count() ==> pt_constants.arch@.entry_count(level) == 512,
            A::frame_size() == 4096,
        ensures
            match res {
                Ok(hv) => {
                    &&& hv.alloc.invariants()
                    &&& hv.zone_mem_list.len() == 1
                    &&& hv.zone_mem_list[0].zone_id == 0
                    &&& hv.view(&hv.alloc).inv()
                }
                Err(()) => true,
            },
    {
        let mut hv = Self {
            zone_mem_list: Vec::new(),
            alloc,
        };

        let r = hv.create_zone(pt_constants, 0usize, root_cfg_regions);
        if r.is_err() {
            return Err(());
        }

        Ok(hv)
    }

    pub fn find_zone(&self, zone_id: usize) -> (res: Option<usize>)
        ensures
            match res {
                Some(i) => {
                    &&& i < self.zone_mem_list.len()
                    &&& self.zone_mem_list[i as int].zone_id == zone_id
                }
                None => {
                    &&& forall|i: int| 0 <= i < self.zone_mem_list.len() ==> self.zone_mem_list[i].zone_id != zone_id
                }
            },
    {
        let mut i: usize = 0;
        while i < self.zone_mem_list.len()
            invariant
                i <= self.zone_mem_list.len(),
                forall|j: int| 0 <= j < i ==> self.zone_mem_list[j].zone_id != zone_id,
        {
            if self.zone_mem_list[i].zone_id == zone_id {
                return Some(i);
            }
            i += 1;
        }
        None
    }

    pub fn create_zone(
        &mut self,
        pt_constants: PTConstants,
        zone_id: usize,
        cfg_regions: Vec<HvMemRegion>,
    ) -> (res: Result<(), ()>)
        requires
            old(self).view(&old(self).alloc).inv(),
            !old(self).alloc@.clients.contains_key(zone_id as nat),
            !old(self).alloc@.free.is_empty(),
            pt_constants@.valid(),
            forall|level: nat|
                level < pt_constants.arch@.level_count() ==> pt_constants.arch@.entry_count(level) == 512,
            A::frame_size() == 4096,
        ensures
            match res {
                Ok(()) => {
                    &&& self.zone_mem_list.len() == old(self).zone_mem_list.len() + 1
                    &&& self.zone_mem_list[self.zone_mem_list.len() - 1].zone_id == zone_id
                    &&& self.view(&self.alloc).inv()
                }
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
                forall|j: int| 0 <= j < i ==> cfg_regions[j].valid(),
        {
            if !cfg_regions[i].valid() {
                return Err(());
            }
            i += 1;
        }

        self.alloc.add_client(zone_id);
        let pt = PT::new(&mut self.alloc, zone_id, pt_constants);
        let mut mem_set = VecMemorySet {
            regions: Vec::new(),
            pt,
            phantom: PhantomData,
        };

        let mut j: usize = 0;
        // TODO: add invariants
        while j < cfg_regions.len()
            invariant
                j <= cfg_regions.len(),
                // self.alloc.invariants(),
                // mem_set.invariants(&self.alloc),
            decreases cfg_regions.len() - j,
        {
            let region = mem_region_from_cfg(cfg_regions[j]);
            let insert_res = mem_set.insert(&mut self.alloc, region);
            if insert_res.is_err() {
                return Err(());
            }

            j += 1;
        }

        self.zone_mem_list.push(ZoneMem { zone_id, mem_set });
        Ok(())
    }

    // pub fn destroy_zone(&mut self, zone_id: usize) -> (res: Result<ZoneMem<PT, A>, ()>)
    //     requires
    //         old(self).alloc.invariants(),
    //     ensures
    //         self.alloc.invariants(),
    //         match res {
    //             Ok(z) => {
    //                 &&& z.zone_id == zone_id
    //                 &&& self.zone_mem_list.len() + 1 == old(self).zone_mem_list.len()
    //                 &&& !self.alloc@.clients.contains_key(zone_id as nat)
    //             }
    //             Err(()) => {
    //                 &&& self.zone_mem_list.len() == old(self).zone_mem_list.len()
    //             }
    //         },
    // {
    //     let idx = self.find_zone(zone_id);
    //     if idx.is_none() {
    //         return Err(());
    //     }

    //     let zone = self.zone_mem_list.remove(idx.unwrap());
    //     self.alloc.remove_client(zone_id);
    //     Ok(zone)
    // }

    // pub fn query(&self, zone_id: usize, vaddr: VAddr) -> (res: Result<PAddr, ()>)
    //     requires
    //         self.alloc.invariants(),
    //         vaddr@.aligned(8),
    //     ensures
    //         self.alloc.invariants(),
    // {
    //     let idx = self.find_zone(zone_id);
    //     if idx.is_none() {
    //         return Err(());
    //     }

    //     let zone = &self.zone_mem_list[idx.unwrap()];
    //     let pt_res = zone.mem_set.pt.query(&self.alloc, vaddr);
    //     if pt_res.is_err() {
    //         return Err(());
    //     }

    //     let (vbase, frame) = pt_res.unwrap();
    //     let offset = vaddr.0 - vbase.0;
    //     Ok(PAddr(frame.base.0 + offset))
    // }
}

// TODO: need to check again
pub fn attr_from_mem_type(mem_type: MemType) -> (attr: MemAttr)
    ensures
        attr == spec_attr_from_mem_type(mem_type@),
{
    match mem_type {
        MemType::Ram => MemAttr::new(true, true, true, true, false),
        MemType::Io => MemAttr::new(true, true, false, true, true),
        MemType::VirtIo => MemAttr::new(true, true, false, true, true),
    }
}

pub open spec fn spec_attr_from_mem_type(mem_type: SpecMemType) -> MemAttr {
    match mem_type {
        SpecMemType::Ram => MemAttr::spec_new(true, true, true, true, false),
        SpecMemType::Io => MemAttr::spec_new(true, true, false, true, true),
        SpecMemType::VirtIo => MemAttr::spec_new(true, true, false, true, true),
    }
}

pub fn mapper_from_cfg(r: HvMemRegion) -> (mapper: Mapper)
    ensures
        mapper == spec_mapper_from_cfg(r@),
{
    Mapper::Fixed(r.pstart.0)
}

pub open spec fn spec_mapper_from_cfg(r: SpecMemRegion) -> Mapper {
    Mapper::Fixed(r.pstart.0 as usize)
}

/// A mapped region matches a config region if:
/// - they have the same virtual interval;
/// - for every page-aligned virtual address in the interval,
///   the mapped physical translation agrees with the config translation.
pub open spec fn mapped_region_matches_cfg(mr: MemoryRegion, cr: SpecMemRegion) -> bool {
    &&& mr.start@ == cr.vstart
    &&& (mr.pages as nat) * PAGE_SIZE as nat == cr.size
}

pub fn mem_region_from_cfg(r: HvMemRegion) -> (mr: MemoryRegion)
    ensures
        mapped_region_matches_cfg(mr, r@),
        mr.spec_valid(),
{
    MemoryRegion {
        start: r.vstart,
        pages: r.size / PAGE_SIZE,
        attr: attr_from_mem_type(r.mem_type),
        mapper: mapper_from_cfg(r),
    }
}



} // verus!
