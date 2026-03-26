//! Abstract top-level hvisor memory model and specification.
//!
//! It is intended to serve as the top-level contract for memory safety:
//!   P1 RegionDisjoint   ——  static physical partitioning (region disjointness),
//!   P2 ZoneIsolated     ——  per-zone isolation enforced by page tables,
//!   P3 PTMemDisjoint    ——  page-table-memory discipline (PT pages allocated from pool, disjoint, not mapped).
//!
//! Concrete implementations (mm.rs, page table code, allocators) should refine this model.

use vstd::prelude::*;
use crate::{
    address::{
        addr::{SpecVAddr, SpecPAddr},
        frame::{self, Frame, FrameSize, MemoryRegion, SpecFrame, PAGE_SIZE},
    },
    page_table::PageTable,
    global_allocator::{GlobalAllocator, GlobalAllocatorModel},
    memory_set::VecMemorySet,
};

verus! {

/// Memory type tags consistent with HvConfigMemoryRegion.mem_type.
pub enum SpecMemType {
    Ram,
    Io,
    VirtIo,
}

/// A pure physical region used for top-level static partitioning.
/// This is suitable for hvisor core / cpu_data / memory pool / shared.
pub struct SpecPhysRegion {
    pub start: SpecPAddr,
    pub size: nat,   // bytes
}

impl SpecPhysRegion {
    pub open spec fn end(&self) -> SpecPAddr {
        SpecPAddr(self.start.0 + self.size)
    }

    pub open spec fn disjoint(&self, other: &SpecPhysRegion) -> bool {
        self.end().0 <= other.start.0 || other.end().0 <= self.start.0
    }
}

/// A config memory region derived from HvConfigMemoryRegion.
/// It carries both virtual and physical bases.
pub struct SpecMemRegion {
    pub mem_type: SpecMemType,
    pub pstart: SpecPAddr,
    pub vstart: SpecVAddr,
    pub size: nat,         // bytes
}

impl SpecMemRegion {
    pub open spec fn vend(&self) -> SpecVAddr { SpecVAddr(self.vstart.0 + self.size) }
    pub open spec fn pend(&self) -> SpecPAddr { SpecPAddr(self.pstart.0 + self.size) }

    pub open spec fn contains_v(&self, v: SpecVAddr) -> bool {
        self.vstart.0 <= v.0 < self.vend().0
    }

    pub open spec fn contains_p(&self, p: SpecPAddr) -> bool {
        self.pstart.0 <= p.0 < self.pend().0
    }

    pub open spec fn phys_disjoint(&self, other: &SpecCfgMemRegion) -> bool {
        self.pend() <= other.pstart || other.pend() <= self.pstart
    }

    /// Intended affine translation induced by (vstart, pstart).
    pub open spec fn translate(&self, v: SpecVAddr) -> SpecPAddr
        recommends self.contains_v(v)
    {
        SpecPAddr(self.pstart.0 + (v.0 - self.vstart.0))
    }
}

/// Stage-2 translation view of one zone.
/// The key is the guest VA page base, and the value is the mapped PA page base.
pub struct SpecMemSet {
    pub view: Map<SpecVAddr, SpecPAddr>,
}

/// A spec wrapper for one zone.
pub struct SpecZone {
    pub zone_id: nat,

    /// Static configured memory regions of this zone.
    pub cfg_regions: Seq<SpecMemRegion>,
    
    /// Abstract stage-2 mapping state of this zone.
    pub mem_set: SpecMemSet,

    /// Physical frame IDs occupied by page-table memory of this zone.
    pub pt_frames: Set<nat>,
}

/// Top-level memory model for hvisor.
///
/// It aggregates all zones and the static partitions.
pub struct SpecHvMem {
    // pub core: SpecPhysRegion,
    // pub cpu_data: SpecPhysRegion,
    // pub pool: SpecPhysRegion,
    // pub shared: SpecPhysRegion,

    /// All zones in the system.
    pub zones: Seq<SpecZone>,

    /// Global allocator model.
    pub alloc: GlobalAllocatorModel,
}

impl SpecHvMem {
    /// P1: static physical partitioning (region disjointness).
    pub open spec fn p1_region_disjoint(&self) -> bool {
        // Intra-zone disjointness.
        &&& forall|z: int, i: int, j: int|
            0 <= z < self.zones.len()
            && 0 <= i < self.zones[z].cfg_regions.len()
            && 0 <= j < self.zones[z].cfg_regions.len()
            && i < j
            ==> self.zones[z].cfg_regions[i].phys_disjoint(&self.zones[z].cfg_regions[j])

        // Inter-zone disjointness.
        &&& forall|z1: int, z2: int, i: int, j: int|
            0 <= z1 < self.zones.len()
            && 0 <= z2 < self.zones.len()
            && z1 < z2
            && 0 <= i < self.zones[z1].cfg_regions.len()
            && 0 <= j < self.zones[z2].cfg_regions.len()
            ==> self.zones[z1].cfg_regions[i].phys_disjoint(&self.zones[z2].cfg_regions[j])
    }

    /// P2: zone isolation enforced by page tables.
    pub open spec fn p2_zone_isolated(&self) -> bool {
        forall|z: int, v: SpecVAddr|
            0 <= z < self.zones.len()
            && self.zones[z].mem_set.view.contains_key(v)
            ==> ({
                let p = self.zones[z].mem_set.view.index(v);

                // The mapped PA must come from some configured region,
                // and respect that region's intended translation.
                exists|r: int|
                    0 <= r < self.zones[z].cfg_regions.len()
                    && self.zones[z].cfg_regions[r].contains_v(v)
                    && self.zones[z].cfg_regions[r].contains_p(p)
                    && self.zones[z].cfg_regions[r].translate(v) == p
            })
    }

    /// P3: page-table memory discipline enforced by the global allocator.
    pub open spec fn p3_ptmem_disjoint(&self) -> bool {
        &&& forall|i: int, j: int|
            0 <= i < j < self.zones.len()
            ==> self.zones[i].pt_frames.disjoint(self.zones[j].pt_frames)

        &&& forall|zi: int|
            0 <= zi && zi < self.zones.len()
            ==> ({
                let z = self.zones[zi];
                self.alloc.clients.contains_key(z.zone_id)
                && z.pt_frames.subset_of(self.alloc.clients.index(z.zone_id))
            })
    }

    /// Full top-level memory invariant.
    pub open spec fn inv(&self) -> bool {
        &&& self.p1_region_disjoint()
        &&& self.p2_zone_isolated()
        &&& self.p3_ptmem_disjoint()
    }
}

} // verus!