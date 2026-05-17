//! Zone configuration and region-conversion utilities.
//!
//! This module provides config-side data types (`HvConfigMemRegion` and its spec view)
//! and conversion logic into `MemoryRegion`. It is consumed by `hv_mem::mod` during
//! zone creation.
use crate::address::{
    addr::{PAddr, SpecPAddr, SpecVAddr, VAddr},
    frame::MemType,
    region::{Mapper, MemoryRegion, PAGE_SIZE, SPEC_PAGE_SIZE},
};
use vstd::prelude::*;

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
