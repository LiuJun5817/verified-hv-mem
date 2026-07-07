//! Zone configuration and region-conversion utilities.
//!
//! This module provides config-side data types (`HvConfigMemRegion` and its spec view)
//! and conversion logic into `MemoryRegion`. It is consumed by `hv_mem::mod` during
//! zone creation.
use crate::address::{
    addr::{PAddr, SpecPAddr, SpecVAddr, VAddr},
    frame::MemType,
    region::{MemoryRegion, PAGE_SIZE, SPEC_PAGE_SIZE},
};
use vstd::prelude::*;

verus! {

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
    /// Spec-mode check if the config region is valid.
    pub open spec fn spec_valid(&self) -> bool {
        &&& 0 < self.size as nat <= usize::MAX as nat
        &&& self.size as nat % SPEC_PAGE_SIZE == 0
        &&& self.vstart@.aligned(SPEC_PAGE_SIZE)
        &&& self.pstart@.aligned(SPEC_PAGE_SIZE)
        &&& self.vstart.0 + self.size <= usize::MAX
        &&& self.pstart.0 + self.size <= usize::MAX
    }

    /// Check if the config region is valid.
    pub fn valid(&self) -> (res: bool)
        ensures
            res == self.spec_valid(),
    {
        self.size > 0 && self.size % PAGE_SIZE == 0 && self.vstart.0 % PAGE_SIZE == 0
            && self.pstart.0 % PAGE_SIZE == 0 && self.vstart.0 <= usize::MAX - self.size
            && self.pstart.0 <= usize::MAX - self.size
    }

    /// Construct a `MemoryRegion` from the config region.
    pub fn to_region(&self) -> (res: MemoryRegion)
        by (nonlinear_arith)
        requires
            self.spec_valid(),
        ensures
            res.spec_valid(),
            res.vstart == self.vstart,
            res.pstart == self.pstart,
            res.pages == self.size / PAGE_SIZE,
            res.attr == self.mem_type.spec_to_attr(),
    {
        MemoryRegion {
            vstart: self.vstart,
            pstart: self.pstart,
            pages: self.size / PAGE_SIZE,
            attr: self.mem_type.to_attr(),
        }
    }
}

} // verus!
