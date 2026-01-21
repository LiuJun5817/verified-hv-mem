//! Page table trait with formal specification.
use vstd::prelude::*;

use crate::address::addr::{PAddr, PAddrExec, VAddr, VAddrExec};
use crate::address::frame::{Frame, FrameExec, MemAttr};
use crate::page_table::pt_arch::{SpecPTArch, PTArch};

verus! {

/// Result type returned by paging operations (map, unmap, query).
pub type PagingResult<T = ()> = Result<T, ()>;

/// Page table config constants.
pub struct SpecPTConstants {
    /// Page table architecture.
    pub arch: SpecPTArch,
    /// Physical memory lower bound.
    pub pmem_lb: PAddr,
    /// Physical memory upper bound.
    pub pmem_ub: PAddr,
}

impl SpecPTConstants {
    /// Check if valid.
    pub open spec fn valid(self) -> bool {
        &&& self.arch.valid()
        &&& self.pmem_lb.0 < self.pmem_ub.0
    }
}

/// Page table config constants (exec mode).
pub struct PTConstants {
    /// Page table architecture.
    pub arch: PTArch,
    /// Physical memory lower bound.
    pub pmem_lb: PAddrExec,
    /// Physical memory upper bound.
    pub pmem_ub: PAddrExec,
}

impl PTConstants {
    /// View as `PTConstants`
    pub open spec fn view(self) -> SpecPTConstants {
        SpecPTConstants { arch: self.arch@, pmem_lb: self.pmem_lb@, pmem_ub: self.pmem_ub@ }
    }
}

/// Abstract page table state.
pub struct PageTableState {
    /// Mappings from virtual address to physical frames.
    pub mappings: Map<VAddr, Frame>,
    /// Page table constants.
    pub constants: SpecPTConstants,
}

/// State transition specification.
impl PageTableState {
    /// Init state.
    pub open spec fn init(self) -> bool {
        &&& self.mappings === Map::empty()
        &&& self.constants.arch.valid()
    }

    /// Map preconditions.
    pub open spec fn map_pre(self, vbase: VAddr, frame: Frame) -> bool {
        // Arch should support frame size
        &&& self.constants.arch.is_valid_frame_size(
            frame.size,
        )
        // Base vaddr should align to frame size
        &&& vbase.aligned(
            frame.size.as_nat(),
        )
        // Base paddr should align to frame size
        &&& frame.base.aligned(
            frame.size.as_nat(),
        )
        // Frame should be within pmem
        &&& frame.base.0 >= self.constants.pmem_lb.0
        &&& frame.base.0 + frame.size.as_nat()
            <= self.constants.pmem_ub.0
    }

    /// State transition - map a virtual address to a physical frame.
    pub open spec fn map(
        s1: Self,
        s2: Self,
        vbase: VAddr,
        frame: Frame,
        res: PagingResult,
    ) -> bool {
        &&& s1.constants == s2.constants
        // Precondition
        &&& s1.map_pre(vbase, frame)
        // Check vmem overlapping
        &&& if s1.overlaps_vmem(vbase, frame) {
            // Mapping fails
            &&& res is Err
            // Page table should not be updated
            &&& s1.mappings === s2.mappings
        } else {
            // Mapping succeeds
            &&& res is Ok
            // Update page table
            &&& s1.mappings.insert(vbase, frame) === s2.mappings
        }
    }

    /// Unmap precondition.
    pub open spec fn unmap_pre(self, vbase: VAddr) -> bool {
        // Base vaddr should align to leaf frame size
        vbase.aligned(self.constants.arch.leaf_frame_size().as_nat())
    }

    /// State transition - unmap a virtual address.
    pub open spec fn unmap(s1: Self, s2: Self, vbase: VAddr, res: PagingResult) -> bool {
        &&& s1.constants == s2.constants
        // Precondition
        &&& s1.unmap_pre(vbase)
        // Check page table
        &&& if s1.mappings.contains_key(vbase) {
            // Unmapping succeeds
            &&& res is Ok
            // Update page table
            &&& s1.mappings.remove(vbase) === s2.mappings
        } else {
            // Unmapping fails
            &&& res is Err
            // Page table should not be updated
            &&& s1.mappings === s2.mappings
        }
    }

    /// Query precondition.
    pub open spec fn query_pre(self, vaddr: VAddr) -> bool {
        // Base vaddr should align to 8 bytes
        vaddr.aligned(8)
    }

    /// Query the physical frame mapped to a virtual address.
    pub open spec fn query(self, vaddr: VAddr, res: PagingResult<(VAddr, Frame)>) -> bool {
        // Precondition
        &&& self.query_pre(vaddr)
        // Check result
        &&& if self.has_mapping_for(vaddr) {
            // Query succeeds
            &&& res is Ok
            &&& res.unwrap() == self.mapping_for(vaddr)
        } else {
            // Query fails
            &&& res is Err
        }
    }
}

/// Helper functions.
impl PageTableState {
    /// Construct a page table state.
    pub open spec fn new(mappings: Map<VAddr, Frame>, constants: SpecPTConstants) -> Self {
        Self { mappings, constants }
    }

    /// If `frame` overlaps with existing physical memory.
    pub open spec fn overlaps_pmem(self, frame: Frame) -> bool {
        exists|frame2: Frame|
            {
                &&& #[trigger] self.mappings.contains_value(frame2)
                &&& PAddr::overlap(
                    frame2.base,
                    frame2.size.as_nat(),
                    frame.base,
                    frame.size.as_nat(),
                )
            }
    }

    /// If mapping `(vaddr, frame)` overlaps with existing virtual memory.
    pub open spec fn overlaps_vmem(self, vbase: VAddr, frame: Frame) -> bool {
        exists|vbase2: VAddr|
            {
                &&& #[trigger] self.mappings.contains_key(vbase2)
                &&& VAddr::overlap(
                    vbase2,
                    self.mappings[vbase2].size.as_nat(),
                    vbase,
                    frame.size.as_nat(),
                )
            }
    }

    /// If there exists a mapping for `vaddr`.
    pub open spec fn has_mapping_for(self, vaddr: VAddr) -> bool {
        exists|vbase: VAddr, frame: Frame|
            {
                &&& #[trigger] self.mappings.contains_pair(vbase, frame)
                &&& vaddr.within(vbase, frame.size.as_nat())
            }
    }

    /// Get the mapping for `vaddr`.
    pub open spec fn mapping_for(self, vaddr: VAddr) -> (VAddr, Frame)
        recommends
            self.has_mapping_for(vaddr),
    {
        choose|vbase: VAddr, frame: Frame|
            {
                &&& #[trigger] self.mappings.contains_pair(vbase, frame)
                &&& vaddr.within(vbase, frame.size.as_nat())
            }
    }
}

/// Specification of a Page Table viewed by higher-level components.
///
/// Concrete implementation must implement `PageTable` trait to satisfy the specification.
pub trait PageTable where Self: Sized {
    /// View as a `VAddr` to `Frame` mapping.
    spec fn view(self) -> PageTableState;

    /// Invariants that must be implied at initial state and preseved after each operation.
    spec fn invariants(self) -> bool;

    /// Create an empty page table.
    fn new(constants: PTConstants) -> (pt: Self)
        requires
            constants@.valid(),
        ensures
            pt@.constants == constants@,
            pt@.init(),
            pt.invariants(),
    ;

    /// Map a virtual address to a physical frame with given attributes.
    fn map(&mut self, vbase: VAddrExec, frame: FrameExec) -> (res: Result<(), ()>)
        requires
            old(self).invariants(),
            old(self)@.map_pre(vbase@, frame@),
        ensures
            self.invariants(),
            PageTableState::map(old(self)@, self@, vbase@, frame@, res),
    ;

    /// Unmap a virtual address.
    fn unmap(&mut self, vbase: VAddrExec) -> (res: Result<(), ()>)
        requires
            old(self).invariants(),
            old(self)@.unmap_pre(vbase@),
        ensures
            self.invariants(),
            PageTableState::unmap(old(self)@, self@, vbase@, res),
    ;

    /// Query the physical frame mapped to a virtual address.
    fn query(&self, vaddr: VAddrExec) -> (res: Result<(VAddrExec, FrameExec), ()>)
        requires
            self.invariants(),
            self@.query_pre(vaddr@),
        ensures
            self.invariants(),
            self@.query(
                vaddr@,
                match res {
                    Ok((vaddr_exec, frame_exec)) => Ok((vaddr_exec@, frame_exec@)),
                    Err(()) => Err(()),
                },
            ),
    ;
}

} // verus!
