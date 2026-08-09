//! Constants shared across VeriHyMem's executable and specification layers.
use vstd::prelude::*;

verus! {

/// Page size in bytes (4 KiB).
pub const PAGE_SIZE: usize = 0x1000;

/// Page size in specification mode.
pub spec const SPEC_PAGE_SIZE: nat = 0x1000;

/// Exclusive upper bound of physical addresses in the scoped 48-bit AArch64 format.
pub const PADDR_UPPER_BOUND: usize = 0x1_0000_0000_0000;

/// Frame size used by the global allocator (4 KiB).
pub const FRAME_SIZE: usize = 4096;

/// Frame size used by the global allocator in specification mode.
pub spec const SPEC_FRAME_SIZE: nat = 4096;

/// Page-table entry size in bytes.
pub spec const PTE_SIZE: nat = 8;

/// Page granularity of the abstract machine model, measured in data words.
pub spec const PAGE_WORDS: nat = 512;

} // verus!
