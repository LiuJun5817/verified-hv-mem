//! Assumption-1 (weak) region-assignment evidence (placeholder).
//!
//! Under assumption 1, the only proof that a region is not yet assigned is the absence
//! of the region from the global `HvRegionClosureToken`.  Because this token is a
//! `#[sharding(variable)]` singleton, the inserter must hold the `HvMem` write lock.
//!
//! # TODO
//! - Define `ClosureEvidence` as a tracked struct wrapping `&mut HvMemState`
//!   (or a borrow of the relevant token) that implements `DisjointEvidence`.
use vstd::prelude::*;

verus! {
    // TODO: ClosureEvidence

} // verus!
