//! Region-assignment policy abstraction.
//!
//! Under assumption 1 (global `all_regions`), inserting a region into a zone requires
//! holding the global `HvMem` write lock to update the single `HvRegionClosureToken`.
//! Under assumption 2 (per-zone budgets), a per-zone budget token suffices, eliminating
//! the global lock from the `insert_region` fast path.
//!
//! The `DisjointEvidence` trait (TODO) will abstract over both assumptions so that
//! `HvMem::insert_region` can be generic in the policy.
//!
//! Submodules:
//! - [`weak`]: assumption-1 `ClosureEvidence` (placeholder).
//! - [`strong`]: assumption-2 `BudgetEvidence` + `ZoneBudgetSpec` (placeholder).
pub mod weak;
pub mod strong;
