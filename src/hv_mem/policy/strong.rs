//! Assumption-2 (strong) per-zone budget evidence (placeholder).
//!
//! Under assumption 2, each zone is pre-allocated a static budget of regions at boot time.
//! The budget is modeled by an external uninterpreted spec function `zone_budget(zid)`
//! plus trusted axioms (budget validity and cross-zone disjointness). Because no global
//! mutable closure token is needed, `insert_region` can remain zone-local and does not
//! require the global `HvMem` write lock.
//!
//! # TODO
//! - Define `BudgetEvidence` (if still needed by policy layer) as a lightweight wrapper
//!   around proof obligations derived from `zone_budget(zid)`.
use vstd::prelude::*;

verus! {
    // TODO: ZoneBudget, BudgetEvidence

} // verus!
