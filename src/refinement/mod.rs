//! Software-refinement layer: connect the concurrent `HvMem` implementation to
//! the machine-level security contract [`crate::machine::software::SoftwareOps`].
//!
//! The implementation proof (`hv_mem`) establishes spatial properties (region
//! disjointness, zone isolation, PT-mem discipline) about a concurrent object;
//! the machine proof (`machine`) establishes information-flow security about the
//! abstract machine `SwView`.  This layer is the bridge.
//!
//! # Architecture
//!
//! The abstract state **is** the state machine's own `BudgetSpec::State`
//! (`zone_ids` + the per-zone `GhostZone` region sets).  `SwView` is a projection
//! of it (`<BudgetSpec::State as View>::view`), and the contract `invariants()`
//! is the machine's real, inductively-proven `invariant()`.
//!
//! ```text
//!   SoftwareOps              ghost contract; invariants() == BudgetSpec invariant()
//!       ▲ impl (in `refine`)
//!   BudgetSpec::State        the state machine's own state  (projected by `view`)
//!   ├─ zones:    Map<nat, GhostZone>
//!   └─ zone_ids: Set<nat>
//!       ▲ token soundness: the sharded tokens HvMem holds are tokens of a
//!         reachable BudgetSpec::State
//!   HvMem  (fires BudgetSpec transitions via BudgetProtocol, behind locks)
//! ```
//!
//! Because the contract invariant is the inductive `invariant()`, every reachable
//! state `HvMem` drives projects to a `wf` (hence secure) `SwView`.  The contract
//! methods fire the real macro transitions via `BudgetSpec::take_step::*`, so each
//! post-state — and its `invariant()` — comes from the state machine itself.
//!
//! # Operation correspondence
//!
//! | `SoftwareOps` op | `SwView` step                  |
//! |------------------|--------------------------------|
//! | `add_vm`         | [`SwView::add_vm_step`]         |
//! | `remove_vm`      | [`SwView::remove_vm_step`]      |
//! | `insert_region`  | [`SwView::insert_region_step`]  |
//! | `remove_region`  | [`SwView::remove_region_step`]  |
//!
//! Per-page `map` / `unmap` are not realizable from region-only state, so they are
//! not contract methods.  `share_page` / `unshare_page` are out of scope
//! (`shared_pages ≡ ∅`).
//!
//! # Module layout
//!
//! A single refinement layer, split across three modules for organization:
//!
//! | module          | role                                                          |
//! |-----------------|---------------------------------------------------------------|
//! | [`view`]        | the projection `BudgetSpec::State` → `SwView` and its facts    |
//! | [`transition`]  | how the projection moves under each insert/remove transition  |
//! | [`refine`]      | `impl SoftwareOps for BudgetSpec::State` (the contract proof)  |
pub mod refine;
pub mod sync;
pub mod transition;
pub mod view;
