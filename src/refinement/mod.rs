//! Software-refinement layer: bridging the concurrent `HvMem` implementation to
//! the security contract [`crate::machine::software::SoftwareOps`].
//!
//! # Goal
//!
//! Connect the implementation proof (`hv_mem`, which proves *spatial* properties
//! — region disjointness P1, zone isolation P2, PT-mem discipline P3 — about a
//! **concurrent** object) to the machine-level security proof (`machine`, which
//! proves *information-flow* properties — confidentiality / integrity — about the
//! abstract machine `SwView`).
//!
//! # Chosen architecture (project from the state machine's own state)
//!
//! The abstract state **is** `BudgetSpec::State` — the state machine's logical
//! state (`zone_ids` + the per-zone `GhostZone` region sets) — not a hand-written
//! twin.  `SwView` is a spec function of it (`sw_view_of` / `<BudgetSpec::State as
//! View>::view`), and the contract `invariants()` is the machine's real
//! `invariant()`.
//!
//! ```text
//!   SoftwareOps              ghost contract; invariants() == BudgetSpec invariant()
//!       ▲ impl (in `refine`)
//!   BudgetSpec::State        the state machine's own state  (projected by `view`)
//!   ├─ zones:    Map<nat, GhostZone>
//!   └─ zone_ids: Set<nat>
//!       ▲ token soundness: the sharded BudgetGlobalState + BudgetZoneState tokens
//!         that HvMem holds are exactly tokens of a reachable BudgetSpec::State
//!   HvMem  (fires BudgetSpec transitions via BudgetProtocol, behind locks)
//! ```
//!
//! ## Why this is connected (not a twin)
//!
//! - `invariants()` is `BudgetSpec::State::invariant()`.  `inv_implies_wf` proves
//!   `invariant() ⟹ sw_view_of(self).wf()`.  The macro guarantees `invariant()` at
//!   **every reachable state**, so every reachable state is `wf` (hence secure).
//! - `HvMem` already fires the real `BudgetSpec` transitions (via `BudgetProtocol`),
//!   so the state it drives is always a reachable `BudgetSpec::State` — the same
//!   states this projection is proven `wf` for.  No separate linearization step.
//!
//! # Operation correspondence (region-bulk, ownership = inserted regions)
//!
//! | `SoftwareOps` op | `SwView` step                                            |
//! |------------------|----------------------------------------------------------|
//! | `add_vm`         | [`SwView::add_vm_step`]                                  |
//! | `remove_vm`      | [`SwView::remove_vm_step`]                               |
//! | `insert_region`  | [`SwView::insert_region_step`]  (= bulk assign + map)    |
//! | `remove_region`  | [`SwView::remove_region_step`]  (= bulk unmap + reclaim) |
//!
//! Per-page `map` / `unmap` are not realizable from region-only state, so they are
//! not contract methods; they remain only as the `SwView` step predicates that
//! *define* a region step's meaning.  `share_page` / `unshare_page` are **out of
//! scope**: `shared_pages ≡ ∅`.
//!
//! # Module layout (four layers, bottom-up)
//!
//! | module          | role                                                          |
//! |-----------------|---------------------------------------------------------------|
//! | [`geometry`]    | page-unit reconciliation: a region's pages / guest pages / s2 entries |
//! | [`view`]        | the abstraction relation R: `BudgetSpec::State` → `SwView`    |
//! | [`transition`]  | how the projection moves under each insert/remove transition  |
//! | [`refine`]      | `impl SoftwareOps for BudgetSpec::State` (the contract proof)  |
//!
//! # Open obligations
//!
//! The refinement *glue* — `inv_implies_wf`, the four transition methods, the
//! cross-zone disjointness lemma — is **proven**.  What remains are the isolated
//! analytic lemmas in [`geometry`] / [`transition`]:
//! - geometry: `lemma_same_phys_page_implies_pmem_overlap` (with the `Offset`-mapper
//!   caveat) and `lemma_ghost_zone_insert_region_wf`;
//! - the `Set`/`Map` deltas under a transition (`lemma_all_owned_*`,
//!   `lemma_*_region_owned_pages`, and the `choose`-heavy `lemma_state_s2_map_*`).
//! - **Model-internal admits** (outside this module): `machine::machine::refine`
//!   (×7) and `machine::machine::security` (×2) remain `admit()`.
pub mod geometry;
pub mod refine;
pub mod transition;
pub mod view;
