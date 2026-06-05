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
//! state (`zone_ids` + the per-zone `GhostZone` region sets). `SwView` is a spec
//! function of it (`<BudgetSpec::State as View>::view`), and the contract
//! `invariants()` is the machine's real `invariant()`.
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
//! ## Why this is connected
//!
//! - `invariants()` is `BudgetSpec::State::invariant()`.  `inv_implies_wf` proves
//!   `invariant() ⟹ self@.wf()`.  The macro guarantees `invariant()` at
//!   **every reachable state**, so every reachable state is `wf` (hence secure).
//! - `HvMem` already fires the real `BudgetSpec` transitions (via `BudgetProtocol`),
//!   so the state it drives is always a reachable `BudgetSpec::State` — the same
//!   states this projection is proven `wf` for.  No separate linearization step.
//! - The `SoftwareOps` transition methods in [`refine`] do **not** hand-build their
//!   post-states: each fires the matching macro transition via
//!   `BudgetSpec::take_step::{add_zone, remove_zone, insert_region, remove_region}`,
//!   so the post is *definitionally* the transition's post (consistency by
//!   construction) and `post.invariant()` is reused from the macro's inductiveness
//!   rather than re-proven.
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
//! # Module layout
//!
//! This is a **single** refinement layer (`BudgetSpec::State` → `SwView`); the
//! three modules below are just an organizational split of that one proof, not
//! separate refinement layers:
//!
//! | module          | role                                                          |
//! |-----------------|---------------------------------------------------------------|
//! | [`view`]        | page-unit reconciliation + the abstraction relation R: `BudgetSpec::State` → `SwView` |
//! | [`transition`]  | how the projection moves under each insert/remove transition  |
//! | [`refine`]      | `impl SoftwareOps for BudgetSpec::State` (the contract proof)  |
//!
//! # Open obligations
//!
//! This module has **no `admit()`s**.  Everything is proven: the contract methods
//! (`inv_implies_wf`, `add_vm` / `remove_vm` / `insert_region` / `remove_region`),
//! the cross-zone disjointness lemma `lemma_state_owned_pages_disjoint`, and every
//! [`transition`] delta (the `all_owned` / `s2_map` insert and remove lemmas).
//!
//! The proofs bottom out on the project's **trusted region axioms** (in
//! `hv_mem::spec::closure`, alongside `all_regions_valid` / `all_regions_disjoint`):
//! - `all_regions_pmem_linear` — every configured region is physically linear
//!   (`Offset`-mapped without address-space wrap; see `MemoryRegion::pmem_linear`
//!   and `hv_mem::config`).  This is what makes
//!   `lemma_same_phys_page_implies_pmem_overlap` — and hence every owned-page delta
//!   and the disjointness proof — go through: a shared physical page index of two
//!   page-aligned physical blocks forces their byte intervals to overlap.
//!
//! **Model-internal admits** (outside this module) are unchanged:
//! `machine::machine::refine` (×8) and `machine::machine::security` (×2).
pub mod refine;
pub mod transition;
pub mod view;
