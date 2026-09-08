//! The **refinement layer**: connects each tokenized state machine to its abstract
//! model, and the two models to the combined machine state.  The models live in
//! [`crate::model`]; the state machines and their exec impls in [`crate::hardware`]
//! (`MmuSpec`/`MmuHardware`) and [`crate::hv_mem`] (`BudgetSpec`/`HvMem`).
//!
//! ```text
//!         software                              hardware
//!   SoftwareRefinement   (software/)      HardwareRefinement   (hardware.rs)
//!     impl for SoftwareSpec                 impl for HardwareSpec
//!      (BudgetSpec::State)               (MmuSpec::State, MmuSpec::State)
//!         │ view                                 │ view
//!     SoftwareView ◄──────── sync ──────────► HardwareView
//!         └────────────► MachineState ◄──────────┘   (machine.rs)
//! ```
//!
//! Each `*Refinement` is a **ghost contract**. Software policies expose their
//! projection through `SoftwareRefinement::view`, independently of Verus's `View`
//! trait; `invariants()` is the policy TSM's inductively maintained invariant.
//! Thus every reachable policy state projects to a well-formed software view.
//! # Module layout
//!
//! All refinement proofs, one per layer/side:
//!
//! | module       | role                                                                 |
//! |--------------|----------------------------------------------------------------------|
//! | [`software`] | common software helpers plus policy-specific BudgetSpec/HyperEnclave refinements |
//! | [`hardware`] | `HardwareSpec` projection + `HardwareRefinement` contract/impl        |
//! | [`sync`]     | concrete BudgetSpec/MMU token synchronization bridge                   |
//! | [`machine`]  | view-only `(SoftwareView, HardwareView)` → `MachineState`              |
pub mod hardware;
pub mod machine;
pub mod software;
pub mod sync;
