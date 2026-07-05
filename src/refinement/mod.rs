//! The **refinement layer**: connects each tokenized state machine to its abstract
//! model, and the two models to the combined machine state.  The models live in
//! [`crate::machine`]; the state machines and their exec impls in [`crate::hardware`]
//! (`MmuSpec`/`MmuHardware`) and [`crate::hv_mem`] (`BudgetSpec`/`HvMem`).
//!
//! ```text
//!         software                              hardware
//!   SoftwareRefinement   (software.rs)    HardwareRefinement   (hardware.rs)
//!     impl for BudgetSpec::State            impl for MmuSpec::State
//!         │ view                                 │ view
//!     SoftwareView ◄──────── sync ──────────► HardwareView
//!         └────────────► MachineState ◄──────────┘   (machine.rs)
//! ```
//!
//! Each `*Refinement` is a **ghost contract**: the tokenized SM's own `State` is the
//! abstract state, the model `*View` is its `View` projection, and `invariants()` is
//! the SM's real, inductively-proven `invariant()` — so every reachable state the
//! impl drives projects to a `wf` (hence secure) view.  The contract methods fire
//! the macro transitions via `*Spec::take_step::*`.
//! # Module layout
//!
//! All refinement proofs, one per layer/side:
//!
//! | module       | role                                                                 |
//! |--------------|----------------------------------------------------------------------|
//! | [`software`] | `BudgetSpec::State` -> `SoftwareView` projection + `SoftwareRefinement` contract/impl |
//! | [`hardware`] | `HardwareRefinement` contract + `impl` for `MmuSpec::State`           |
//! | [`machine`]  | `(SoftwareView, HardwareView)` → `MachineState`, incl. the sync bridge |
pub mod hardware;
pub mod machine;
pub mod software;
