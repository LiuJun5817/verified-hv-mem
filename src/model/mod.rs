//! The abstract **models** (no refinement proofs — those live in
//! [`crate::refinement`]): the software view, the hardware view, and the combined
//! machine state, each with its transitions, well-formedness, and (for the machine)
//! the security lemmas.
pub mod types;

/// Geometry/conversion bridge between implementation types (`address`) and model
/// types (`types`) — the single place the two worlds meet.
pub mod convert;

/// Software model — `SoftwareView`, its transitions, and `wf`.
pub mod software;

/// Hardware model — `HardwareView`, its transitions, and `wf`.
pub mod hardware;

/// High-level abstract machine — `MachineState`, combined steps, and security lemmas.
pub mod machine;

// ---------------------------------------------------------------------------
// Flat re-exports for convenience
// ---------------------------------------------------------------------------

pub use hardware::HardwareView;
pub use machine::MachineState;
pub use software::SoftwareView;
pub use types::*;
