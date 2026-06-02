pub mod types;

// ---------------------------------------------------------------------------
// New three-layer architecture
// ---------------------------------------------------------------------------

/// Software state machine — `SwView`, SW transitions, `SoftwareOps` trait.
pub mod software;

/// Hardware state machine — `HwView`, HW transitions, `HardwareOps` trait.
pub mod hardware;

/// High-level abstract machine — `MachineState`, combined steps, security
/// lemmas, and refinement proofs.
pub mod machine;

// ---------------------------------------------------------------------------
// Flat re-exports for convenience
// ---------------------------------------------------------------------------

pub use hardware::{HardwareOps, HwView};
pub use machine::MachineState;
pub use software::{SoftwareOps, SwView};
pub use types::*;
