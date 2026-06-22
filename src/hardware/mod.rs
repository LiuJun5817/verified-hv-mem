//! Concrete hardware instructions refining `HwView`.
//!
//! This module provides architecture-specific realizations of the
//! [`HardwareOps`](crate::machine::hardware::HardwareOps) trust contract: exec
//! `fn`s wrapping real instructions, each axiomatized to refine the matching
//! `HwView` step.  The abstract side of the contract lives in
//! [`crate::machine::hardware`].
pub mod aarch64;

pub use aarch64::Aarch64Hw;
