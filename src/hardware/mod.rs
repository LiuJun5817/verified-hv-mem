//! Concrete hardware instructions refining `HwView`.
//!
//! This module provides architecture-specific realizations of the
//! [`HardwareInstr`] trust contract: exec `fn`s wrapping real instructions,
//! each axiomatized to refine the matching `HwView` step.
//! The abstract side of the contract lives in [`crate::machine::hardware`].
pub mod aarch64;
pub mod mmu;

pub use aarch64::Aarch64Hw;
pub use mmu::{HardwareInstr, MmuHardware};
