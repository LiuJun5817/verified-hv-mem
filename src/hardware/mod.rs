//! Stage-2 translation state and maintenance interfaces.
//!
//! [`spec`] defines the tokenized MMU state, [`mmu`] connects that state to CPU
//! and IOMMU operations, and [`aarch64`] implements the platform interface.

#[cfg(target_arch = "aarch64")]
pub mod aarch64;
pub mod mmu;
pub mod spec;

#[cfg(target_arch = "aarch64")]
pub use aarch64::Aarch64Hw;
pub use mmu::{HardwareInstr, MmuHardware, MmuInstr, SmmuInstr, ZoneIdInstr};
