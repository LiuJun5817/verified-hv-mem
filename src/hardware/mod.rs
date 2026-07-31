//! Stage-2 translation state and maintenance interfaces.
//!
//! [`spec`] defines the tokenized MMU state, [`mmu`] connects that state to CPU
//! and IOMMU operations, and [`aarch64`] implements the platform interface.
pub mod aarch64;
pub mod mmu;
pub mod spec;

pub use aarch64::Aarch64Hw;
pub use mmu::{HardwareInstr, MmuHardware, MmuInstr, SmmuInstr, ZoneIdInstr};
