//! Stage-2 translation state and maintenance interfaces.
//!
//! [`spec`] defines the tokenized MMU state and [`mmu`] connects that state to
//! CPU and IOMMU operations. Concrete instruction backends are supplied by
//! hypervisor integrations.

pub mod mmu;
pub mod spec;

pub use mmu::{HardwareInstr, MmuHardware, MmuInstr, SmmuInstr, ZoneIdInstr};
