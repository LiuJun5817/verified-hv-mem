//! The hardware side: the MMU tokenized state machine ([`spec::MmuSpec`]) together
//! with its concrete exec implementation ([`mmu::MmuHardware`]) and the trusted
//! instruction seam ([`mmu::HardwareInstr`]).  The symmetric counterpart of
//! [`crate::hv_mem`] (which holds `BudgetSpec` + `HvMem`).  The abstract
//! `HardwareView` model and the `MmuSpec`→`HardwareView` refinement live elsewhere
//! ([`crate::machine::hardware`], [`crate::refinement`]).
pub mod aarch64;
pub mod mmu;
pub mod spec;

pub use aarch64::Aarch64Hw;
pub use mmu::{HardwareInstr, MmuHardware};
