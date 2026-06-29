//! The hardware side: the stage-2 tokenized state machine ([`spec::MmuSpec`]),
//! shared by **two regimes** (the CPU MMU and the SMMU/IOMMU) as two separate
//! instances, together with its concrete exec handle ([`mmu::MmuHardware`]) and the
//! trusted instruction seams — [`mmu::MmuInstr`] (CPU MMU) and [`mmu::SmmuInstr`]
//! (SMMU), combined under [`mmu::HardwareInstr`].  The symmetric counterpart of
//! [`crate::hv_mem`] (which holds `BudgetSpec` + `HvMem`).  The abstract
//! `HardwareView` model and the `MmuSpec`→`HardwareView` refinement live elsewhere
//! ([`crate::machine::hardware`], [`crate::refinement`]).
pub mod aarch64;
pub mod mmu;
pub mod spec;

pub use aarch64::Aarch64Hw;
pub use mmu::{HardwareInstr, MmuHardware, MmuInstr, SmmuInstr};
