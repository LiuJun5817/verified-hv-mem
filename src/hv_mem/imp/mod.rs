//! Executable `HvMem` implementation layers.
//!
//! - [`zone`]: protocol-generic per-zone definitions and operations.
//! - [`mem`]: protocol-generic global memory-manager definitions and operations.
//! - [`budget`]: executable operations specialized for `BudgetProtocol`.
//! - [`enclave`]: executable operations specialized for `EnclaveProtocol`.
pub mod budget;
pub mod enclave;
pub mod mem;
pub mod zone;

pub use mem::*;
pub use zone::*;
