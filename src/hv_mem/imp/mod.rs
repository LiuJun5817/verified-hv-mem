//! Executable `HvMem` implementation layers.
//!
//! - [`zone`]: protocol-generic per-zone definitions and operations.
//! - [`mem`]: protocol-generic global memory-manager definitions and operations.
//! - [`budget`]: executable operations specialized for `BudgetProtocol`.
//! - [`hyperenclave`]: executable operations specialized for `HyperEnclaveProtocol`.
pub mod budget;
pub mod hyperenclave;
pub mod mem;
pub mod zone;

pub use mem::*;
pub use zone::*;
