//! Hypervisor memory-management interface.
//!
//! Protocol specifications and tracked-token wrappers are kept separate from
//! executable implementations. Generic executable code lives under [`imp`],
//! while policy-specific methods live in modules such as [`imp::budget`].
pub mod imp;
pub mod protocol;
pub mod spec;

pub use imp::mem::*;
pub use imp::zone::*;
