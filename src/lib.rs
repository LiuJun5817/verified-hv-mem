// #![verifier::deprecated_postcondition_mut_ref_style(true)]
#![no_std]
use core::panic;
use vstd::prelude::*;

pub mod address;
pub mod bitmap_allocator;
pub mod global_allocator;
pub mod hardware;
pub mod hv_mem;
pub mod memory_set;
pub mod model;
pub mod page_table;
pub mod refinement;
pub mod sync;

verus! {

global layout usize is size == 8;

} // verus!
fn main() {}
