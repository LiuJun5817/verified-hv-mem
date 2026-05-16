#![verifier::deprecated_postcondition_mut_ref_style(true)]
use vstd::prelude::*;

pub mod address;
pub mod bitmap_allocator;
pub mod memory_set;
pub mod page_table;
pub mod global_allocator;
// pub mod hv_mem;
pub mod sync;

verus! {

global layout usize is size == 8;

} // verus!
fn main() {}
