use vstd::prelude::*;

pub mod address;
pub mod page_table;
pub mod memory_set;
pub mod bitmap_allocator;
pub mod frame_allocator;

verus! {

global layout usize is size == 8;

} // verus!
fn main() {}
