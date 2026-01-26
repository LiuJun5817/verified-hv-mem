use vstd::prelude::*;

pub mod address;
pub mod bitmap_allocator;
pub mod frame_allocator;
pub mod memory_set;
pub mod page_table;

verus! {

global layout usize is size == 8;

} // verus!
fn main() {}
