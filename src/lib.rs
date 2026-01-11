use vstd::prelude::*;

pub mod address;
// pub mod bitmap_allocator;
pub mod page_table;
// pub mod frame_allocator;

verus! {
    global layout usize is size == 8;
}

fn main() {}