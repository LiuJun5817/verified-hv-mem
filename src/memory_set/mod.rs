//! A memory set is a collection of memory areas that can be mapped into the virtual address
//! space of a zone (process). It manages the page table for the zone, and provides methods to
//! insert, remove, and find memory areas.
use crate::{
    address::{
        addr::VAddr,
        frame::{Frame, FrameSize, MemoryRegion, PAGE_SIZE},
    },
    frame_allocator::frame_trait::FrameAllocator,
    global_allocator::GlobalAllocator,
    page_table::PageTable,
};
use std::marker::PhantomData;
use vstd::{invariant, prelude::*};

verus! {

/// Specification of a memory set viewed by higher-level components.
pub trait MemorySet<P, A> where P: PageTable<A>, A: GlobalAllocator {
    /// View the memory set as a list of memory regions.
    spec fn view(&self, allocator: &A) -> Seq<MemoryRegion>;

    /// Invariants that must be implied at initial state and preseved after each operation.
    spec fn invariants(&self, allocator: &A) -> bool;

    /// Insert a new memory region into the memory set.
    fn insert(&mut self, allocator: &mut A, region: MemoryRegion) -> (res: Result<(), ()>)
        requires
            old(self).invariants(old(allocator)),
            region.spec_valid(),
        ensures
            if exists|i: int|
                0 <= i < old(self).view(old(allocator)).len() && #[trigger] old(self).view(
                    old(allocator),
                )[i].spec_overlaps(region) {
                &&& res is Err
                &&& self.view(allocator) == old(self).view(old(allocator))
            } else {
                &&& res is Ok
                &&& self.view(allocator) == old(self).view(old(allocator)).push(region)
                &&& self.invariants(old(allocator))
            },
    ;

    /// Remove a memory region from the memory set by its starting virtual address.
    fn remove(&mut self, allocator: &mut A, start: VAddr) -> (res: Result<(), ()>)
        requires
            old(self).invariants(old(allocator)),
        ensures
            if exists|i: int|
                0 <= i < old(self).view(old(allocator)).len() && #[trigger] old(self).view(
                    old(allocator),
                )[i].start@ == start@ {
                let i = choose|i: int|
                    0 <= i < old(self).view(old(allocator)).len() && #[trigger] old(self).view(
                        old(allocator),
                    )[i].start@ == start@;
                &&& res is Ok
                &&& self.view(allocator) == old(self).view(old(allocator)).remove(i)
                &&& self.invariants(old(allocator))
            } else {
                &&& res is Err
                &&& self.view(allocator) == old(self).view(old(allocator))
            },
    ;
}

// /// Memory set implementation using a vector of memory regions.
// pub struct VecMemorySet<P, A> where P: PageTable<A>, A: FrameAllocator {
//     /// The list of memory regions in the memory set.
//     pub regions: Vec<MemoryRegion>,
//     /// Page table managing the mappings.
//     pub pt: P,
//     /// Phantom data for the page table memory type.
//     pub phantom: PhantomData<A>,
// }
// impl<P, A> VecMemorySet<P, A> where P: PageTable<A>, A: FrameAllocator {
//     /// If a region is mapped in the page table.
//     pub open spec fn has_mapping_for(self, allocator: &GlobalFrameAllocator<A>, region: MemoryRegion) -> bool {
//         forall|page_idx: nat|
//             page_idx < region.pages ==> #[trigger] self.pt.view(allocator).has_mapping_for(
//                 region.start@.offset(page_idx * PAGE_SIZE as nat),
//             )
//     }
//     /// Spec-mode overlap check.
//     pub open spec fn spec_overlaps(self, region: MemoryRegion) -> bool {
//         exists|i: int|
//             0 <= i < self.regions.len() && #[trigger] self.regions[i].spec_overlaps(region)
//     }
//     /// Check if a region overlaps with any existing region.
//     pub fn overlaps(&self, allocator: &GlobalFrameAllocator<A>, region: &MemoryRegion) -> (res:
//         bool)
//         requires
//             self.invariants(allocator),
//             region.spec_valid(),
//         ensures
//             res == self.spec_overlaps(*region),
//     {
//         for i in 0..self.regions.len()
//             invariant
//                 0 <= i <= self.regions.len(),
//                 region.spec_valid(),
//                 self.invariants(allocator),
//                 forall|j: int| #![auto] 0 <= j < i ==> !self.regions[j].spec_overlaps(*region),
//         {
//             let r = &self.regions[i];
//             if r.overlaps(region) {
//                 return true;
//             }
//         }
//         false
//     }
//     /// Lemma: overlaps in `vec` implies overlaps in spec view.
//     proof fn lemma_overlaps_equiv(self, allocator: &GlobalFrameAllocator<A>, region: MemoryRegion)
//         requires
//             self.invariants(allocator),
//             region.spec_valid(),
//         ensures
//             self.spec_overlaps(allocator, region) == exists|i: int|
//                 0 <= i < self.view(allocator).len() && #[trigger] self.view(
//                     allocator,
//                 )[i].spec_overlaps(region),
//     {
//         if self.spec_overlaps(allocator, region) {
//             let i = choose|i: int|
//                 {
//                     &&& 0 <= i < self.regions.len()
//                     &&& #[trigger] self.regions[i].spec_overlaps(region)
//                 };
//             assert(self.view(allocator)[i] == self.regions[i]);
//         }
//     }
// }
// impl<P, A> MemorySet<P, A> for VecMemorySet<P, A> where
//     P: PageTable<A>,
//     A: FrameAllocator,
//  {
//     open spec fn view(&self, allocator: &GlobalFrameAllocator<A>) -> Seq<MemoryRegion> {
//         Seq::new(self.regions.len() as nat, |i| self.regions[i])
//     }
//     open spec fn pt(&self, allocator: &GlobalFrameAllocator<A>) -> P {
//         self.pt
//     }
//     open spec fn invariants(&self, allocator: &GlobalFrameAllocator<A>) -> bool {
//         &&& self.pt.view(allocator).constants.valid()
//         // Frame size is 4K
//         &&& self.pt.view(allocator).constants.arch.leaf_frame_size()
//             == FrameSize::Size4K
//         // Page table invariants
//         &&& self.pt.invariants(allocator)
//         // Regions are valid
//         &&& forall|i: int|
//             0 <= i < self.regions.len()
//                 ==> #[trigger] self.regions[i].spec_valid()
//         // Regions do not overlap
//         &&& forall|i: int, j: int|
//             0 <= i < self.regions.len() && 0 <= j < self.regions.len() && i != j
//                 ==> !self.regions[i].spec_overlaps(
//                 self.regions[j],
//             )
//             // All regions are mapped in the page table
//         &&& forall|i: int|
//             0 <= i < self.regions.len() ==> #[trigger] self.has_mapping_for(self.regions[i])
//     }
//     fn insert(&mut self, allocator: &mut GlobalFrameAllocator<A>,region: MemoryRegion) -> (res: Result<(), ()>) {
//         proof {
//             self.lemma_overlaps_equiv(allocator, region);
//         }
//         if self.overlaps(allocator, &region) {
//             return Err(());
//         }
//         // Map the region in the page table
//         for i in 0..region.pages
//             invariant
//                 region.spec_valid(),
//                 self.pt.invariants(allocator),
//                 self.pt.view(allocator).constants == old(self).pt.view(allocator).constants,
//                 self.pt.view(allocator).constants.valid(),
//                 self.pt.view(allocator).constants.arch.leaf_frame_size() == FrameSize::Size4K,
//                 self.view(allocator) == old(self).view(old(allocator)),
//         {
//             let vaddr = VAddr(region.start.0 + i * PAGE_SIZE);
//             let paddr = region.mapper.map(vaddr);
//             // TODO: support huge pages
//             let frame = Frame { base: paddr, size: FrameSize::Size4K, attr: region.attr.clone() };
//             assert(self.pt.view(allocator).map_pre(vaddr@, frame@));
//             self.pt.map(allocator, vaddr, frame);
//         }
//         // Push the region into the list
//         self.regions.push(region);
//         proof {
//             assert(self@ == old(self)@.push(region));
//             // All regions are still valid
//             assert forall|i: int|
//                 0 <= i < self.regions.len() implies #[trigger] self.regions[i].spec_valid() by {
//                 if i < self.regions.len() - 1 {
//                     assert(self.regions[i] == old(self)@[i]);
//                 } else {
//                     assert(self.regions[i] == region);
//                 }
//             };
//             // All regions are still non-overlapping
//             assert forall|i: int, j: int|
//                 0 <= i < self.regions.len() && 0 <= j < self.regions.len() && i
//                     != j implies !self.regions[i].spec_overlaps(self.regions[j]) by {
//                 self.regions[i].lemma_overlaps_symmetric(self.regions[j]);
//                 if i != self.regions.len() - 1 && j != self.regions.len() - 1 {
//                     // Old regions
//                     assert(!self.regions[i].spec_overlaps(self.regions[j])) by {
//                         assert(!old(self)@[i].spec_overlaps(old(self)@[j]));
//                     };
//                 }
//             }
//             // All regions are mapped in the page table
//             assert forall|i: int|
//                 0 <= i < self.regions.len() implies #[trigger] self.has_mapping_for(
//                 self.regions[i],
//             ) by {
//                 // TODO
//                 assume(false);
//             }
//         }
//         Ok(())
//     }
//     fn remove(&mut self, start: VAddr) -> (res: Result<(), ()>) {
//         let len = self.regions.len();
//         for i in 0..len
//             invariant
//                 len == self.regions.len(),
//                 0 <= i <= self.regions.len(),
//                 self.invariants(),
//                 self.pt@.constants == old(self).pt@.constants,
//                 old(self).regions == self.regions,
//                 forall|j: int| 0 <= j < i ==> #[trigger] self.regions[j].start@ != start@,
//         {
//             let r = &self.regions[i];
//             // Find the region with the given start address
//             if r.start.0 == start.0 {
//                 assert(old(self).regions == self.regions);
//                 // Unmap the region from the page table
//                 for j in 0..r.pages
//                     invariant
//                         r.spec_valid(),
//                         self.pt.invariants(),
//                         self.pt@.constants == old(self).pt@.constants,
//                         self.pt@.constants.arch.leaf_frame_size() == FrameSize::Size4K,
//                         old(self).regions == self.regions,
//                 {
//                     let vaddr = VAddr(r.start.0 + j * PAGE_SIZE);
//                     // TODO: prove addr alignment
//                     assume(self.pt.view().unmap_pre(vaddr@));
//                     self.pt.unmap(vaddr);
//                 }
//                 // Remove the region from the list
//                 self.regions.remove(i);
//                 proof {
//                     assert(old(self)@[i as int].start@ == start@);
//                     // TODO: prove uniqueness
//                     assume(i == choose|i: int|
//                         0 <= i < old(self)@.len() && #[trigger] old(self)@[i].start@ == start@);
//                     assert(self@ == old(self)@.remove(i as int));
//                     // All regions are still valid
//                     assert(forall|j: int|
//                         0 <= j < self.regions.len() ==> #[trigger] self.regions[j].spec_valid());
//                     // All regions are still non-overlapping
//                     assert(forall|i: int, j: int|
//                         0 <= i < self.regions.len() && 0 <= j < self.regions.len() && i != j
//                             ==> !self.regions[i].spec_overlaps(self.regions[j]));
//                     // All regions are mapped in the page table
//                     assert forall|i: int|
//                         0 <= i < self.regions.len() implies #[trigger] self.has_mapping_for(
//                         self.regions[i],
//                     ) by {
//                         // TODO
//                         assume(false);
//                     }
//                 }
//                 return Ok(());
//             }
//         }
//         // Region not found
//         assert(!exists|i: int|
//             0 <= i < self.regions.len() && #[trigger] self.regions[i].start@ == start@);
//         Err(())
//     }
// }
} // verus!
