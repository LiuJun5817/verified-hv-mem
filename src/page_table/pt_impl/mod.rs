//! Executable page table implementation. Implements the `PageTable` trait to satisfy the specification
//! required by higher-level components.
use super::{
    pt_mem::PageTableMem,
    pt_trait::{PTConstants, PageTable, PageTableState},
    pte::PageTableEntry,
};
use crate::{
    address::{
        addr::{SpecPAddr, VAddr},
        frame::Frame,
    },
    global_allocator::GlobalAllocator,
};
use vstd::prelude::*;

mod path;
mod pt;
mod spec_pt;
mod tree;

verus! {

/// Wrap `pt::PageTable` to implement `pt_trait::PageTable` trait, which is the specification
/// required by higher-level components.
pub struct ExPageTable<A, E>(pub pt::PageTable<A, E>) where A: GlobalAllocator, E: PageTableEntry;

impl<A, E> PageTable<A> for ExPageTable<A, E> where A: GlobalAllocator, E: PageTableEntry {
    open spec fn view(&self, allocator: &A) -> PageTableState {
        self.0.view(allocator).view().view()
    }

    open spec fn invariants(&self, allocator: &A) -> bool {
        self.0.invariants(allocator)
    }

    fn new(allocator: &mut A, cid: usize, constants: PTConstants) -> (pt: Self) {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        let pt = pt::PageTable::<A, E>::new(allocator, cid, constants);
        proof {
            pt.view(allocator).construct_node_facts(pt.view(allocator).pt_mem.root, 0);
            assert(pt.view(allocator).view().view().mappings === Map::empty());
        }
        ExPageTable(pt)
    }

    fn map(&mut self, allocator: &mut A, vbase: VAddr, frame: Frame) -> (res: Result<(), ()>) {
        proof {
            self.0.view(allocator).lemma_wf_implies_node_wf();
            self.0.view(allocator).construct_node_facts(self.0.view(allocator).pt_mem.root, 0);
            self.0.view(allocator).view().map_refinement(vbase@, frame@);
        }
        self.0.map(allocator, vbase, frame)
    }

    fn unmap(&mut self, allocator: &mut A, vbase: VAddr) -> (res: Result<(), ()>) {
        proof {
            self.0.view(allocator).lemma_wf_implies_node_wf();
            self.0.view(allocator).construct_node_facts(self.0.view(allocator).pt_mem.root, 0);
            self.0.view(allocator).view().unmap_refinement(vbase@);
        }
        self.0.unmap(allocator, vbase)
    }

    fn query(&self, allocator: &A, vaddr: VAddr) -> (res: Result<(VAddr, Frame), ()>) {
        proof {
            self.0.view(allocator).lemma_wf_implies_node_wf();
            self.0.view(allocator).construct_node_facts(self.0.view(allocator).pt_mem.root, 0);
            self.0.view(allocator).view().query_refinement(vaddr@);
        }
        self.0.query(allocator, vaddr)
    }
}

} // verus!
