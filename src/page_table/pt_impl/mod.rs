//! Executable page table implementation. Implements the `PageTable` trait to satisfy the specification
//! required by higher-level components.
use super::{
    pt_trait::{PTConstants, PageTable, PageTableState},
    pte::PageTableEntry,
};
use crate::{
    address::{addr::VAddr, frame::Frame},
    bitmap_allocator::bitmap_trait::BitmapAllocator,
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
pub struct ExPageTable<A, E>(pub pt::PageTable<A, E>) where A: BitmapAllocator, E: PageTableEntry;

impl<A, E> PageTable<A> for ExPageTable<A, E> where A: BitmapAllocator, E: PageTableEntry {
    open spec fn view(&self) -> PageTableState {
        self.0.view().view().view()
    }

    open spec fn invariants(&self) -> bool {
        self.0.invariants()
    }

    open spec fn inst_id(&self) -> InstanceId {
        self.0.inst_id()
    }

    fn new(allocator: &GlobalAllocator<A>, constants: PTConstants) -> (pt: Self) {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        let pt = pt::PageTable::<A, E>::new(allocator, constants);
        proof {
            pt.view().construct_node_facts(pt.view().pt_mem.root, 0);
            assert(pt.view().view().view().mappings === Map::empty());
        }
        ExPageTable(pt)
    }

    fn drop(self, allocator: &GlobalAllocator<A>) {
        self.0.drop(allocator)
    }

    fn map(&mut self, allocator: &GlobalAllocator<A>, vbase: VAddr, frame: Frame) -> (res: Result<
        (),
        (),
    >) {
        proof {
            let view = self.0.view();
            view.lemma_wf_implies_node_wf();
            view.construct_node_facts(view.pt_mem.root, 0);
            view.lemma_all_nonempty_above_root_implies();
            if view.is_table_empty(view.pt_mem.root) {
                view.lemma_empty_implies_node_empty();
            } else {
                view.lemma_all_nonempty_implies_node_all_nonempty();
            }
            view.view().map_refinement(vbase@, frame@);
        }
        self.0.map(allocator, vbase, frame)
    }

    fn unmap(&mut self, allocator: &GlobalAllocator<A>, vbase: VAddr) -> (res: Result<(), ()>) {
        proof {
            let view = self.0.view();
            view.lemma_wf_implies_node_wf();
            view.construct_node_facts(view.pt_mem.root, 0);
            view.lemma_all_nonempty_above_root_implies();
            if view.is_table_empty(view.pt_mem.root) {
                view.lemma_empty_implies_node_empty();
            } else {
                view.lemma_all_nonempty_implies_node_all_nonempty();
            }
            view.view().unmap_refinement(vbase@);
        }
        self.0.unmap(allocator, vbase)
    }

    fn query(&self, vaddr: VAddr) -> (res: Result<(VAddr, Frame), ()>) {
        proof {
            let view = self.0.view();
            view.lemma_wf_implies_node_wf();
            view.construct_node_facts(view.pt_mem.root, 0);
            view.lemma_all_nonempty_above_root_implies();
            if view.is_table_empty(view.pt_mem.root) {
                view.lemma_empty_implies_node_empty();
            } else {
                view.lemma_all_nonempty_implies_node_all_nonempty();
            }
            view.view().query_refinement(vaddr@);
        }
        self.0.query(vaddr)
    }

    proof fn lemma_invariants_implies_wf(&self) {
        let view = self.0.view();
        view.lemma_wf_implies_node_wf();
        view.construct_node_facts(view.pt_mem.root, 0);
        view.lemma_all_nonempty_above_root_implies();
        if view.is_table_empty(view.pt_mem.root) {
            view.lemma_empty_implies_node_empty();
        } else {
            view.lemma_all_nonempty_implies_node_all_nonempty();
        }
        assert(view.view().wf());
        view.view().lemma_mappings_nonoverlap_in_vmem();
        view.view().lemma_mappings_valid();
    }
}

} // verus!
