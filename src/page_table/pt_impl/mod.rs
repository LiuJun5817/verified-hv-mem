//! Executable page table implementation. Implements the `PageTable` trait to satisfy the specification
//! required by higher-level components.
use super::{
    pt_mem::PageTableMem,
    pt_trait::{PTConstants, PageTable, PageTableState},
    pte::{ExecPTE, GhostPTE},
};
use crate::address::{
    addr::{SpecPAddr, VAddr},
    frame::Frame,
};
use vstd::prelude::*;

mod path;
mod pt;
mod spec_pt;
mod tree;

verus! {

/// Wrap `pt::PageTable` to implement `pt_trait::PageTable` trait, which is the specification
/// required by higher-level components.
pub struct ExPageTable<M, G, E>(pub pt::PageTable<M, G, E>) where
    M: PageTableMem,
    G: GhostPTE,
    E: ExecPTE<G>,
;

impl<M, G, E> PageTable<M> for ExPageTable<M, G, E> where
    M: PageTableMem,
    G: GhostPTE,
    E: ExecPTE<G>,
 {
    open spec fn view(self) -> PageTableState {
        self.0.view().view().view()
    }

    open spec fn invariants(self) -> bool {
        self.0.invariants()
    }

    fn new(pt_mem: M, constants: PTConstants) -> (pt: Self) {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        proof {
            pt_mem.view().lemma_init_implies_wf();
        }
        let pt = pt::PageTable::<M, G, E>::new(pt_mem, constants);
        proof {
            pt.view().pt_mem.lemma_contains_root();
            pt.view().construct_node_facts(pt.view().pt_mem.root(), 0);

            assert forall|base: SpecPAddr, idx: nat| pt.pt_mem@.accessible(base, idx) implies {
                let pt_mem = pt.pt_mem@;
                let table = pt_mem.table(base);
                let pte = G::from_u64(pt_mem.read(base, idx));
                !pte.valid()
            } by {
                assert(base == pt_mem@.root());
                assert(pt_mem@.table_view(base) == seq![0u64; pt_mem@.arch.entry_count(0)]);
                assert(pt_mem@.read(base, idx) == 0);
            }
            assert(pt.view().view().view().mappings === Map::empty());
        }
        ExPageTable(pt)
    }

    fn map(&mut self, vbase: VAddr, frame: Frame) -> (res: Result<(), ()>) {
        proof {
            self.0.view().lemma_wf_implies_node_wf();
            self.0.view().pt_mem.lemma_contains_root();
            self.0.view().construct_node_facts(self.0.view().pt_mem.root(), 0);
            self.0.view().view().map_refinement(vbase@, frame@);
        }
        self.0.map(vbase, frame)
    }

    fn unmap(&mut self, vbase: VAddr) -> (res: Result<(), ()>) {
        proof {
            self.0.view().lemma_wf_implies_node_wf();
            self.0.view().pt_mem.lemma_contains_root();
            self.0.view().construct_node_facts(self.0.view().pt_mem.root(), 0);
            self.0.view().view().unmap_refinement(vbase@);
        }
        self.0.unmap(vbase)
    }

    fn query(&self, vaddr: VAddr) -> (res: Result<(VAddr, Frame), ()>) {
        proof {
            self.0.view().lemma_wf_implies_node_wf();
            self.0.view().pt_mem.lemma_contains_root();
            self.0.view().construct_node_facts(self.0.view().pt_mem.root(), 0);
            self.0.view().view().query_refinement(vaddr@);
        }
        self.0.query(vaddr)
    }
}

} // verus!
