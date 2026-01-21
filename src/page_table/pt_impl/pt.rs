//! Executable page table implementation.
use core::marker::PhantomData;
use vstd::prelude::*;

use super::{path::PTTreePath, spec_pt::SpecPageTable};
use crate::{
    address::{
        addr::{PAddrExec, VAddr, VAddrExec},
        frame::{Frame, FrameExec, FrameSize, MemAttr},
    },
    page_table::{
        pt_arch::SpecPTArch,
        pt_mem::PageTableMem,
        pt_trait::{PTConstants, PagingResult},
        pte::{ExecPTE, GhostPTE},
    },
};

verus! {

// Use page table memory related lemmas.
broadcast use crate::page_table::pt_mem::group_pt_mem_lemmas;

/// Executable page table implementation.
///
/// `PageTable` wraps a `PageTableMemExec` and a `PTConstantsExec` to provide a convenient interface for
/// manipulating the page table. Refinement proof is provided by implementing trait `PageTableInterface`
/// to ensure `PageTableMemExec` is manipulated correctly.
pub struct PageTable<M: PageTableMem, G: GhostPTE, E: ExecPTE<G>> {
    /// Page table memory.
    pub pt_mem: M,
    /// Page table config constants.
    pub constants: PTConstants,
    /// Phantom data.
    pub _phantom: PhantomData<(G, E)>,
}

impl<M, G, E> PageTable<M, G, E> where M: PageTableMem, G: GhostPTE, E: ExecPTE<G> {
    /// View as a specification-level page table.
    pub open spec fn view(self) -> SpecPageTable<G> {
        SpecPageTable { pt_mem: self.pt_mem@, constants: self.constants@, _phantom: PhantomData }
    }

    /// Page table architecture specification.
    pub open spec fn arch(self) -> SpecPTArch {
        self.constants.arch@
    }

    /// Construct a new page table.
    pub fn new(pt_mem: M, constants: PTConstants) -> (res: Self)
        requires
            SpecPageTable::<G>::new(pt_mem@, constants@).invariants(),
            pt_mem@.arch == constants.arch@,
        ensures
            res@.invariants(),
            res.pt_mem == pt_mem,
            res.constants == constants,
    {
        Self { pt_mem, constants, _phantom: PhantomData }
    }

    /// If all pte in a table are invalid.
    pub fn is_table_empty(&self, base: PAddrExec, level: usize) -> (res: bool)
        requires
            self@.invariants(),
            self@.pt_mem.contains_table(base@),
            self@.pt_mem.table(base@).level == level,
        ensures
            self@.is_table_empty(base@) == res,
    {
        let entry_count = self.constants.arch.entry_count(level);
        for i in 0..entry_count
            invariant
                self@.invariants(),
                self.constants.arch@.entry_count(level as nat) == entry_count,
                self@.pt_mem.contains_table(base@),
                self@.pt_mem.table(base@).level == level,
                forall|j: nat| #![auto] j < i ==> !G::from_u64(self@.pt_mem.read(base@, j)).valid(),
        {
            assert(self@.pt_mem.accessible(base@, i as nat));
            let pte = E::from_u64(self.pt_mem.read(base, i));
            if pte.valid() {
                return false;
            }
        }
        true
    }

    /// Traverse the page table for the given virtual address and return the matching
    /// entry and level. Proven consistent with the specification-level walk.
    pub fn walk(&self, vaddr: VAddrExec, base: PAddrExec, level: usize) -> (res: (E, usize))
        requires
            self@.invariants(),
            self.pt_mem@.contains_table(base@),
            self.pt_mem@.table(base@).level == level,
        ensures
            (res.0@, res.1 as nat) == self@.walk(vaddr@, base@, level as nat),
        decreases self.constants.arch@.level_count() - level as nat,
    {
        let idx = self.constants.arch.pte_index(vaddr, level);
        assert(self.pt_mem@.accessible(base@, idx as nat));
        let pte = E::from_u64(self.pt_mem.read(base, idx));
        if level < self.constants.arch.level_count() - 1 && pte.valid() && !pte.huge() {
            self.walk(vaddr, pte.addr(), level + 1)
        } else {
            (pte, level)
        }
    }

    /// Insert a page table entry into the page table, creates intermediate tables if necessary.
    ///
    /// `target_level` is the level at which the entry should be inserted.
    /// `new_pte` is the entry to be inserted.
    pub fn insert(
        &mut self,
        vbase: VAddrExec,
        base: PAddrExec,
        level: usize,
        target_level: usize,
        new_pte: E,
    ) -> (res: PagingResult)
        requires
            old(self)@.invariants(),
            level <= target_level < old(self).arch().level_count(),
            old(self).pt_mem@.contains_table(base@),
            old(self).pt_mem@.table(base@).level == level,
            old(self)@.pte_valid_frame(new_pte@, target_level as nat),
        ensures
            (self@, res) == old(self)@.insert(
                vbase@,
                base@,
                level as nat,
                target_level as nat,
                new_pte@,
            ),
            res is Err ==> old(self)@ == self@,
        decreases old(self).arch().level_count() - level as nat,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        assert(self.pt_mem@.accessible(base@, idx as nat));
        let pte = E::from_u64(self.pt_mem.read(base, idx));
        if level >= target_level {
            // Insert at current level
            if pte.valid() {
                PagingResult::Err(())
            } else {
                self.pt_mem.write(base, idx, new_pte.to_u64());
                PagingResult::Ok(())
            }
        } else {
            if pte.valid() {
                if pte.huge() {
                    PagingResult::Err(())
                } else {
                    // Insert at next level
                    self.insert(vbase, pte.addr(), level + 1, target_level, new_pte)
                }
            } else {
                proof {
                    self@.lemma_alloc_intermediate_table_preserves_invariants(
                        base@,
                        level as nat,
                        idx as nat,
                    );
                    // Lemma ensures this branch returns Ok
                    self@.lemma_insert_intermediate_node_results_ok(
                        vbase@,
                        base@,
                        level as nat,
                        target_level as nat,
                        new_pte@,
                    );
                }
                // Allocate intermediate table
                let (table_base, _) = self.pt_mem.alloc_table(level + 1);
                proof {
                    // TODO: prove alignment
                    assume(table_base@.aligned(FrameSize::Size4K.as_nat()));
                }
                // Write entry
                let pte = E::new(table_base, MemAttr::default(), false);
                self.pt_mem.write(base, idx, pte.to_u64());

                // Insert at next level
                self.insert(vbase, table_base, level + 1, target_level, new_pte)
            }
        }
    }

    /// Recursively remove a page table entry.
    pub fn remove(&mut self, vbase: VAddrExec, base: PAddrExec, level: usize) -> (res: PagingResult)
        requires
            old(self)@.invariants(),
            level < old(self).arch().level_count(),
            old(self).pt_mem@.contains_table(base@),
            old(self).pt_mem@.table(base@).level == level,
        ensures
            (self@, res) == old(self)@.remove(vbase@, base@, level as nat),
            res is Err ==> old(self)@ == self@,
        decreases old(self).arch().level_count() - level as nat,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        assert(self.pt_mem@.accessible(base@, idx as nat));
        let pte = E::from_u64(self.pt_mem.read(base, idx));
        if pte.valid() {
            if level >= self.constants.arch.level_count() - 1 {
                // Leaf node
                if vbase.aligned(self.constants.arch.frame_size(level).as_usize()) {
                    self.pt_mem.write(base, idx, E::empty().to_u64());
                    PagingResult::Ok(())
                } else {
                    PagingResult::Err(())
                }
            } else {
                // Intermediate node
                if pte.huge() {
                    if vbase.aligned(self.constants.arch.frame_size(level).as_usize()) {
                        self.pt_mem.write(base, idx, E::empty().to_u64());
                        PagingResult::Ok(())
                    } else {
                        PagingResult::Err(())
                    }
                } else {
                    self.remove(vbase, pte.addr(), level + 1)
                }
            }
        } else {
            PagingResult::Err(())
        }
    }

    /// Recursively deallocate empty tables along `vaddr` from `base`.
    pub fn prune(&mut self, vaddr: VAddrExec, base: PAddrExec, level: usize)
        requires
            old(self)@.invariants(),
            level < old(self).arch().level_count(),
            old(self).pt_mem@.contains_table(base@),
            old(self).pt_mem@.table(base@).level == level,
        ensures
            self@ == old(self)@.prune(vaddr@, base@, level as nat),
        decreases old(self).arch().level_count() - level as nat,
    {
        let idx = self.constants.arch.pte_index(vaddr, level);
        assert(self.pt_mem@.accessible(base@, idx as nat));
        let pte = E::from_u64(self.pt_mem.read(base, idx));
        if level < self.constants.arch.level_count() - 1 && pte.valid() && !pte.huge() {
            // Prune from subtable
            proof {
                // Invariants satisfied after recycling from subtable
                self.view().lemma_prune_preserves_invariants(vaddr@, pte@.addr(), level as nat + 1);
                // Current table and subtable are accessible after recycling from subtable
                self.view().lemma_prune_preserves_lower_tables(
                    vaddr@,
                    pte@.addr(),
                    level as nat + 1,
                    base@,
                );
                self.view().lemma_prune_preserves_lower_tables(
                    vaddr@,
                    pte@.addr(),
                    level as nat + 1,
                    pte@.addr(),
                );
            }
            self.prune(vaddr, pte.addr(), level + 1);
            assert(self.pt_mem@.accessible(base@, idx as nat));
            assert(self.pt_mem@.contains_table(pte@.addr()));

            if self.is_table_empty(pte.addr(), level + 1) {
                // If subtable is empty, deallocate the table, and mark the entry as invalid
                self.pt_mem.dealloc_table(pte.addr());
                assert(self.pt_mem@.accessible(base@, idx as nat));
                self.pt_mem.write(base, idx, E::empty().to_u64());
            }
        }
    }

    /// Resolve a virtual address to its mapped physical frame.
    pub fn query(&self, vaddr: VAddrExec) -> (res: PagingResult<(VAddrExec, FrameExec)>)
        requires
            self@.invariants(),
        ensures
            self@@.query(vaddr@) == match res {
                PagingResult::Ok((vaddr, frame)) => PagingResult::Ok((vaddr@, frame@)),
                PagingResult::Err(_) => PagingResult::Err(()),
            },
    {
        let (pte, level) = self.walk(vaddr, self.pt_mem.root(), 0);
        proof {
            let root = self.pt_mem@.root();
            self@.construct_node_facts(root, 0);

            // spec `get_pte` == node `visit`
            self.pt_mem@.lemma_contains_root();
            self@.lemma_construct_node_implies_invariants(root, 0);
            let node = self@.construct_node(root, 0);
            self@.lemma_walk_consistent_with_model(vaddr@, root, 0);
            node.lemma_visit_length_bounds(
                PTTreePath::from_vaddr_root(
                    vaddr@,
                    self.arch(),
                    (self.arch().level_count() - 1) as nat,
                ),
            );
            assert(level < self.arch().level_count());
            // exec `query` consistent with model `query`
            if pte@.valid() {
                assert(self@@.query(vaddr@) == PagingResult::Ok(
                    (
                        self.arch().vbase(vaddr@, level as nat),
                        Frame {
                            base: pte@.addr(),
                            size: self.arch().frame_size(level as nat),
                            attr: pte@.attr(),
                        },
                    ),
                ));
            } else {
                assert(self@@.query(vaddr@) == PagingResult::<(VAddr, Frame)>::Err(()));
            }
        }
        if pte.valid() {
            Ok(
                (
                    self.constants.arch.vbase(vaddr, level),
                    FrameExec {
                        base: pte.addr(),
                        size: self.constants.arch.frame_size(level),
                        attr: pte.attr(),
                    },
                ),
            )
        } else {
            Err(())
        }
    }

    /// Insert a mapping from a virtual base address to a physical frame.
    pub fn map(&mut self, vbase: VAddrExec, frame: FrameExec) -> (res: PagingResult)
        requires
            old(self)@.invariants(),
            old(self)@.constants.arch.is_valid_frame_size(frame.size),
            vbase@.aligned(frame.size.as_nat()),
            frame.base@.aligned(frame.size.as_nat()),
            frame.base.0 >= old(self).constants.pmem_lb.0,
            frame.base.0 + frame.size.as_nat() <= old(self).constants.pmem_ub.0,
        ensures
            self@.invariants(),
            ({
                let (s2, r) = old(self)@@.map(vbase@, frame@);
                r is Ok == res is Ok && s2 == self@@
            }),
    {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        let target_level = self.constants.arch.level_of_frame_size(frame.size);
        let huge = target_level < self.constants.arch.level_count() - 1;
        proof {
            assume(frame.base@.aligned(FrameSize::Size4K.as_nat()));
        }
        let new_pte = E::new(frame.base, frame.attr, huge);

        proof {
            let root = self.pt_mem@.root();
            self.view().construct_node_facts(root, 0);
            // Ensures #1
            self.view().lemma_insert_preserves_invariants(
                vbase@,
                root,
                0,
                target_level as nat,
                new_pte@,
            );
            // Ensures #2
            self.view().lemma_insert_consistent_with_model(
                vbase@,
                root,
                0,
                target_level as nat,
                new_pte@,
            );
            self.view().lemma_insert_preserves_root(vbase@, root, 0, target_level as nat, new_pte@);
        }

        self.insert(vbase, self.pt_mem.root(), 0, target_level, new_pte)
    }

    /// Remove the mapping for a given virtual base address.
    pub fn unmap(&mut self, vbase: VAddrExec) -> (res: PagingResult)
        requires
            old(self)@.invariants(),
        ensures
            self@.invariants(),
            ({
                let (s2, r) = old(self)@@.unmap(vbase@);
                r is Ok == res is Ok && s2 == self@@
            }),
    {
        let ghost root = self.pt_mem@.root();
        proof {
            self@.construct_node_facts(root, 0);
            // Ensures #1
            self@.lemma_remove_preserves_invariants(vbase@, root, 0);
            // Ensures #2
            self@.lemma_remove_consistent_with_model(vbase@, root, 0);
            self@.lemma_remove_preserves_root(vbase@, root, 0);
        }
        let res = self.remove(vbase, self.pt_mem.root(), 0);
        proof {
            self@.construct_node_facts(root, 0);
            // Ensures #1
            self@.lemma_prune_preserves_invariants(vbase@, root, 0);
            // Ensures #2
            self@.lemma_prune_consistent_with_model(vbase@, root, 0);
            self@.lemma_prune_preserves_root(vbase@, root, 0);
        }
        if res.is_ok() {
            self.prune(vbase, self.pt_mem.root(), 0);
        }
        res
    }
}

} // verus!
