//! Executable page table implementation.
use core::{alloc, marker::PhantomData};
use std::alloc::Allocator;
use vstd::prelude::*;

use super::{path::PTTreePath, spec_pt::SpecPageTable};
use crate::{
    address::{
        addr::{PAddr, SpecVAddr, VAddr},
        frame::{Frame, FrameSize, MemAttr, SpecFrame},
    },
    frame_allocator::frame_trait::FrameAllocator,
    global_allocator::GlobalAllocator,
    page_table::{
        pt_arch::SpecPTArch,
        pt_mem::PageTableMem,
        pt_trait::{PTConstants, PagingResult},
        pte::PageTableEntry,
    },
};

verus! {

// Use page table memory related lemmas.
broadcast use crate::page_table::pt_mem::group_pt_mem_lemmas;

/// Executable page table implementation.
///
/// `PageTable` wraps a `PageTableMem` and a `PTConstants` to provide a convenient interface for
/// manipulating the page table. Refinement proof is provided by implementing trait `PageTableInterface`
/// to ensure `PageTableMem` is manipulated correctly.
pub struct PageTable<A: GlobalAllocator, E: PageTableEntry> {
    /// Page table memory.
    pub pt_mem: PageTableMem<A>,
    /// Page table config constants.
    pub constants: PTConstants,
    /// Phantom data.
    pub _phantom: PhantomData<E>,
}

impl<A, E> PageTable<A, E> where A: GlobalAllocator, E: PageTableEntry {
    /// View as a specification-level page table.
    pub open spec fn view(&self, allocator: &A) -> SpecPageTable<E> {
        SpecPageTable {
            pt_mem: self.pt_mem.view(allocator),
            constants: self.constants@,
            _phantom: PhantomData,
        }
    }

    /// Page table architecture specification.
    pub open spec fn arch(&self) -> SpecPTArch {
        self.constants.arch@
    }

    /// Invariants that must implied at initial state and preseved after each operation.
    pub open spec fn invariants(&self, allocator: &A) -> bool {
        &&& self.pt_mem.invariants(allocator)
        &&& self.view(allocator).wf()
    }

    /// Construct a new page table.
    ///
    /// TODO: we assume all tables in the hierarchical page table contain 512 8-byte entries, which is true
    /// for hvisor's aarch64 implementation. We can make it more general in the future.
    pub fn new(allocator: &mut A, cid: usize, constants: PTConstants) -> (res: Self)
        requires
            old(allocator).invariants(),
            old(allocator).view().clients.contains_key(cid as nat),
            old(allocator).view().clients[cid as nat].is_empty(),
            !old(allocator).view().free.is_empty(),
            constants@.valid(),
            forall|level: nat|
                level < constants.arch@.level_count() ==> constants.arch@.entry_count(level) == 512,
            A::frame_size() == 4096,
        ensures
            res.invariants(allocator),
            res.view(allocator).pt_mem.init(),
            res.constants == constants,
    {
        let res = Self {
            pt_mem: PageTableMem::new(allocator, cid, constants.arch.clone()),
            constants,
            _phantom: PhantomData,
        };
        proof {
            // TODO
            assume(res.view(allocator).wf());
        }
        res
    }

    /// If all pte in a table are invalid.
    pub fn is_table_empty(&self, allocator: &A, base: PAddr, level: usize) -> (res: bool)
        requires
            self.invariants(allocator),
            self.view(allocator).pt_mem.contains_table(base@),
            self.view(allocator).pt_mem.level(base@) == level,
        ensures
            self.view(allocator).is_table_empty(base@) == res,
    {
        let entry_count = self.constants.arch.entry_count(level);
        for i in 0..entry_count
            invariant
                self.invariants(allocator),
                self.constants.arch@.entry_count(level as nat) == entry_count,
                self.view(allocator).pt_mem.contains_table(base@),
                self.view(allocator).pt_mem.level(base@) == level,
                forall|j: nat|
                    #![auto]
                    j < i ==> !E::spec_from_u64(
                        self.view(allocator).pt_mem.read(base@, j),
                    ).spec_valid(),
        {
            assert(self.view(allocator).pt_mem.accessible(base@, i as nat));
            let pte = E::from_u64(self.pt_mem.read(allocator, base, i));
            if pte.valid() {
                return false;
            }
        }
        true
    }

    /// Traverse the page table for the given virtual address and return the matching
    /// entry and level. Proven consistent with the specification-level walk.
    pub fn walk(&self, allocator: &A, vaddr: VAddr, base: PAddr, level: usize) -> (res: (E, usize))
        requires
            self.invariants(allocator),
            self.pt_mem.view(allocator).contains_table(base@),
            self.pt_mem.view(allocator).level(base@) == level,
        ensures
            (res.0, res.1 as nat) == self.view(allocator).walk(vaddr@, base@, level as nat),
        decreases self.constants.arch@.level_count() - level as nat,
    {
        let idx = self.constants.arch.pte_index(vaddr, level);
        assert(self.pt_mem.view(allocator).accessible(base@, idx as nat));
        let pte = E::from_u64(self.pt_mem.read(allocator, base, idx));
        if level < self.constants.arch.level_count() - 1 && pte.valid() && !pte.huge() {
            self.walk(allocator, vaddr, pte.addr(), level + 1)
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
        allocator: &mut A,
        vbase: VAddr,
        base: PAddr,
        level: usize,
        target_level: usize,
        new_pte: E,
    ) -> (res: PagingResult)
        requires
            old(self).invariants(old(allocator)),
            level <= target_level < old(self).arch().level_count(),
            old(self).pt_mem.view(old(allocator)).contains_table(base@),
            old(self).pt_mem.view(old(allocator)).level(base@) == level,
            old(self).view(old(allocator)).pte_valid_frame(new_pte, target_level as nat),
            !old(allocator).view().free.is_empty(),
        ensures
            (self.view(allocator), res) == old(self).view(old(allocator)).insert(
                vbase@,
                base@,
                level as nat,
                target_level as nat,
                new_pte,
            ),
            self.invariants(allocator),
            res is Err ==> old(self).view(old(allocator)) == self.view(allocator),
        decreases old(self).arch().level_count() - level as nat,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        assert(self.pt_mem.view(allocator).accessible(base@, idx as nat));
        let pte = E::from_u64(self.pt_mem.read(allocator, base, idx));
        if level >= target_level {
            // Insert at current level
            if pte.valid() {
                PagingResult::Err(())
            } else {
                self.pt_mem.write(allocator, base, idx, new_pte.to_u64());
                PagingResult::Ok(())
            }
        } else {
            if pte.valid() {
                if pte.huge() {
                    PagingResult::Err(())
                } else {
                    // Insert at next level
                    self.insert(allocator, vbase, pte.addr(), level + 1, target_level, new_pte)
                }
            } else {
                proof {
                    self.view(allocator).lemma_alloc_intermediate_table_preserves_wf(
                        base@,
                        level as nat,
                        idx as nat,
                    );
                    // Lemma ensures this branch returns Ok
                    self.view(allocator).lemma_insert_intermediate_node_results_ok(
                        vbase@,
                        base@,
                        level as nat,
                        target_level as nat,
                        new_pte,
                    );
                }
                // Allocate intermediate table
                let table_base = self.pt_mem.alloc_table(allocator, level + 1);
                assert(table_base@.aligned(FrameSize::Size4K.as_nat()));

                // Write entry
                let pte = E::new(table_base, MemAttr::default(), false);
                self.pt_mem.write(allocator, base, idx, pte.to_u64());

                // TODO: assume allocator always contains enough free frames for intermediate table allocation
                assume(!allocator.view().free.is_empty());
                
                // Insert at next level
                self.insert(allocator, vbase, table_base, level + 1, target_level, new_pte)
            }
        }
    }

    /// Recursively remove a page table entry.
    pub fn remove(&mut self, allocator: &A, vbase: VAddr, base: PAddr, level: usize) -> (res:
        PagingResult)
        requires
            old(self).invariants(allocator),
            level < old(self).arch().level_count(),
            old(self).pt_mem.view(allocator).contains_table(base@),
            old(self).pt_mem.view(allocator).level(base@) == level,
        ensures
            (self.view(allocator), res) == old(self).view(allocator).remove(
                vbase@,
                base@,
                level as nat,
            ),
            self.invariants(allocator),
            res is Err ==> old(self).view(allocator) == self.view(allocator),
        decreases old(self).arch().level_count() - level as nat,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        assert(self.pt_mem.view(allocator).accessible(base@, idx as nat));
        let pte = E::from_u64(self.pt_mem.read(allocator, base, idx));
        if pte.valid() {
            if level >= self.constants.arch.level_count() - 1 {
                // Leaf node
                if vbase.aligned(self.constants.arch.frame_size(level).as_usize()) {
                    self.pt_mem.write(allocator, base, idx, E::empty().to_u64());
                    PagingResult::Ok(())
                } else {
                    PagingResult::Err(())
                }
            } else {
                // Intermediate node
                if pte.huge() {
                    if vbase.aligned(self.constants.arch.frame_size(level).as_usize()) {
                        self.pt_mem.write(allocator, base, idx, E::empty().to_u64());
                        PagingResult::Ok(())
                    } else {
                        PagingResult::Err(())
                    }
                } else {
                    self.remove(allocator, vbase, pte.addr(), level + 1)
                }
            }
        } else {
            PagingResult::Err(())
        }
    }

    /// Recursively deallocate empty tables along `vaddr` from `base`.
    pub fn prune(&mut self, allocator: &mut A, vaddr: VAddr, base: PAddr, level: usize)
        requires
            old(self).invariants(old(allocator)),
            level < old(self).arch().level_count(),
            old(self).pt_mem.view(old(allocator)).contains_table(base@),
            old(self).pt_mem.view(old(allocator)).level(base@) == level,
        ensures
            self.view(allocator) == old(self).view(old(allocator)).prune(
                vaddr@,
                base@,
                level as nat,
            ),
            self.invariants(allocator),
        decreases old(self).arch().level_count() - level as nat,
    {
        proof { self.view(allocator).lemma_prune_preserves_wf(vaddr@, base@, level as nat) }

        let idx = self.constants.arch.pte_index(vaddr, level);
        assert(self.pt_mem.view(allocator).accessible(base@, idx as nat));
        let pte = E::from_u64(self.pt_mem.read(allocator, base, idx));
        if level < self.constants.arch.level_count() - 1 && pte.valid() && !pte.huge() {
            // Prune from subtable
            proof {
                // Invariants satisfied after recycling from subtable
                self.view(allocator).lemma_prune_preserves_wf(
                    vaddr@,
                    pte.spec_addr(),
                    level as nat + 1,
                );
                // Current table and subtable are accessible after recycling from subtable
                self.view(allocator).lemma_prune_preserves_lower_tables(
                    vaddr@,
                    pte.spec_addr(),
                    level as nat + 1,
                    base@,
                );
                self.view(allocator).lemma_prune_preserves_lower_tables(
                    vaddr@,
                    pte.spec_addr(),
                    level as nat + 1,
                    pte.spec_addr(),
                );
            }
            self.prune(allocator, vaddr, pte.addr(), level + 1);
            assert(self.pt_mem.view(allocator).accessible(base@, idx as nat));
            assert(self.pt_mem.view(allocator).contains_table(pte.spec_addr()));

            if self.is_table_empty(allocator, pte.addr(), level + 1) {
                // If subtable is empty, deallocate the table, and mark the entry as invalid
                self.pt_mem.dealloc_table(allocator, pte.addr());
                assert(self.pt_mem.view(allocator).accessible(base@, idx as nat));
                self.pt_mem.write(allocator, base, idx, E::empty().to_u64());
            }
        }
    }

    /// Resolve a virtual address to its mapped physical frame.
    pub fn query(&self, allocator: &A, vaddr: VAddr) -> (res: PagingResult<(VAddr, Frame)>)
        requires
            self.invariants(allocator),
        ensures
            self.view(allocator)@.query(vaddr@) == match res {
                PagingResult::Ok((vaddr, frame)) => PagingResult::Ok((vaddr@, frame@)),
                PagingResult::Err(_) => PagingResult::Err(()),
            },
    {
        let (pte, level) = self.walk(allocator, vaddr, self.pt_mem.root, 0);
        proof {
            let root = self.pt_mem.view(allocator).root;
            self.view(allocator).construct_node_facts(root, 0);

            // spec `get_pte` == node `visit`
            self.view(allocator).lemma_construct_node_implies_node_wf(root, 0);
            let node = self.view(allocator).construct_node(root, 0);
            self.view(allocator).lemma_walk_consistent_with_model(vaddr@, root, 0);
            node.lemma_visit_length_bounds(
                PTTreePath::from_vaddr_root(
                    vaddr@,
                    self.arch(),
                    (self.arch().level_count() - 1) as nat,
                ),
            );
            assert(level < self.arch().level_count());
            // exec `query` consistent with model `query`
            if pte.spec_valid() {
                assert(self.view(allocator)@.query(vaddr@) == PagingResult::Ok(
                    (
                        self.arch().vbase(vaddr@, level as nat),
                        SpecFrame {
                            base: pte.spec_addr(),
                            size: self.arch().frame_size(level as nat),
                            attr: pte.spec_attr(),
                        },
                    ),
                ));
            } else {
                assert(self.view(allocator)@.query(vaddr@) == PagingResult::<
                    (SpecVAddr, SpecFrame),
                >::Err(()));
            }
        }
        if pte.valid() {
            Ok(
                (
                    self.constants.arch.vbase(vaddr, level),
                    Frame {
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
    pub fn map(&mut self, allocator: &mut A, vbase: VAddr, frame: Frame) -> (res: PagingResult)
        requires
            old(self).invariants(old(allocator)),
            old(self).constants@.arch.is_valid_frame_size(frame.size),
            vbase@.aligned(frame.size.as_nat()),
            frame.base@.aligned(frame.size.as_nat()),
            !old(allocator).view().free.is_empty(),
        ensures
            self.invariants(allocator),
            ({
                let (s2, r) = old(self).view(old(allocator))@.map(vbase@, frame@);
                r is Ok == res is Ok && s2 == self.view(allocator)@
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
            let root = self.pt_mem.view(allocator).root;
            self.view(allocator).construct_node_facts(root, 0);
            // Ensures #1
            self.view(allocator).lemma_insert_preserves_wf(
                vbase@,
                root,
                0,
                target_level as nat,
                new_pte,
            );
            // Ensures #2
            self.view(allocator).lemma_insert_consistent_with_model(
                vbase@,
                root,
                0,
                target_level as nat,
                new_pte,
            );
            self.view(allocator).lemma_insert_preserves_root(
                vbase@,
                root,
                0,
                target_level as nat,
                new_pte,
            );
        }

        self.insert(allocator, vbase, self.pt_mem.root, 0, target_level, new_pte)
    }

    /// Remove the mapping for a given virtual base address.
    pub fn unmap(&mut self, allocator: &mut A, vbase: VAddr) -> (res: PagingResult)
        requires
            old(self).invariants(old(allocator)),
        ensures
            self.invariants(allocator),
            ({
                let (s2, r) = old(self).view(old(allocator))@.unmap(vbase@);
                r is Ok == res is Ok && s2 == self.view(allocator)@
            }),
    {
        let ghost root = self.pt_mem.view(allocator).root;
        proof {
            self.view(allocator).construct_node_facts(root, 0);
            // Ensures #1
            self.view(allocator).lemma_remove_preserves_wf(vbase@, root, 0);
            // Ensures #2
            self.view(allocator).lemma_remove_consistent_with_model(vbase@, root, 0);
            self.view(allocator).lemma_remove_preserves_root(vbase@, root, 0);
        }
        let res = self.remove(allocator, vbase, self.pt_mem.root, 0);
        proof {
            self.view(allocator).construct_node_facts(root, 0);
            // Ensures #1
            self.view(allocator).lemma_prune_preserves_wf(vbase@, root, 0);
            // Ensures #2
            self.view(allocator).lemma_prune_consistent_with_model(vbase@, root, 0);
            self.view(allocator).lemma_prune_preserves_root(vbase@, root, 0);
        }
        if res.is_ok() {
            self.prune(allocator, vbase, self.pt_mem.root, 0);
        }
        res
    }
}

} // verus!
