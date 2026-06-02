//! Executable page table implementation.
use core::{alloc, marker::PhantomData};
use vstd::prelude::*;
use vstd::tokens::InstanceId;

use super::{path::PTTreePath, spec_pt::SpecPageTable};
use crate::{
    address::{
        addr::{PAddr, SpecPAddr, SpecVAddr, VAddr},
        frame::{Frame, FrameSize, MemAttr, SpecFrame},
    },
    bitmap_allocator::bitmap_trait::BitmapAllocator,
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
pub struct PageTable<A: BitmapAllocator, E: PageTableEntry> {
    /// Page table memory.
    pub pt_mem: PageTableMem<A>,
    /// Page table config constants.
    pub constants: PTConstants,
    /// Phantom data.
    pub _phantom: PhantomData<E>,
}

impl<A, E> PageTable<A, E> where A: BitmapAllocator, E: PageTableEntry {
    /// View as a specification-level page table.
    pub open spec fn view(&self) -> SpecPageTable<E> {
        SpecPageTable { pt_mem: self.pt_mem@, constants: self.constants@, _phantom: PhantomData }
    }

    /// Page table architecture specification.
    pub open spec fn arch(&self) -> SpecPTArch {
        self.constants.arch@
    }

    /// Invariants that must implied at initial state and preseved after each operation.
    pub open spec fn invariants(&self) -> bool {
        let view = self@;
        &&& self.pt_mem.invariants()
        &&& view.wf()
        &&& view.all_nonempty_above(0)
    }

    /// Instance Id of the `AllocSpec`
    pub open spec fn inst_id(&self) -> InstanceId {
        self.pt_mem.inst_id()
    }

    /// Construct a new page table.
    ///
    /// TODO: we assume all tables in the hierarchical page table contain 512 8-byte entries, which is true
    /// for hvisor's aarch64 implementation. We can make it more general in the future.
    pub fn new(allocator: &GlobalAllocator<A>, constants: PTConstants) -> (res: Self)
        requires
            allocator.invariants(),
            constants@.valid(),
            forall|level: nat|
                level < constants.arch@.level_count() ==> constants.arch@.entry_count(level) == 512,
        ensures
            res.invariants(),
            res.inst_id() == allocator.inst_id(),
            res@.pt_mem.init(),
            res.constants == constants,
    {
        let res = Self {
            pt_mem: PageTableMem::new(allocator, constants.arch.clone()),
            constants,
            _phantom: PhantomData,
        };
        proof {
            broadcast use crate::page_table::pte::group_pte_lemmas;

            let pt_mem = res.pt_mem@;
            assert(forall|base: SpecPAddr, idx: nat| #[trigger]
                pt_mem.accessible(base, idx) ==> !E::spec_from_u64(
                    pt_mem.read(base, idx),
                ).spec_valid());
            assert(res@.wf());
        }
        res
    }

    /// If all pte in a table are invalid.
    pub fn is_table_empty(&self, base: PAddr, level: usize) -> (res: bool)
        requires
            self.pt_mem.invariants(),
            self@.wf(),
            self@.pt_mem.contains_table(base@),
            self@.pt_mem.level(base@) == level,
        ensures
            self@.is_table_empty(base@) == res,
    {
        let entry_count = self.constants.arch.entry_count(level);
        for i in 0..entry_count
            invariant
                self.pt_mem.invariants(),
                self@.wf(),
                self.constants.arch@.entry_count(level as nat) == entry_count,
                self@.pt_mem.contains_table(base@),
                self@.pt_mem.level(base@) == level,
                forall|j: nat|
                    #![auto]
                    j < i ==> !E::spec_from_u64(self@.pt_mem.read(base@, j)).spec_valid(),
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
    pub fn walk(&self, vaddr: VAddr, base: PAddr, level: usize) -> (res: (E, usize))
        requires
            self.pt_mem.invariants(),
            self@.wf(),
            self.pt_mem@.contains_table(base@),
            self.pt_mem@.level(base@) == level,
        ensures
            (res.0, res.1 as nat) == self@.walk(vaddr@, base@, level as nat),
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
        allocator: &GlobalAllocator<A>,
        vbase: VAddr,
        base: PAddr,
        level: usize,
        target_level: usize,
        new_pte: E,
    ) -> (res: PagingResult)
        requires
            allocator.invariants(),
            old(self).inst_id() == allocator.inst_id(),
            old(self).pt_mem.invariants(),
            old(self)@.wf(),
            level <= target_level < old(self).arch().level_count(),
            old(self).pt_mem@.contains_table(base@),
            old(self).pt_mem@.level(base@) == level,
            old(self)@.pte_valid_frame(new_pte, target_level as nat),
            new_pte.wf(),
        ensures
            (self@, res) == old(self)@.insert(
                vbase@,
                base@,
                level as nat,
                target_level as nat,
                new_pte,
            ),
            self.inst_id() == old(self).inst_id(),
            self.pt_mem.invariants(),
            self@.wf(),
            res is Err ==> old(self)@ == self@,
        decreases old(self).arch().level_count() - level as nat,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        assert(self.pt_mem@.accessible(base@, idx as nat));
        let pte = E::from_u64(self.pt_mem.read(base, idx));
        proof {
            self@.lemma_insert_preserves_wf(
                vbase@,
                base@,
                level as nat,
                target_level as nat,
                new_pte,
            );
        }

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
                    self.insert(allocator, vbase, pte.addr(), level + 1, target_level, new_pte)
                }
            } else {
                proof {
                    self@.lemma_alloc_intermediate_table_preserves_wf(
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
                        new_pte,
                    );
                }
                // Allocate intermediate table
                let table_base = self.pt_mem.alloc_table(allocator, level + 1);
                assert(table_base@.aligned(FrameSize::Size4K.as_nat()));

                // Write entry
                let pte = E::new(table_base, MemAttr::default(), false);
                self.pt_mem.write(base, idx, pte.to_u64());

                // Insert at next level
                self.insert(allocator, vbase, table_base, level + 1, target_level, new_pte)
            }
        }
    }

    /// Recursively remove a page table entry.
    pub fn remove(&mut self, vbase: VAddr, base: PAddr, level: usize) -> (res: PagingResult)
        requires
            old(self).pt_mem.invariants(),
            old(self)@.wf(),
            level < old(self).arch().level_count(),
            old(self).pt_mem@.contains_table(base@),
            old(self).pt_mem@.level(base@) == level,
        ensures
            (self@, res) == old(self)@.remove(vbase@, base@, level as nat),
            self.inst_id() == old(self).inst_id(),
            self.pt_mem.invariants(),
            self@.wf(),
            res is Err ==> old(self)@ == self@,
        decreases old(self).arch().level_count() - level as nat,
    {
        proof {
            self@.lemma_remove_preserves_wf(vbase@, base@, level as nat);
        }
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
    pub fn prune(&mut self, allocator: &GlobalAllocator<A>, vaddr: VAddr, base: PAddr, level: usize)
        requires
            allocator.invariants(),
            old(self).inst_id() == allocator.inst_id(),
            old(self).pt_mem.invariants(),
            old(self)@.wf(),
            level < old(self).arch().level_count(),
            old(self).pt_mem@.contains_table(base@),
            old(self).pt_mem@.level(base@) == level,
        ensures
            self@ == old(self)@.prune(vaddr@, base@, level as nat),
            self.inst_id() == old(self).inst_id(),
            self.pt_mem.invariants(),
            self@.wf(),
        decreases old(self).arch().level_count() - level as nat,
    {
        proof { self@.lemma_prune_preserves_wf(vaddr@, base@, level as nat) }

        let idx = self.constants.arch.pte_index(vaddr, level);
        assert(self.pt_mem@.accessible(base@, idx as nat));
        let pte = E::from_u64(self.pt_mem.read(base, idx));
        if level < self.constants.arch.level_count() - 1 && pte.valid() && !pte.huge() {
            // Prune from subtable
            proof {
                // Invariants satisfied after recycling from subtable
                self@.lemma_prune_preserves_wf(vaddr@, pte.spec_addr(), level as nat + 1);
                // Current table and subtable are accessible after recycling from subtable
                self@.lemma_prune_preserves_lower_tables(
                    vaddr@,
                    pte.spec_addr(),
                    level as nat + 1,
                    base@,
                );
                self@.lemma_prune_preserves_lower_tables(
                    vaddr@,
                    pte.spec_addr(),
                    level as nat + 1,
                    pte.spec_addr(),
                );
            }
            self.prune(allocator, vaddr, pte.addr(), level + 1);
            assert(self.pt_mem@.accessible(base@, idx as nat));
            assert(self.pt_mem@.contains_table(pte.spec_addr()));

            if self.is_table_empty(pte.addr(), level + 1) {
                // If subtable is empty, deallocate the table, and mark the entry as invalid
                self.pt_mem.dealloc_table(allocator, pte.addr());
                assert(self.pt_mem@.accessible(base@, idx as nat));
                self.pt_mem.write(base, idx, E::empty().to_u64());
            }
        }
    }

    /// Resolve a virtual address to its mapped physical frame.
    pub fn query(&self, vaddr: VAddr) -> (res: PagingResult<(VAddr, Frame)>)
        requires
            self.invariants(),
        ensures
            self@@.query(vaddr@) == match res {
                PagingResult::Ok((vaddr, frame)) => PagingResult::Ok((vaddr@, frame@)),
                PagingResult::Err(_) => PagingResult::Err(()),
            },
    {
        let (pte, level) = self.walk(vaddr, self.pt_mem.root, 0);
        proof {
            let root = self.pt_mem@.root;
            self@.construct_node_facts(root, 0);

            // spec `get_pte` == node `visit`
            self@.lemma_construct_node_wf(root, 0);
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
            if pte.spec_valid() {
                assert(self@@.query(vaddr@) == PagingResult::Ok(
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
                assert(self@@.query(vaddr@) == PagingResult::<(SpecVAddr, SpecFrame)>::Err(()));
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
    pub fn map(&mut self, allocator: &GlobalAllocator<A>, vbase: VAddr, frame: Frame) -> (res:
        PagingResult)
        requires
            allocator.invariants(),
            old(self).inst_id() == allocator.inst_id(),
            old(self).invariants(),
            old(self).constants@.arch.is_valid_frame_size(frame.size),
            vbase@.aligned(frame.size.as_nat()),
            frame.base@.aligned(frame.size.as_nat()),
        ensures
            allocator.invariants(),
            self.inst_id() == old(self).inst_id(),
            self.invariants(),
            ({
                let (s2, r) = old(self)@@.map(vbase@, frame@);
                r is Ok == res is Ok && s2 == self@@
            }),
    {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        let target_level = self.constants.arch.level_of_frame_size(frame.size);
        let huge = target_level < self.constants.arch.level_count() - 1;
        proof {
            // TODO: supporting more frame sizes
            assert(forall|level: nat|
                level < self.constants.arch@.level_count() ==> self.constants.arch@.entry_count(
                    level,
                ) == 512);
            assert(frame.size.as_nat() % 4096 == 0);
            assert(frame.base@.aligned(4096)) by (nonlinear_arith)
                requires
                    frame.size.as_nat() % 4096 == 0,
                    frame.base@.aligned(frame.size.as_nat()),
            ;
        }
        let new_pte = E::new(frame.base, frame.attr, huge);
        assert(new_pte.wf());

        proof {
            let root = self.pt_mem@.root;
            self@.construct_node_facts(root, 0);
            // Ensures #1
            self@.lemma_insert_preserves_wf(vbase@, root, 0, target_level as nat, new_pte);
            self@.lemma_insert_preserves_all_nonempty(
                vbase@,
                root,
                0,
                target_level as nat,
                new_pte,
            );
            // Ensures #2
            self@.lemma_insert_consistent_with_model(vbase@, root, 0, target_level as nat, new_pte);
            self@.lemma_insert_preserves_root(vbase@, root, 0, target_level as nat, new_pte);
        }

        self.insert(allocator, vbase, self.pt_mem.root, 0, target_level, new_pte)
    }

    /// Remove the mapping for a given virtual base address.
    pub fn unmap(&mut self, allocator: &GlobalAllocator<A>, vbase: VAddr) -> (res: PagingResult)
        requires
            allocator.invariants(),
            old(self).inst_id() == allocator.inst_id(),
            old(self).invariants(),
            vbase@.aligned(old(self).constants.arch@.leaf_frame_size().as_nat()),
        ensures
            allocator.invariants(),
            self.inst_id() == old(self).inst_id(),
            self.invariants(),
            ({
                let (s2, r) = old(self)@@.unmap(vbase@);
                r is Ok == res is Ok && s2 == self@@
            }),
    {
        let ghost root = self.pt_mem@.root;
        proof {
            self@.construct_node_facts(root, 0);
            // Ensures #1
            self@.lemma_remove_preserves_wf(vbase@, root, 0);
            if !self@.is_table_empty(root) {
                self@.lemma_prune_after_remove_preserves_all_nonempty(vbase@, root, 0);
            }
            // Ensures #2

            self@.lemma_remove_consistent_with_model(vbase@, root, 0);
            self@.lemma_remove_preserves_root(vbase@, root, 0);
        }
        let res = self.remove(vbase, self.pt_mem.root, 0);
        proof {
            self@.construct_node_facts(root, 0);
            // Ensures #1
            self@.lemma_prune_preserves_wf(vbase@, root, 0);
            // Ensures #2
            self@.lemma_prune_consistent_with_model(vbase@, root, 0);
            self@.lemma_prune_preserves_root(vbase@, root, 0);
        }
        if res.is_ok() {
            self.prune(allocator, vbase, self.pt_mem.root, 0);
            proof {
                self@.lemma_all_nonempty_above_root_implies();
            }
        }
        res
    }
}

} // verus!
