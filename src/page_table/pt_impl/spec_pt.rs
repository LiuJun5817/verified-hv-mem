//! Spec-mode page table implementation. Used for refinement proofs.
use core::marker::PhantomData;
use std::io::Empty;
use vstd::prelude::*;

use super::{
    path::*,
    tree::{NodeEntry, PTTreeModel, PTTreeNode},
};
use crate::page_table::{
    pt_arch::SpecPTArch,
    pt_mem::SpecPageTableMem,
    pt_trait::{PagingResult, SpecPTConstants},
    pte,
};
use crate::{
    address::{
        addr::{SpecPAddr, SpecVAddr},
        frame::{MemAttr, SpecFrame},
    },
    page_table::pte::PageTableEntry,
};

verus! {

// Use page table memory related lemmas.
broadcast use crate::page_table::pt_mem::group_pt_mem_lemmas;

/// Spec-mode page table implementation.
pub struct SpecPageTable<E: PageTableEntry> {
    /// Page table memory.
    pub pt_mem: SpecPageTableMem,
    /// Page table config constants.
    pub constants: SpecPTConstants,
    /// Phantom data.
    pub _phantom: PhantomData<E>,
}

impl<E> SpecPageTable<E> where E: PageTableEntry {
    /// Wrap a page table memory and constants into a spec-mode page table.
    pub open spec fn new(pt_mem: SpecPageTableMem, constants: SpecPTConstants) -> Self {
        Self { pt_mem, constants, _phantom: PhantomData }
    }

    /// If `pte` points to a frame.
    pub open spec fn pte_points_to_frame(self, pte: E, level: nat) -> bool {
        pte.wf() && pte.spec_valid() && if level < self.constants.arch.level_count() - 1 {
            pte.spec_huge()
        } else {
            !pte.spec_huge()
        }
    }

    /// If `pte` points to a table.
    pub open spec fn pte_points_to_table(self, pte: E, level: nat) -> bool {
        pte.wf() && pte.spec_valid() && level < self.constants.arch.level_count() - 1
            && !pte.spec_huge()
    }

    /// If `pte` points to a frame with valid address and size.
    pub open spec fn pte_valid_frame(self, pte: E, level: nat) -> bool {
        let frame_size = self.constants.arch.frame_size(level);
        &&& self.pte_points_to_frame(pte, level)
        &&& pte.spec_addr().aligned(frame_size.as_nat())
    }

    /// Construct a `Frame` from a `PTE`.
    pub open spec fn pte_to_frame(self, pte: E, level: nat) -> SpecFrame {
        SpecFrame {
            base: pte.spec_addr(),
            attr: pte.spec_attr(),
            size: self.constants.arch.frame_size(level),
        }
    }

    /// If all pte in a table are invalid.
    pub open spec fn is_table_empty(self, base: SpecPAddr) -> bool
        recommends
            self.wf(),
            self.pt_mem.contains_table(base),
    {
        let level = self.pt_mem.level(base);
        forall|idx: nat|
            #![auto]
            idx < self.constants.arch.entry_count(level) ==> !E::spec_from_u64(
                self.pt_mem.read(base, idx),
            ).spec_valid()
    }

    /// Structure well-formedness of the page table.
    pub open spec fn wf(self) -> bool {
        // Architecture
        &&& self.pt_mem.arch
            == self.constants.arch
        // Page table memory well-formed
        &&& self.pt_mem.wf()
        // For each page table entry that can be accessed
        &&& forall|base: SpecPAddr, idx: nat|
            self.pt_mem.accessible(base, idx) ==> {
                let pt_mem = self.pt_mem;
                let level = pt_mem.level(base);
                let pte = E::spec_from_u64(pt_mem.read(base, idx));
                let addr = pte.spec_addr();
                &&& pte.wf()
                // If `table` is a leaf table, `pte` is either invalid or points to a frame
                &&& (level == self.constants.arch.level_count() - 1 && pte.spec_valid())
                    ==> !pte.spec_huge()
                // If `pte` is valid and points to a subtable
                &&& self.pte_points_to_table(pte, level) ==> {
                    // The subtable is not root
                    &&& addr
                        != self.pt_mem.root
                    // `pt_mem` contains the subtable, and the table level is one level higher than `base`
                    &&& pt_mem.contains_table(addr)
                    &&& pt_mem.level(addr) == level + 1
                }
                // If `pte` is valid and points to a frame
                &&& self.pte_points_to_frame(pte, level) ==> {
                    // The frame is valid
                    addr.aligned(self.constants.arch.frame_size(level).as_nat())
                }
            }
            // For each 2 page table entries that can be accessed
        &&& forall|base1: SpecPAddr, idx1: nat, base2: SpecPAddr, idx2: nat|
            self.pt_mem.accessible(base1, idx1) && self.pt_mem.accessible(base2, idx2) ==> {
                let pte1 = E::spec_from_u64(self.pt_mem.read(base1, idx1));
                let pte2 = E::spec_from_u64(self.pt_mem.read(base2, idx2));
                // If two pte points to the same table, they must be equal
                ({
                    &&& self.pte_points_to_table(pte1, self.pt_mem.level(base1))
                    &&& self.pte_points_to_table(pte2, self.pt_mem.level(base2))
                }) ==> {
                    ||| base1 == base2 && idx1 == idx2
                    ||| (pte1.spec_addr() != pte2.spec_addr())
                }
            }
    }

    /// For each table except `base`, it contains at least one valid pte.
    pub open spec fn all_nonempty_except(self, base: SpecPAddr) -> bool {
        forall|base2: SpecPAddr|
            self.pt_mem.contains_table(base2) && base2 != base ==> !self.is_table_empty(base2)
    }

    /// All tables contain at least one valid pte.
    pub open spec fn all_nonempty(self) -> bool {
        forall|base: SpecPAddr| self.pt_mem.contains_table(base) ==> !self.is_table_empty(base)
    }

    /// All tables higher than a given level contain at least one valid pte.
    pub open spec fn all_nonempty_above(self, level: nat) -> bool {
        forall|base: SpecPAddr, level2: nat|
            self.pt_mem.contains_table_with_level(base, level2) && level2 > level
                ==> !self.is_table_empty(base)
    }

    /// Recursively construct a `PTTreeNode` from a subtable.
    pub uninterp spec fn construct_node(self, base: SpecPAddr, level: nat) -> PTTreeNode
        recommends
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
    ;

    /// Illustrate the refinement relationship between `PageTable` and `PTTreeModel`.
    #[verifier::external_body]
    pub proof fn construct_node_facts(self, base: SpecPAddr, level: nat)
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
        ensures
            ({
                let node = self.construct_node(base, level);
                &&& node.level == level
                &&& node.constants == self.constants
                &&& node.entries.len() == self.constants.arch.entry_count(level)
                &&& forall|idx: nat|
                    idx < self.constants.arch.entry_count(level) ==> {
                        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
                        let entry = #[trigger] node.entries[idx as int];
                        match entry {
                            NodeEntry::Frame(frame) => {
                                &&& self.pte_points_to_frame(pte, level)
                                &&& frame.base == pte.spec_addr()
                                &&& frame.attr == pte.spec_attr()
                                &&& frame.size == self.constants.arch.frame_size(level)
                            },
                            NodeEntry::Node(subnode) => {
                                &&& self.pte_points_to_table(pte, level)
                                &&& subnode == self.construct_node(pte.spec_addr(), level + 1)
                            },
                            NodeEntry::Empty => !pte.spec_valid(),
                        }
                    }
            }),
    {
    }

    /// View the page table implementation as a tree-model abstraction.
    pub open spec fn view(self) -> PTTreeModel
        recommends
            self.wf(),
    {
        PTTreeModel { root: self.construct_node(self.pt_mem.root, 0) }
    }

    /// Perform a recursive specification-level page table walk starting from a given base.
    ///
    /// Terminate upon reaching an invalid or block entry, or reaching the leaf level.
    pub open spec fn walk(self, vaddr: SpecVAddr, base: SpecPAddr, level: nat) -> (E, nat)
        recommends
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
        decreases self.constants.arch.level_count() - level,
    {
        let pte = E::spec_from_u64(
            self.pt_mem.read(base, self.constants.arch.pte_index(vaddr, level)),
        );
        if self.pte_points_to_table(pte, level) {
            self.walk(vaddr, pte.spec_addr(), level + 1)
        } else {
            (pte, level)
        }
    }

    /// Perform a recursive specification-level page table insertion starting from a given base.
    pub open spec fn insert(
        self,
        vbase: SpecVAddr,
        base: SpecPAddr,
        level: nat,
        target_level: nat,
        new_pte: E,
    ) -> (Self, PagingResult)
        recommends
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level <= target_level < self.constants.arch.level_count(),
            self.pte_valid_frame(new_pte, target_level),
        decreases target_level - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
        if level >= target_level {
            // Insert at current level
            if pte.spec_valid() {
                (self, Err(()))
            } else {
                (
                    Self::new(self.pt_mem.write(base, idx, new_pte.spec_to_u64()), self.constants),
                    Ok(()),
                )
            }
        } else {
            if pte.spec_valid() {
                if pte.spec_huge() {
                    (self, Err(()))
                } else {
                    // Insert at next level
                    self.insert(vbase, pte.spec_addr(), level + 1, target_level, new_pte)
                }
            } else {
                // Insert intermediate table
                // Allocate a new table
                let (pt_mem, new_base) = self.pt_mem.alloc_table(level + 1);
                // Write entry
                let pt_mem = pt_mem.write(
                    base,
                    idx,
                    E::spec_new(new_base, MemAttr::spec_default(), false).spec_to_u64(),
                );
                Self::new(pt_mem, self.constants).insert(
                    vbase,
                    new_base,
                    level + 1,
                    target_level,
                    new_pte,
                )
            }
        }
    }

    /// Perform a recursive specification-level page table removal starting from a given base.
    pub open spec fn remove(self, vbase: SpecVAddr, base: SpecPAddr, level: nat) -> (
        Self,
        PagingResult,
    )
        recommends
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
        if pte.spec_valid() {
            if level >= self.constants.arch.level_count() - 1 {
                // Leaf node
                if vbase.aligned(self.constants.arch.frame_size(level).as_nat()) {
                    (
                        Self::new(
                            self.pt_mem.write(base, idx, E::spec_empty().spec_to_u64()),
                            self.constants,
                        ),
                        Ok(()),
                    )
                } else {
                    (self, Err(()))
                }
            } else {
                if pte.spec_huge() {
                    if vbase.aligned(self.constants.arch.frame_size(level).as_nat()) {
                        (
                            Self::new(
                                self.pt_mem.write(base, idx, E::spec_empty().spec_to_u64()),
                                self.constants,
                            ),
                            Ok(()),
                        )
                    } else {
                        (self, Err(()))
                    }
                } else {
                    // Intermediate node
                    self.remove(vbase, pte.spec_addr(), level + 1)
                }
            }
        } else {
            (self, Err(()))
        }
    }

    /// Recursively remove empty tables along `vaddr` from `base`.
    pub open spec fn prune(self, vaddr: SpecVAddr, base: SpecPAddr, level: nat) -> Self
        recommends
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vaddr, level);
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
        if level >= self.constants.arch.level_count() - 1 {
            // Leaf table
            self
        } else {
            if pte.spec_valid() && !pte.spec_huge() {
                // Prune from subtable
                let sub_pruned = self.prune(vaddr, pte.spec_addr(), level + 1);
                if sub_pruned.is_table_empty(pte.spec_addr()) {
                    // If subtable is empty, deallocate it and mark the entry as invalid
                    Self::new(
                        sub_pruned.pt_mem.dealloc_table(pte.spec_addr()).write(
                            base,
                            idx,
                            E::spec_empty().spec_to_u64(),
                        ),
                        self.constants,
                    )
                } else {
                    sub_pruned
                }
            } else {
                self
            }
        }
    }

    /// Return the sequence of page-table base addresses visited when walking the
    /// page-table path for `vaddr` starting at table `base` on level `level`.
    pub open spec fn collect_table_chain(
        self,
        vaddr: SpecVAddr,
        base: SpecPAddr,
        level: nat,
    ) -> Seq<SpecPAddr>
        recommends
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
        decreases self.constants.arch.level_count() - level,
    {
        let pte = E::spec_from_u64(
            self.pt_mem.read(base, self.constants.arch.pte_index(vaddr, level)),
        );
        if self.pte_points_to_table(pte, level) {
            // PTE points to a child table: continue walk into the child table
            Seq::new(1, |_i| base).add(self.collect_table_chain(vaddr, pte.spec_addr(), level + 1))
        } else {
            // PTE does not point to another table: chain ends here
            Seq::new(1, |_i| base)
        }
    }

    /// Lemma. If a subtree is well-formed, then the node constructed from it is also well-formed.
    pub proof fn lemma_construct_node_wf(self, base: SpecPAddr, level: nat)
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
        ensures
            self.construct_node(base, level).wf(),
        decreases self.constants.arch.level_count() - level,
    {
        let node = self.construct_node(base, level);
        self.construct_node_facts(base, level);

        assert forall|i| 0 <= i < node.entries.len() implies {
            &&& PTTreeNode::is_entry_valid(#[trigger] node.entries[i], node.level, node.constants)
            &&& node.entries[i] is Node ==> node.entries[i]->Node_0.wf()
        } by {
            assert(self.pt_mem.accessible(base, i as nat));
            match node.entries[i] {
                NodeEntry::Frame(frame) => {
                    assert(frame.base.aligned(frame.size.as_nat()));
                },
                NodeEntry::Node(subnode) => {
                    let pte = E::spec_from_u64(self.pt_mem.read(base, i as nat));
                    assert(self.pt_mem.accessible(base, i as nat));
                    // wf ensures this
                    assert(self.pt_mem.contains_table(pte.spec_addr()));
                    assert(self.pt_mem.level(pte.spec_addr()) == level + 1);
                    self.construct_node_facts(pte.spec_addr(), level + 1);
                    self.lemma_construct_node_wf(pte.spec_addr(), level + 1);
                },
                NodeEntry::Empty => (),
            }
        }
    }

    /// Lemma. If a subtree is well-formed and all_nonempty, then the node constructed from it
    /// is also all_nonempty.
    pub proof fn lemma_construct_node_all_nonempty(self, base: SpecPAddr, level: nat)
        requires
            self.wf(),
            self.all_nonempty(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
        ensures
            self.construct_node(base, level).all_nonempty(),
        decreases self.constants.arch.level_count() - level,
    {
        let node = self.construct_node(base, level);
        self.construct_node_facts(base, level);

        // At least one entry is valid and points to a frame or a subtable
        assert(self.pt_mem.contains_table(base));
        let i = choose|i: nat|
            #![auto]
            i < node.entries.len() && E::spec_from_u64(self.pt_mem.read(base, i)).spec_valid();
        assert(node.entries.contains(node.entries[i as int]));
        assert(exists|entry: NodeEntry| #[trigger]
            node.entries.contains(entry) && !(entry is Empty));

        // Satisfied recursively
        assert forall|entry: NodeEntry| #[trigger]
            node.entries.contains(entry) && PTTreeNode::is_entry_valid(
                entry,
                node.level,
                node.constants,
            ) && entry is Node implies entry->Node_0.all_nonempty() by {
            let i = choose|i| 0 <= i < node.entries.len() && node.entries[i] == entry;
            assert(self.pt_mem.accessible(base, i as nat));
            let pte = E::spec_from_u64(self.pt_mem.read(base, i as nat));
            assert(entry->Node_0 == self.construct_node(pte.spec_addr(), level + 1));
            // Recursive call on the child node
            self.lemma_construct_node_all_nonempty(pte.spec_addr(), level + 1);
        }
    }

    /// Lemma. If a table is empty, then the node constructed from it is also empty.
    pub proof fn lemma_construct_node_empty(self, base: SpecPAddr)
        requires
            self.wf(),
            self.pt_mem.contains_table(base),
        ensures
            self.is_table_empty(base) <==> self.construct_node(
                base,
                self.pt_mem.level(base),
            ).empty(),
    {
        let level = self.pt_mem.level(base);
        let node = self.construct_node(base, level);
        self.construct_node_facts(base, level);
        if node.empty() {
            assert forall|idx: nat|
                #![auto]
                idx < self.constants.arch.entry_count(level) implies !E::spec_from_u64(
                self.pt_mem.read(base, idx),
            ).spec_valid() by {
                assert(node.entries.contains(node.entries[idx as int]));
            }
        }
    }

    /// Lemma. The tree model constructed from a well-formed page table is also well-formed.
    pub proof fn lemma_wf_implies_node_wf(self)
        requires
            self.wf(),
        ensures
            self@.root.wf(),
    {
        self.lemma_construct_node_wf(self.pt_mem.root, 0);
    }

    /// Lemma. The tree model constructed from a well-formed and all_nonempty page table is also all_nonempty.
    pub proof fn lemma_all_nonempty_implies_node_all_nonempty(self)
        requires
            self.wf(),
            self.all_nonempty(),
        ensures
            self@.root.all_nonempty(),
    {
        self.lemma_construct_node_all_nonempty(self.pt_mem.root, 0);
    }

    /// Lemma. The tree model constructed from an empty page table is also empty.
    pub proof fn lemma_empty_implies_node_empty(self)
        requires
            self.wf(),
            self.is_table_empty(self.pt_mem.root),
        ensures
            self@.root.empty(),
    {
        self.lemma_construct_node_empty(self.pt_mem.root);
    }

    /// Lemma. The chain returned by `collect_table_chain` is well-formed: each address
    /// corresponds to a valid table, table levels increase by one, and consecutive
    /// tables are linked via the PTE at the corresponding index.
    pub proof fn lemma_table_chain_entries_valid(
        self,
        vaddr: SpecVAddr,
        base: SpecPAddr,
        level: nat,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
        ensures
            ({
                let tables = self.collect_table_chain(vaddr, base, level);
                &&& forall|i|
                    #![auto]
                    0 <= i < tables.len() ==> self.pt_mem.contains_table_with_level(
                        tables[i],
                        level + i as nat,
                    )
                &&& forall|i|
                    0 <= i < tables.len() - 1 ==> {
                        let idx = self.constants.arch.pte_index(vaddr, level + i as nat);
                        let pte = E::spec_from_u64(self.pt_mem.read(#[trigger] tables[i], idx));
                        self.pte_points_to_table(pte, level + i as nat) && pte.spec_addr()
                            == tables[i + 1]
                    }
            }),
        decreases self.constants.arch.level_count() - level,
    {
        let tables = self.collect_table_chain(vaddr, base, level);
        let idx = self.constants.arch.pte_index(vaddr, level);
        assert(self.pt_mem.accessible(base, idx));
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));

        if self.pte_points_to_table(pte, level) {
            let sub_tables = self.collect_table_chain(vaddr, pte.spec_addr(), level + 1);
            assert(sub_tables == tables.skip(1));
            // PTE points to a child table: continue walk into the child table
            self.lemma_table_chain_entries_valid(vaddr, pte.spec_addr(), level + 1);
        }
    }

    /// Lemma. All tables in `collect_table_chain(vaddr, base, level)` have `pt_mem.level >= level`.
    /// Consequently, a table at a strictly lower level cannot appear in the chain.
    pub proof fn lemma_chain_level_ge(
        self,
        vaddr: SpecVAddr,
        base: SpecPAddr,
        level: nat,
        base2: SpecPAddr,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
            self.collect_table_chain(vaddr, base, level).contains(base2),
        ensures
            self.pt_mem.level(base2) >= level,
    {
        self.lemma_table_chain_entries_valid(vaddr, base, level);
        let tables = self.collect_table_chain(vaddr, base, level);
        let i = choose|i| 0 <= i < tables.len() && tables[i] == base2;
        assert(self.pt_mem.contains_table_with_level(tables[i], level + i as nat));
    }

    /// Lemma. Any table at the chain's starting level that appears in
    /// `collect_table_chain(vaddr, head, level)` must equal `head`.
    /// Consequence: a table at level `level` that differs from `head` cannot be in the chain.
    pub proof fn lemma_table_at_chain_start_level_is_head(
        self,
        vaddr: SpecVAddr,
        head: SpecPAddr,
        level: nat,
        base2: SpecPAddr,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(head, level),
            level < self.constants.arch.level_count(),
            self.collect_table_chain(vaddr, head, level).contains(base2),
            self.pt_mem.contains_table_with_level(base2, level),
        ensures
            base2 == head,
    {
        self.lemma_table_chain_entries_valid(vaddr, head, level);
        let tables = self.collect_table_chain(vaddr, head, level);
        let i = choose|i| 0 <= i < tables.len() && tables[i] == base2;
        assert(self.pt_mem.contains_table_with_level(tables[i], level + i as nat));
        assert(tables[0] == head);
    }

    /// Lemma. An entry at `idx2` in `base` that points to a table but is not the index
    /// chosen by `vaddr` cannot appear in the chain collected for `vaddr`.
    pub proof fn lemma_other_index_not_in_chain(
        self,
        vaddr: SpecVAddr,
        base: SpecPAddr,
        level: nat,
        idx2: nat,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
            self.pt_mem.accessible(base, idx2),
            idx2 != self.constants.arch.pte_index(vaddr, level),
            self.pte_points_to_table(E::spec_from_u64(self.pt_mem.read(base, idx2)), level),
        ensures
            !self.collect_table_chain(vaddr, base, level).contains(
                E::spec_from_u64(self.pt_mem.read(base, idx2)).spec_addr(),
            ),
    {
        let idx = self.constants.arch.pte_index(vaddr, level);
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
        let pte2 = E::spec_from_u64(self.pt_mem.read(base, idx2));
        let tables = self.collect_table_chain(vaddr, base, level);
        self.lemma_table_chain_entries_valid(vaddr, base, level);

        if tables.contains(pte2.spec_addr()) {
            // Assume pte2's address in the collected chain
            assert(pte2.spec_addr() != base);
            assert(tables[0] == base);
            let i = choose|i| 0 <= i < tables.len() && tables[i] == pte2.spec_addr();
            assert(i > 0);

            let idx3 = self.constants.arch.pte_index(vaddr, (level + i - 1) as nat);
            assert(self.pt_mem.accessible(tables[i - 1], idx3));
            let pte3 = E::spec_from_u64(self.pt_mem.read(tables[i - 1], idx3));
            assert(self.pte_points_to_table(pte3, (level + i - 1) as nat));
            // Found 2 pte points to the same table — derive contradiction
            assert(pte3.spec_addr() == pte2.spec_addr());
            assert(false);
        }
    }

    /// Lemma. If `base2` is not in the chain collected for `vaddr` starting at `base`, then
    /// the child table addressed by the PTE at `base2[idx2]` is also not in that chain.
    pub proof fn lemma_table_not_in_chain_implies_child_not_in_chain(
        self,
        vaddr: SpecVAddr,
        base: SpecPAddr,
        level: nat,
        base2: SpecPAddr,
        idx2: nat,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
            self.pt_mem.accessible(base2, idx2),
            self.pt_mem.level(base2) >= level,
            self.pte_points_to_table(
                E::spec_from_u64(self.pt_mem.read(base2, idx2)),
                self.pt_mem.level(base2),
            ),
            !self.collect_table_chain(vaddr, base, level).contains(base2),
        ensures
            !self.collect_table_chain(vaddr, base, level).contains(
                E::spec_from_u64(self.pt_mem.read(base2, idx2)).spec_addr(),
            ),
    {
        let tables = self.collect_table_chain(vaddr, base, level);
        self.lemma_table_chain_entries_valid(vaddr, base, level);

        let pte2 = E::spec_from_u64(self.pt_mem.read(base2, idx2));
        if tables.contains(pte2.spec_addr()) {
            // Assume pte2's address in the collected chain
            assert(pte2.spec_addr() != base);
            assert(tables[0] == base);
            let i = choose|i| 0 <= i < tables.len() && tables[i] == pte2.spec_addr();
            let base3 = tables[i - 1];
            assert(tables.contains(base3));
            let level3 = self.pt_mem.level(base3);
            let idx3 = self.constants.arch.pte_index(vaddr, level3);
            assert(self.pt_mem.accessible(base3, idx3));

            let pte3 = E::spec_from_u64(self.pt_mem.read(base3, idx3));
            assert(self.pte_points_to_table(pte3, level3));
            // Found 2 pte points to the same table — derive contradiction
            assert(pte3.spec_addr() != pte2.spec_addr());
            assert(false);
        }
    }

    /// Lemma. The specification-level walk is consistent with the node model traversal
    /// via `PTTreeNode::visit`.
    pub proof fn lemma_walk_consistent_with_model(
        self,
        vaddr: SpecVAddr,
        base: SpecPAddr,
        level: nat,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
        ensures
            ({
                let (pte, level2) = self.walk(vaddr, base, level);
                let node = self.construct_node(base, level);
                let path = PTTreePath::from_vaddr(
                    vaddr,
                    self.constants.arch,
                    level,
                    (self.constants.arch.level_count() - 1) as nat,
                );
                let visited = node.visit(path);
                // This last entry returned by `visit` is consistent with
                // the page table entry returned by `walk`.
                level2 == level + visited.len() - 1 && visited.last() == if pte.spec_valid() {
                    NodeEntry::Frame(self.pte_to_frame(pte, level2))
                } else {
                    NodeEntry::Empty
                }
            }),
        decreases self.constants.arch.level_count() - level,
    {
        let (pte, level2) = self.walk(vaddr, base, level);
        let node = self.construct_node(base, level);
        self.construct_node_facts(base, level);

        let arch = self.constants.arch;
        let end = (arch.level_count() - 1) as nat;
        let path = PTTreePath::from_vaddr(vaddr, arch, level, end);
        // Precondition of `visit`: node.wf and path.valid
        self.lemma_construct_node_wf(base, level);
        let visited = node.visit(path);

        let (idx, remain) = path.step();
        let entry = node.entries[idx as int];
        assert(self.pt_mem.accessible(base, idx));

        if path.len() <= 1 {
            assert(visited == Seq::new(1, |_i| entry));
        } else {
            if let NodeEntry::Node(subnode) = entry {
                let pte2 = E::spec_from_u64(self.pt_mem.read(base, idx));
                // `pte2` points to a subtable
                let subtable_base = pte2.spec_addr();
                // Recursive visit from the subtable
                self.lemma_walk_consistent_with_model(vaddr, subtable_base, level + 1);
                PTTreePath::lemma_from_vaddr_step(vaddr, arch, level, end);
            }
        }
    }

    /// Lemma. Allocating an intermediate table preserves wf.
    pub proof fn lemma_alloc_intermediate_table_preserves_wf(
        self,
        base: SpecPAddr,
        level: nat,
        idx: nat,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level + 1 < self.constants.arch.level_count(),
            self.pt_mem.accessible(base, idx),
            !E::spec_from_u64(self.pt_mem.read(base, idx)).spec_valid(),
        ensures
            ({
                let (pt_mem, new_base) = self.pt_mem.alloc_table(level + 1);
                let pt_mem = pt_mem.write(
                    base,
                    idx,
                    E::spec_new(new_base, MemAttr::spec_default(), false).spec_to_u64(),
                );
                Self::new(pt_mem, self.constants).wf()
            }),
    {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        let (pt_mem, new_base) = self.pt_mem.alloc_table(level + 1);
        let pt_mem = pt_mem.write(
            base,
            idx,
            E::spec_new(new_base, MemAttr::spec_default(), false).spec_to_u64(),
        );
        let s2 = Self::new(pt_mem, self.constants);

        assert forall|base2: SpecPAddr, idx2: nat| pt_mem.accessible(base2, idx2) implies {
            let level2 = pt_mem.level(base2);
            let pte = E::spec_from_u64(pt_mem.read(base2, idx2));
            let addr = pte.spec_addr();
            &&& (level2 == s2.constants.arch.level_count() - 1 && pte.spec_valid())
                ==> !pte.spec_huge()
            &&& s2.pte_points_to_table(pte, level2) ==> {
                &&& addr != pt_mem.root
                &&& pt_mem.contains_table(addr)
                &&& pt_mem.level(addr) == level2 + 1
            }
            &&& s2.pte_points_to_frame(pte, level2) ==> {
                addr.aligned(s2.constants.arch.frame_size(level2).as_nat())
            }
        } by {
            let level2 = pt_mem.level(base2);
            let val = pt_mem.read(base2, idx2);
            let pte = E::spec_from_u64(val);

            if base2 == base && idx2 == idx {
                // `(base2, idx2)` is the entry just inserted
                E::lemma_eq_by_u64(pte, E::spec_new(new_base, MemAttr::spec_default(), false));
            } else {
                if base2 == new_base {
                    // `base2` is the newly allocated table
                    assert(pte == E::spec_from_u64(0));
                } else {
                    // Entry at `(base2, idx2)` is not updated
                    assert(self.pt_mem.accessible(base2, idx2));
                    assert(val == self.pt_mem.read(base2, idx2));
                    if self.pte_points_to_table(pte, level2) {
                        assert(pte.spec_addr() != pt_mem.root);
                        assert(pt_mem.contains_table(pte.spec_addr()));
                        assert(pt_mem.level(pte.spec_addr()) == level2 + 1);
                    }
                    if level2 == self.constants.arch.level_count() - 1 && pte.spec_valid() {
                        assert(!pte.spec_huge());
                    }
                }
            }
        }
        assert forall|base1: SpecPAddr, idx1: nat, base2: SpecPAddr, idx2: nat|
            pt_mem.accessible(base1, idx1) && pt_mem.accessible(base2, idx2) implies {
            let pte1 = E::spec_from_u64(pt_mem.read(base1, idx1));
            let pte2 = E::spec_from_u64(pt_mem.read(base2, idx2));
            ({
                &&& s2.pte_points_to_table(pte1, pt_mem.level(base1))
                &&& s2.pte_points_to_table(pte2, pt_mem.level(base2))
            }) ==> {
                ||| base1 == base2 && idx1 == idx2
                ||| (pte1.spec_addr() != pte2.spec_addr())
            }
        } by {
            let pte1 = E::spec_from_u64(pt_mem.read(base1, idx1));
            let pte2 = E::spec_from_u64(pt_mem.read(base2, idx2));
            if s2.pte_points_to_table(pte1, pt_mem.level(base1)) && s2.pte_points_to_table(
                pte2,
                pt_mem.level(base2),
            ) {
                assert(self.pt_mem.accessible(base1, idx1));
                assert(self.pt_mem.accessible(base2, idx2));
                if base1 == base && idx1 == idx {
                    if !(base2 == base && idx2 == idx) {
                        // `base1` is the newly inserted entry, `base2` is not
                        assert(pte1.spec_addr() == new_base);
                        assert(pte2.spec_addr() != new_base);
                    }
                } else {
                    if base2 == base && idx2 == idx {
                        // `base2` is the newly inserted entry, `base1` is not
                        assert(pte1.spec_addr() != new_base);
                        assert(pte2.spec_addr() == new_base);
                    }
                }
            }
        }
    }

    /// Lemma. `insert` does not affect existing tables.
    pub proof fn lemma_insert_preserves_old_tables(
        self,
        vbase: SpecVAddr,
        base: SpecPAddr,
        level: nat,
        target_level: nat,
        new_pte: E,
        base2: SpecPAddr,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level <= target_level < self.constants.arch.level_count(),
            self.pte_valid_frame(new_pte, target_level),
            self.pt_mem.contains_table(base2),
        ensures
            self.insert(vbase, base, level, target_level, new_pte).0.pt_mem.contains_table(base2),
            self.insert(vbase, base, level, target_level, new_pte).0.pt_mem.level(base2)
                == self.pt_mem.level(base2),
        decreases target_level - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if level < target_level {
            if pte.spec_valid() {
                if !pte.spec_huge() {
                    self.lemma_insert_preserves_wf(
                        vbase,
                        pte.spec_addr(),
                        level + 1,
                        target_level,
                        new_pte,
                    );
                    self.lemma_insert_preserves_old_tables(
                        vbase,
                        pte.spec_addr(),
                        level + 1,
                        target_level,
                        new_pte,
                        base2,
                    )
                }
            } else {
                let (pt_mem, new_base) = self.pt_mem.alloc_table(level + 1);
                let pt_mem = pt_mem.write(
                    base,
                    idx,
                    E::spec_new(new_base, MemAttr::spec_default(), false).spec_to_u64(),
                );
                self.lemma_alloc_intermediate_table_preserves_wf(base, level, idx);
                // Ensures `pt_mem` after `alloc_table` satisfies the wf
                Self::new(pt_mem, self.constants).lemma_insert_preserves_old_tables(
                    vbase,
                    new_base,
                    level + 1,
                    target_level,
                    new_pte,
                    base2,
                );
            }
        }
    }

    /// Lemma. `insert` does not change the root of the page table.
    pub proof fn lemma_insert_preserves_root(
        self,
        vbase: SpecVAddr,
        base: SpecPAddr,
        level: nat,
        target_level: nat,
        new_pte: E,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level <= target_level < self.constants.arch.level_count(),
            self.pte_valid_frame(new_pte, target_level),
        ensures
            self.insert(vbase, base, level, target_level, new_pte).0.pt_mem.root
                == self.pt_mem.root,
        decreases target_level - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if level < target_level {
            if pte.spec_valid() {
                if !pte.spec_huge() {
                    // Recursively insert into the next table
                    self.lemma_insert_preserves_root(
                        vbase,
                        pte.spec_addr(),
                        level + 1,
                        target_level,
                        new_pte,
                    )
                }
            } else {
                // Allocate intermediate table
                let (pt_mem, new_base) = self.pt_mem.alloc_table(level + 1);
                let pt_mem = pt_mem.write(
                    base,
                    idx,
                    E::spec_new(new_base, MemAttr::spec_default(), false).spec_to_u64(),
                );
                // `s2` is the state after allocating an intermediate table
                let s2 = Self::new(pt_mem, self.constants);

                self.lemma_alloc_intermediate_table_preserves_wf(base, level, idx);
                assert(s2.wf());
                s2.lemma_insert_preserves_root(vbase, new_base, level + 1, target_level, new_pte)
            }
        }
    }

    /// Lemma. Inserting an entry using `insert` preserves the page table wf.
    pub proof fn lemma_insert_preserves_wf(
        self,
        vbase: SpecVAddr,
        base: SpecPAddr,
        level: nat,
        target_level: nat,
        new_pte: E,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level <= target_level < self.constants.arch.level_count(),
            self.pte_valid_frame(new_pte, target_level),
        ensures
            self.insert(vbase, base, level, target_level, new_pte).0.constants == self.constants,
            self.insert(vbase, base, level, target_level, new_pte).0.wf(),
        decreases target_level - level,
    {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        let inserted = self.insert(vbase, base, level, target_level, new_pte).0;
        let idx = self.constants.arch.pte_index(vbase, level);
        assert(self.pt_mem.accessible(base, idx));
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));

        if level < target_level {
            if pte.spec_valid() {
                if !pte.spec_huge() {
                    // Recursively insert into the next table
                    self.lemma_insert_preserves_wf(
                        vbase,
                        pte.spec_addr(),
                        level + 1,
                        target_level,
                        new_pte,
                    )
                }
            } else {
                // Allocate intermediate table
                let (pt_mem, new_base) = self.pt_mem.alloc_table(level + 1);
                let pt_mem = pt_mem.write(
                    base,
                    idx,
                    E::spec_new(new_base, MemAttr::spec_default(), false).spec_to_u64(),
                );
                // `s2` is the state after allocating an intermediate table
                let s2 = Self::new(pt_mem, self.constants);

                self.lemma_alloc_intermediate_table_preserves_wf(base, level, idx);
                s2.lemma_insert_preserves_wf(vbase, new_base, level + 1, target_level, new_pte);
            }
        } else {
            if inserted != self {
                assert(inserted.pt_mem == self.pt_mem.write(base, idx, new_pte.spec_to_u64()));
                // Inserting the new entry preserves wf
                assert forall|base2: SpecPAddr, idx2: nat|
                    inserted.pt_mem.accessible(base2, idx2) implies {
                    let level2 = inserted.pt_mem.level(base2);
                    let pte = E::spec_from_u64(inserted.pt_mem.read(base2, idx2));
                    let addr = pte.spec_addr();
                    &&& (level2 == inserted.constants.arch.level_count() - 1 && pte.spec_valid())
                        ==> !pte.spec_huge()
                    &&& inserted.pte_points_to_table(pte, level2) ==> {
                        &&& addr != inserted.pt_mem.root
                        &&& inserted.pt_mem.contains_table(addr)
                        &&& inserted.pt_mem.level(addr) == level2 + 1
                    }
                    &&& inserted.pte_points_to_frame(pte, level2) ==> {
                        addr.aligned(inserted.constants.arch.frame_size(level2).as_nat())
                    }
                } by {
                    let level2 = inserted.pt_mem.level(base2);
                    let val = inserted.pt_mem.read(base2, idx2);
                    let pte = E::spec_from_u64(val);

                    if base2 == base && idx2 == idx {
                        // `(base2, idx2)` is the entry just inserted
                        E::lemma_eq_by_u64(pte, new_pte);
                    } else {
                        // Entry at `(base2, idx2)` is not updated
                        assert(self.pt_mem.accessible(base2, idx2));
                        assert(val == self.pt_mem.read(base2, idx2));
                        if inserted.pte_points_to_table(pte, level2) {
                            assert(pte.spec_addr() != inserted.pt_mem.root);
                            assert(inserted.pt_mem.contains_table(pte.spec_addr()));
                            assert(inserted.pt_mem.level(pte.spec_addr()) == level2 + 1);
                        }
                        if level2 == self.constants.arch.level_count() - 1 && pte.spec_valid() {
                            assert(!pte.spec_huge());
                        }
                    }
                }
                assert forall|base1: SpecPAddr, idx1: nat, base2: SpecPAddr, idx2: nat|
                    inserted.pt_mem.accessible(base1, idx1) && inserted.pt_mem.accessible(
                        base2,
                        idx2,
                    ) implies {
                    let pte1 = E::spec_from_u64(inserted.pt_mem.read(base1, idx1));
                    let pte2 = E::spec_from_u64(inserted.pt_mem.read(base2, idx2));
                    ({
                        &&& inserted.pte_points_to_table(pte1, inserted.pt_mem.level(base1))
                        &&& inserted.pte_points_to_table(pte2, inserted.pt_mem.level(base2))
                    }) ==> {
                        ||| base1 == base2 && idx1 == idx2
                        ||| (pte1.spec_addr() != pte2.spec_addr())
                    }
                } by {
                    let pte1 = E::spec_from_u64(inserted.pt_mem.read(base1, idx1));
                    let pte2 = E::spec_from_u64(inserted.pt_mem.read(base2, idx2));
                    if inserted.pte_points_to_table(pte1, inserted.pt_mem.level(base1))
                        && inserted.pte_points_to_table(pte2, inserted.pt_mem.level(base2)) {
                        assert(self.pt_mem.accessible(base1, idx1));
                        assert(self.pt_mem.accessible(base2, idx2));
                        if base1 == base && idx1 == idx {
                            if !(base2 == base && idx2 == idx) {
                                // `base1` is the newly inserted entry, `base2` is not
                                assert(pte1.spec_addr() == new_pte.spec_addr());
                                assert(pte2.spec_addr() != new_pte.spec_addr());
                            }
                        } else {
                            if base2 == base && idx2 == idx {
                                // `base2` is the newly inserted entry, `base1` is not
                                assert(pte1.spec_addr() != new_pte.spec_addr());
                                assert(pte2.spec_addr() == new_pte.spec_addr());
                            }
                        }
                    }
                }
            }
        }
    }

    /// Lemma. Inserting an entry using `insert` preserves all_nonempty.
    pub proof fn lemma_insert_preserves_all_nonempty(
        self,
        vbase: SpecVAddr,
        base: SpecPAddr,
        level: nat,
        target_level: nat,
        new_pte: E,
    )
        requires
            self.wf(),
            self.all_nonempty_except(base),
            self.pt_mem.contains_table_with_level(base, level),
            level <= target_level < self.constants.arch.level_count(),
            self.pte_valid_frame(new_pte, target_level),
        ensures
            self.insert(vbase, base, level, target_level, new_pte).1 is Ok ==> self.insert(
                vbase,
                base,
                level,
                target_level,
                new_pte,
            ).0.all_nonempty(),
        decreases target_level - level,
    {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        let (inserted, res) = self.insert(vbase, base, level, target_level, new_pte);
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if res is Ok {
            if level < target_level {
                if pte.spec_valid() {
                    assert(!pte.spec_huge());
                    // Recursively insert into the next table
                    self.lemma_insert_preserves_all_nonempty(
                        vbase,
                        pte.spec_addr(),
                        level + 1,
                        target_level,
                        new_pte,
                    );
                } else {
                    // Allocate intermediate table
                    let (pt_mem, new_base) = self.pt_mem.alloc_table(level + 1);
                    let pt_mem = pt_mem.write(
                        base,
                        idx,
                        E::spec_new(new_base, MemAttr::spec_default(), false).spec_to_u64(),
                    );
                    // `s2` is the state after allocating an intermediate table
                    let s2 = Self::new(pt_mem, self.constants);
                    self.lemma_alloc_intermediate_table_preserves_wf(base, level, idx);

                    // All tables except `new_base` contain at least one valid entry
                    assert forall|base2: SpecPAddr| #[trigger]
                        pt_mem.contains_table(base2) && base2
                            != new_base implies !s2.is_table_empty(base2) by {
                        if base2 == base {
                            assert(s2.pt_mem.read(base2, idx) == E::spec_new(
                                new_base,
                                MemAttr::spec_default(),
                                false,
                            ).spec_to_u64());
                        } else {
                            assert(self.pt_mem.contains_table(base2));
                            assert(!self.is_table_empty(base2));
                            assert(forall|idx2: nat|
                                idx2 < self.constants.arch.entry_count(self.pt_mem.level(base2))
                                    ==> s2.pt_mem.read(base2, idx2) == self.pt_mem.read(
                                    base2,
                                    idx2,
                                ));
                        }
                    }
                    s2.lemma_insert_preserves_all_nonempty(
                        vbase,
                        new_base,
                        level + 1,
                        target_level,
                        new_pte,
                    );
                }
            } else {
                assert(inserted.pt_mem == self.pt_mem.write(base, idx, new_pte.spec_to_u64()));
                // Inserting the new entry makes the table all_nonempty
                assert forall|base2: SpecPAddr|
                    inserted.pt_mem.contains_table(base2) implies !inserted.is_table_empty(
                    base2,
                ) by {
                    if base2 == base {
                        assert(inserted.pt_mem.read(base2, idx) == new_pte.spec_to_u64());
                        E::lemma_from_to_u64_inverse(inserted.pt_mem.read(base2, idx));
                    } else {
                        assert(self.pt_mem.contains_table(base2));
                        assert(!self.is_table_empty(base2));
                        assert(forall|idx2: nat|
                            idx2 < self.constants.arch.entry_count(self.pt_mem.level(base2))
                                ==> inserted.pt_mem.read(base2, idx2) == self.pt_mem.read(
                                base2,
                                idx2,
                            ));
                    }
                }
            }
        }
    }

    /// Lemma. When `insert` allocates an intermediate table, the result must succeed (`Ok`).
    pub proof fn lemma_insert_intermediate_node_results_ok(
        self,
        vbase: SpecVAddr,
        base: SpecPAddr,
        level: nat,
        target_level: nat,
        new_pte: E,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level <= target_level < self.constants.arch.level_count(),
            self.pte_valid_frame(new_pte, target_level),
        ensures
            ({
                let idx = self.constants.arch.pte_index(vbase, level);
                let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
                level < target_level && !pte.spec_valid() ==> self.insert(
                    vbase,
                    base,
                    level,
                    target_level,
                    new_pte,
                ).1 is Ok
            }),
        decreases target_level - level,
    {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
        if level < target_level && !pte.spec_valid() {
            // Allocate intermediate table
            let (pt_mem, new_base) = self.pt_mem.alloc_table(level + 1);
            let pt_mem = pt_mem.write(
                base,
                idx,
                E::spec_new(new_base, MemAttr::spec_default(), false).spec_to_u64(),
            );
            // `s2` is the state after allocating an intermediate table
            let s2 = Self::new(pt_mem, self.constants);
            self.lemma_alloc_intermediate_table_preserves_wf(base, level, idx);
            assert(s2.wf());

            let (_, insert_res) = s2.insert(vbase, new_base, level + 1, target_level, new_pte);
            let idx = s2.constants.arch.pte_index(vbase, level + 1);
            let pte = E::spec_from_u64(s2.pt_mem.read(new_base, idx));
            // New table is empty
            assert(s2.pt_mem.read(new_base, idx) == 0);
            assert(!pte.spec_valid());

            // Recursive proof for the next level
            s2.lemma_insert_intermediate_node_results_ok(
                vbase,
                new_base,
                level + 1,
                target_level,
                new_pte,
            );
        }
    }

    /// Lemma. `insert` only modifies tables that lie on the insert path for `vbase`.
    /// Tables outside the path are preserved unchanged.
    pub proof fn lemma_insert_preserves_tables_outside_chain(
        self,
        vbase: SpecVAddr,
        base: SpecPAddr,
        level: nat,
        target_level: nat,
        new_pte: E,
        base2: SpecPAddr,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level <= target_level < self.constants.arch.level_count(),
            self.pte_valid_frame(new_pte, target_level),
            self.pt_mem.contains_table(base2),
            !self.collect_table_chain(vbase, base, level).contains(base2),
        ensures
            self.insert(vbase, base, level, target_level, new_pte).0.pt_mem.contains_table(base2),
            self.insert(vbase, base, level, target_level, new_pte).0.pt_mem.level(base2)
                == self.pt_mem.level(base2),
            self.insert(vbase, base, level, target_level, new_pte).0.pt_mem.contents[base2]
                == self.pt_mem.contents[base2],
        decreases target_level - level,
    {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        let inserted = self.insert(vbase, base, level, target_level, new_pte).0;
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if level < target_level {
            if pte.spec_valid() {
                // PTE is present: either a huge mapping or a pointer to a next-level table
                if !pte.spec_huge() {
                    // Not a huge mapping: descend into the next-level table
                    assert(self.pt_mem.contains_table(pte.spec_addr()));
                    let tables = self.collect_table_chain(vbase, base, level);
                    let tables2 = self.collect_table_chain(vbase, pte.spec_addr(), level + 1);

                    assert(tables == Seq::new(1, |_i| base).add(tables2));
                    lemma_not_in_seq_implies_not_in_subseq(tables, tables2, base, base2);
                    assert(!tables2.contains(base2));
                    self.lemma_insert_preserves_tables_outside_chain(
                        vbase,
                        pte.spec_addr(),
                        level + 1,
                        target_level,
                        new_pte,
                        base2,
                    )
                }
            } else {
                // Allocate intermediate table — create a new table and link it from `base` via the PTE
                let (pt_mem, new_base) = self.pt_mem.alloc_table(level + 1);
                let pt_mem = pt_mem.write(
                    base,
                    idx,
                    E::spec_new(new_base, MemAttr::spec_default(), false).spec_to_u64(),
                );
                // `s2` is the state after allocating an intermediate table
                let s2 = Self::new(pt_mem, self.constants);
                self.lemma_alloc_intermediate_table_preserves_wf(base, level, idx);
                assert(s2.wf());

                let pte = E::spec_new(new_base, MemAttr::spec_default(), false);
                let tables = s2.collect_table_chain(vbase, base, level);
                let tables2 = s2.collect_table_chain(vbase, pte.spec_addr(), level + 1);
                assert(s2.pt_mem.read(base, idx) == pte.spec_to_u64());
                E::lemma_eq_by_u64(E::spec_from_u64(s2.pt_mem.read(base, idx)), pte);
                assert(s2.pte_points_to_table(pte, level));

                assert(tables == Seq::new(1, |_i| base).add(tables2));
                lemma_not_in_seq_implies_not_in_subseq(tables, tables2, base, base2);
                assert(!tables2.contains(base2));
                s2.lemma_insert_preserves_tables_outside_chain(
                    vbase,
                    new_base,
                    level + 1,
                    target_level,
                    new_pte,
                    base2,
                );
            }
        } else {
            if inserted != self {
                // `insert` modifies the entry at `(base, idx)` but preserves all other entries in the same table
                assert(inserted.pt_mem == self.pt_mem.write(base, idx, new_pte.spec_to_u64()));
                let chain = self.collect_table_chain(vbase, base, level);
                assert(chain.contains(chain[0]));
                assert(base2 != base);
            }
        }
    }

    /// Lemma. `insert` does not change the constructed node for nodes outside the insertion path
    /// — structural node representations remain equal for nodes not on the path.
    pub proof fn lemma_insert_preserves_unrelated_node(
        self,
        vbase: SpecVAddr,
        base: SpecPAddr,
        level: nat,
        target_level: nat,
        new_pte: E,
        base2: SpecPAddr,
        level2: nat,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            self.pt_mem.contains_table(base2),
            self.pt_mem.level(base2) == level2,
            level <= target_level < self.constants.arch.level_count(),
            level <= level2 < self.constants.arch.level_count(),
            self.pte_valid_frame(new_pte, target_level),
            !self.collect_table_chain(vbase, base, level).contains(base2),
        ensures
            self.construct_node(base2, level2) == self.insert(
                vbase,
                base,
                level,
                target_level,
                new_pte,
            ).0.construct_node(base2, level2),
        decreases self.constants.arch.level_count() - level2,
    {
        let s2 = self.insert(vbase, base, level, target_level, new_pte).0;
        self.lemma_insert_preserves_wf(vbase, base, level, target_level, new_pte);
        self.lemma_insert_preserves_tables_outside_chain(
            vbase,
            base,
            level,
            target_level,
            new_pte,
            base2,
        );
        assert(self.pt_mem.contents[base2] == s2.pt_mem.contents[base2]);

        let node = self.construct_node(base2, level2);
        self.construct_node_facts(base2, level2);
        let node2 = s2.construct_node(base2, level2);
        s2.construct_node_facts(base2, level2);

        assert(node.entries.len() == node2.entries.len());
        assert forall|i: int| 0 <= i < self.constants.arch.entry_count(level2) implies {
            node.entries[i] == node2.entries[i]
        } by {
            let entry = node.entries[i];
            let entry2 = node2.entries[i];
            let pte = E::spec_from_u64(self.pt_mem.read(base2, i as nat));
            E::lemma_from_u64_wf(self.pt_mem.read(base2, i as nat));
            assert(self.pt_mem.accessible(base2, i as nat));
            let pte2 = E::spec_from_u64(s2.pt_mem.read(base2, i as nat));
            E::lemma_eq_by_u64(pte, pte2);

            match entry {
                NodeEntry::Node(node) => {
                    assert(self.pte_points_to_table(pte, level2));
                    assert(self.pt_mem.contains_table(pte.spec_addr()));
                    self.lemma_table_not_in_chain_implies_child_not_in_chain(
                        vbase,
                        base,
                        level,
                        base2,
                        i as nat,
                    );
                    self.lemma_insert_preserves_unrelated_node(
                        vbase,
                        base,
                        level,
                        target_level,
                        new_pte,
                        pte.spec_addr(),
                        level2 + 1,
                    );
                },
                NodeEntry::Frame(frame) => {
                    assert(self.pte_points_to_frame(pte, level2));
                },
                NodeEntry::Empty => {
                    assert(!pte.spec_valid());
                },
            }
        }
        assert(node.entries == node2.entries);
    }

    /// Lemma. The implementation-level insertion is consistent with the tree model.
    pub proof fn lemma_insert_consistent_with_model(
        self,
        vbase: SpecVAddr,
        base: SpecPAddr,
        level: nat,
        target_level: nat,
        new_pte: E,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level <= target_level < self.constants.arch.level_count(),
            self.pte_valid_frame(new_pte, target_level),
        ensures
            ({
                let (s2, res) = self.insert(vbase, base, level, target_level, new_pte);
                let node = self.construct_node(base, level);
                let node2 = s2.construct_node(base, level);
                let path = PTTreePath::from_vaddr(vbase, self.constants.arch, level, target_level);
                (node2, res) == node.insert(path, self.pte_to_frame(new_pte, target_level))
            }),
        decreases target_level - level,
    {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        let new_frame = self.pte_to_frame(new_pte, target_level);
        let (s2, res) = self.insert(vbase, base, level, target_level, new_pte);
        self.lemma_insert_preserves_wf(vbase, base, level, target_level, new_pte);
        self.lemma_insert_preserves_old_tables(vbase, base, level, target_level, new_pte, base);

        let node = self.construct_node(base, level);
        let node2 = s2.construct_node(base, level);
        self.construct_node_facts(base, level);
        s2.construct_node_facts(base, level);

        let arch = self.constants.arch;
        let path = PTTreePath::from_vaddr(vbase, arch, level, target_level);
        self.lemma_construct_node_wf(base, level);
        s2.lemma_construct_node_wf(base, level);

        let (idx, remain) = path.step();
        let entry = node.entries[idx as int];
        assert(self.pt_mem.accessible(base, idx));
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));

        let right = node.insert(path, new_frame).0;
        node.lemma_insert_preserves_wf(path, new_frame);

        if level >= target_level {
            if !pte.spec_valid() {
                E::lemma_eq_by_u64(E::spec_from_u64(s2.pt_mem.read(base, idx)), new_pte);
                // Update `pte` to `new_pte`, empty entry to frame
                assert(right == node.update(idx, NodeEntry::Frame(new_frame)));
                assert forall|i| 0 <= i < node2.entries.len() implies node2.entries[i]
                    == right.entries[i] by {
                    if i == idx {
                        // Entry `i` is the subtree constructed from `subtable_base`
                        assert(node2.entries[i] == NodeEntry::Frame(new_frame));
                    } else {
                        // Other entries are unchanged
                        if node2.entries[i] is Node {
                            let pte_i = E::spec_from_u64(self.pt_mem.read(base, i as nat));
                            assert(self.pt_mem.accessible(base, i as nat));
                            if self.pte_points_to_table(pte_i, level) {
                                assert(self.pt_mem.contains_table(pte_i.spec_addr()));
                                self.lemma_other_index_not_in_chain(vbase, base, level, i as nat);
                                self.lemma_insert_preserves_unrelated_node(
                                    vbase,
                                    base,
                                    level,
                                    target_level,
                                    new_pte,
                                    pte_i.spec_addr(),
                                    level + 1,
                                );
                            }
                        } else {
                            assert(node2.entries[i] == node.entries[i]);
                        }
                    }
                }
                assert(node2.entries == right.entries);
            }
        } else {
            if pte.spec_valid() {
                if !pte.spec_huge() {
                    // `pte` points to a subtable
                    let subtable_base = pte.spec_addr();
                    let subnode: PTTreeNode = entry->Node_0;

                    let new_subnode = subnode.insert(remain, new_frame).0;
                    assert(s2 == self.insert(
                        vbase,
                        subtable_base,
                        level + 1,
                        target_level,
                        new_pte,
                    ).0);
                    // Recursive call shows subnode is updated according to model
                    self.lemma_insert_consistent_with_model(
                        vbase,
                        subtable_base,
                        level + 1,
                        target_level,
                        new_pte,
                    );
                    PTTreePath::lemma_from_vaddr_step(vbase, arch, level, target_level);
                    assert(s2.construct_node(subtable_base, level + 1) == new_subnode);
                    assert(right == node.update(idx, NodeEntry::Node(new_subnode)));

                    // The content of table `base` is unchanged
                    self.lemma_table_chain_entries_valid(vbase, subtable_base, level + 1);
                    self.lemma_insert_preserves_tables_outside_chain(
                        vbase,
                        subtable_base,
                        level + 1,
                        target_level,
                        new_pte,
                        base,
                    );
                    assert(s2.pt_mem.contents[base] == self.pt_mem.contents[base]);

                    assert forall|i| 0 <= i < node2.entries.len() implies node2.entries[i]
                        == right.entries[i] by {
                        E::lemma_eq_by_u64(
                            E::spec_from_u64(s2.pt_mem.read(base, i as nat)),
                            E::spec_from_u64(self.pt_mem.read(base, i as nat)),
                        );
                        if i == idx {
                            // Entry `i` is the subtree constructed from `subtable_base`
                            assert(node2.entries[i] == NodeEntry::Node(
                                s2.construct_node(subtable_base, level + 1),
                            ));
                        } else {
                            // Other entries are unchanged
                            let pte_i = E::spec_from_u64(self.pt_mem.read(base, i as nat));
                            assert(self.pt_mem.accessible(base, i as nat));
                            if self.pte_points_to_table(pte_i, level) {
                                assert(self.pt_mem.contains_table(pte_i.spec_addr()));
                                self.lemma_other_index_not_in_chain(vbase, base, level, i as nat);
                                self.lemma_insert_preserves_unrelated_node(
                                    vbase,
                                    base,
                                    level,
                                    target_level,
                                    new_pte,
                                    pte_i.spec_addr(),
                                    level + 1,
                                );
                            }
                            assert(node2.entries[i] == node.entries[i]);
                        }
                    }
                    assert(node2.entries == right.entries);
                }
            } else {
                let (allocated, new_base) = self.pt_mem.alloc_table(level + 1);
                let written = allocated.write(
                    base,
                    idx,
                    E::spec_new(new_base, MemAttr::spec_default(), false).spec_to_u64(),
                );
                let subtable_base = new_base;
                self.lemma_alloc_intermediate_table_preserves_wf(base, level, idx);

                // sm is the state after allocating a new intermediate table
                let sm = Self::new(written, self.constants);
                let subnode = PTTreeNode::new(self.constants, level + 1);
                E::lemma_eq_by_u64(
                    E::spec_from_u64(sm.pt_mem.read(base, idx)),
                    E::spec_new(new_base, MemAttr::spec_default(), false),
                );
                let pte = E::spec_from_u64(sm.pt_mem.read(base, idx));

                sm.construct_node_facts(base, level);
                assert(sm.pte_points_to_table(pte, level));
                assert(sm.construct_node(base, level).entries[idx as int] == NodeEntry::Node(
                    sm.construct_node(new_base, level + 1),
                ));

                sm.construct_node_facts(new_base, level + 1);
                assert(sm.construct_node(new_base, level + 1).entries == subnode.entries);
                assert(sm.construct_node(new_base, level + 1) == subnode);

                let new_subnode = subnode.insert(remain, new_frame).0;
                assert(s2 == sm.insert(vbase, new_base, level + 1, target_level, new_pte).0);
                // Recursive call shows subnode is updated according to model
                sm.lemma_insert_consistent_with_model(
                    vbase,
                    subtable_base,
                    level + 1,
                    target_level,
                    new_pte,
                );
                PTTreePath::lemma_from_vaddr_step(vbase, arch, level, target_level);
                sm.lemma_insert_preserves_old_tables(
                    vbase,
                    subtable_base,
                    level + 1,
                    target_level,
                    new_pte,
                    subtable_base,
                );
                s2.construct_node_facts(subtable_base, level + 1);
                assert(s2.construct_node(subtable_base, level + 1) == new_subnode);
                assert(right == node.update(idx, NodeEntry::Node(new_subnode)));

                // The content of table `base` is unchanged
                sm.lemma_insert_preserves_tables_outside_chain(
                    vbase,
                    new_base,
                    level + 1,
                    target_level,
                    new_pte,
                    base,
                );
                assert(s2.pt_mem.contents[base] == sm.pt_mem.contents[base]);
                assert forall|i| 0 <= i < node2.entries.len() implies node2.entries[i]
                    == right.entries[i] by {
                    if i == idx {
                        // Entry `i` is the subtree constructed from `subtable_base`
                        assert(node2.entries[i] == NodeEntry::Node(new_subnode));
                    } else {
                        // Other entries are unchanged
                        if node2.entries[i] is Node {
                            let pte_i = E::spec_from_u64(self.pt_mem.read(base, i as nat));
                            assert(self.pt_mem.accessible(base, i as nat));
                            if self.pte_points_to_table(pte_i, level) {
                                assert(self.pt_mem.contains_table(pte_i.spec_addr()));
                                self.lemma_other_index_not_in_chain(vbase, base, level, i as nat);
                                self.lemma_insert_preserves_unrelated_node(
                                    vbase,
                                    base,
                                    level,
                                    target_level,
                                    new_pte,
                                    pte_i.spec_addr(),
                                    level + 1,
                                );
                            }
                        } else {
                            assert(node2.entries[i] == sm.construct_node(base, level).entries[i]);
                            assert(node2.entries[i] == node.entries[i]);
                        }
                    }
                }
                assert(node2.entries == right.entries);
            }
        }
    }

    /// Lemma. Removing a page table entry using `remove` maintains the page table wf.
    pub proof fn lemma_remove_preserves_wf(self, vbase: SpecVAddr, base: SpecPAddr, level: nat)
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
        ensures
            self.remove(vbase, base, level).0.wf(),
            self.remove(vbase, base, level).0.constants == self.constants,
        decreases self.constants.arch.level_count() - level,
    {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        let removed = self.remove(vbase, base, level).0;
        let idx = self.constants.arch.pte_index(vbase, level);
        assert(self.pt_mem.accessible(base, idx));
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));

        if self.pte_points_to_table(pte, level) {
            self.lemma_remove_preserves_wf(vbase, pte.spec_addr(), level + 1)
        } else {
            if removed != self {
                assert(removed.pt_mem == self.pt_mem.write(
                    base,
                    idx,
                    E::spec_empty().spec_to_u64(),
                ));
                // Removing the entry preserves wf
                assert forall|base2: SpecPAddr, idx2: nat|
                    removed.pt_mem.accessible(base2, idx2) implies {
                    let level2 = removed.pt_mem.level(base2);
                    let pte = E::spec_from_u64(removed.pt_mem.read(base2, idx2));
                    let addr = pte.spec_addr();
                    &&& (level2 == removed.constants.arch.level_count() - 1 && pte.spec_valid())
                        ==> !pte.spec_huge()
                    &&& removed.pte_points_to_table(pte, level2) ==> {
                        &&& addr != removed.pt_mem.root
                        &&& removed.pt_mem.contains_table(addr)
                        &&& removed.pt_mem.level(addr) == level2 + 1
                    }
                    &&& removed.pte_points_to_frame(pte, level2) ==> {
                        addr.aligned(removed.constants.arch.frame_size(level2).as_nat())
                    }
                } by {
                    let level2 = removed.pt_mem.level(base2);
                    let val = removed.pt_mem.read(base2, idx2);
                    let pte = E::spec_from_u64(val);

                    if base2 == base && idx2 == idx {
                        // `(base2, idx2)` is the entry just removed
                        E::lemma_eq_by_u64(pte, E::spec_empty());
                    } else {
                        // Entry at `(base2, idx2)` is not updated
                        assert(self.pt_mem.accessible(base2, idx2));
                        assert(val == self.pt_mem.read(base2, idx2));
                        if removed.pte_points_to_table(pte, level2) {
                            assert(pte.spec_addr() != removed.pt_mem.root);
                            assert(removed.pt_mem.contains_table(pte.spec_addr()));
                            assert(removed.pt_mem.level(pte.spec_addr()) == level2 + 1);
                        }
                        if level2 == self.constants.arch.level_count() - 1 && pte.spec_valid() {
                            assert(!pte.spec_huge());
                        }
                    }
                }
                assert forall|base1: SpecPAddr, idx1: nat, base2: SpecPAddr, idx2: nat|
                    removed.pt_mem.accessible(base1, idx1) && removed.pt_mem.accessible(
                        base2,
                        idx2,
                    ) implies {
                    let pte1 = E::spec_from_u64(removed.pt_mem.read(base1, idx1));
                    let pte2 = E::spec_from_u64(removed.pt_mem.read(base2, idx2));
                    ({
                        &&& removed.pte_points_to_table(pte1, removed.pt_mem.level(base1))
                        &&& removed.pte_points_to_table(pte2, removed.pt_mem.level(base2))
                    }) ==> {
                        ||| base1 == base2 && idx1 == idx2
                        ||| (pte1.spec_addr() != pte2.spec_addr())
                    }
                } by {
                    let pte1 = E::spec_from_u64(removed.pt_mem.read(base1, idx1));
                    let pte2 = E::spec_from_u64(removed.pt_mem.read(base2, idx2));
                    if removed.pte_points_to_table(pte1, removed.pt_mem.level(base1))
                        && removed.pte_points_to_table(pte2, removed.pt_mem.level(base2)) {
                        assert(self.pt_mem.accessible(base1, idx1));
                        assert(self.pt_mem.accessible(base2, idx2));
                        if base1 == base && idx1 == idx {
                            if !(base2 == base && idx2 == idx) {
                                // `base1` is the newly removed entry, `base2` is not
                                assert(pte1.spec_addr() == E::spec_empty().spec_addr());
                                assert(pte2.spec_addr() != E::spec_empty().spec_addr());
                            }
                        } else {
                            if base2 == base && idx2 == idx {
                                // `base2` is the newly removed entry, `base1` is not
                                assert(pte1.spec_addr() != E::spec_empty().spec_addr());
                                assert(pte2.spec_addr() == E::spec_empty().spec_addr());
                            }
                        }
                    }
                }
            }
        }
    }

    /// Lemma. `remove` does not affect existing tables.
    pub proof fn lemma_remove_preserves_old_tables(
        self,
        vbase: SpecVAddr,
        base: SpecPAddr,
        level: nat,
        base2: SpecPAddr,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
            self.pt_mem.contains_table(base2),
        ensures
            self.remove(vbase, base, level).0.pt_mem.contains_table(base2),
            self.remove(vbase, base, level).0.pt_mem.level(base2) == self.pt_mem.level(base2),
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));
        if self.pte_points_to_table(pte, level) {
            self.lemma_remove_preserves_old_tables(vbase, pte.spec_addr(), level + 1, base2)
        }
    }

    /// Lemma. `remove` only modifies tables that lie on the remove path for `vbase`.
    /// Tables outside the path are preserved unchanged.
    pub proof fn lemma_remove_preserves_tables_outside_chain(
        self,
        vbase: SpecVAddr,
        base: SpecPAddr,
        level: nat,
        base2: SpecPAddr,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
            self.pt_mem.contains_table(base2),
            !self.collect_table_chain(vbase, base, level).contains(base2),
        ensures
            self.remove(vbase, base, level).0.pt_mem.contains_table(base2),
            self.remove(vbase, base, level).0.pt_mem.level(base2) == self.pt_mem.level(base2),
            self.remove(vbase, base, level).0.pt_mem.contents[base2] == self.pt_mem.contents[base2],
        decreases self.constants.arch.level_count() - level,
    {
        let removed = self.remove(vbase, base, level).0;
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));
        if self.pte_points_to_table(pte, level) {
            let tables = self.collect_table_chain(vbase, base, level);
            let tables2 = self.collect_table_chain(vbase, pte.spec_addr(), level + 1);
            assert(tables == Seq::new(1, |_i| base).add(tables2));
            lemma_not_in_seq_implies_not_in_subseq(tables, tables2, base, base2);
            assert(!tables2.contains(base2));
            self.lemma_remove_preserves_tables_outside_chain(
                vbase,
                pte.spec_addr(),
                level + 1,
                base2,
            )
        } else {
            if removed != self {
                // `insert` modifies the entry at `(base, idx)` but preserves all other entries in the same table
                assert(removed.pt_mem == self.pt_mem.write(
                    base,
                    idx,
                    E::spec_empty().spec_to_u64(),
                ));
                let chain = self.collect_table_chain(vbase, base, level);
                assert(chain.contains(chain[0]));
                assert(base2 != base);
            }
        }
    }

    /// Lemma. `remove` preserves the set of tables — it only writes entries, never
    /// allocates or deallocates tables. Therefore `removed.pt_mem.tables == self.pt_mem.tables`.
    pub proof fn lemma_remove_preserves_table_set(
        self,
        vbase: SpecVAddr,
        base: SpecPAddr,
        level: nat,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
        ensures
            self.remove(vbase, base, level).0.pt_mem.tables == self.pt_mem.tables,
        decreases self.constants.arch.level_count() - level,
    {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        let removed = self.remove(vbase, base, level).0;
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if pte.spec_valid() {
            if level >= self.constants.arch.level_count() - 1 {
                if vbase.aligned(self.constants.arch.frame_size(level).as_nat()) {
                    assert(removed.pt_mem == self.pt_mem.write(
                        base,
                        idx,
                        E::spec_empty().spec_to_u64(),
                    ));
                }
            } else {
                if pte.spec_huge() {
                    if vbase.aligned(self.constants.arch.frame_size(level).as_nat()) {
                        assert(removed.pt_mem == self.pt_mem.write(
                            base,
                            idx,
                            E::spec_empty().spec_to_u64(),
                        ));
                    }
                } else {
                    self.lemma_remove_preserves_table_set(vbase, pte.spec_addr(), level + 1);
                }
            }
        }
    }

    /// Lemma. `remove` does not change the collected table chain for the same starting point.
    /// The chain `collect_table_chain(vbase, base, level)` is the same before and after `remove`,
    /// because `remove` only modifies leaf entries (non-table-pointers), never intermediate PTEs
    /// that the chain traversal follows.
    pub proof fn lemma_remove_preserves_chain(self, vbase: SpecVAddr, base: SpecPAddr, level: nat)
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
        ensures
            self.collect_table_chain(vbase, base, level) == self.remove(
                vbase,
                base,
                level,
            ).0.collect_table_chain(vbase, base, level),
        decreases self.constants.arch.level_count() - level,
    {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        let removed = self.remove(vbase, base, level).0;
        self.lemma_remove_preserves_wf(vbase, base, level);

        let idx = self.constants.arch.pte_index(vbase, level);
        assert(self.pt_mem.accessible(base, idx));
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));

        if self.pte_points_to_table(pte, level) {
            // remove recurses into pte.spec_addr(); the PTE at (base, idx) is not written
            // so the chain at base follows the same child table
            let child = pte.spec_addr();
            self.lemma_remove_preserves_old_tables(vbase, base, level, child);
            // The content of `base` is unchanged (remove only modifies the chain of the subtable)
            // Actually remove starts at base and recurses — it modifies inside the chain.
            // But the PTE at (base, idx) itself is never written when pte_points_to_table.
            // Specifically: removed = self.remove(vbase, child, level+1).0
            assert(removed == self.remove(vbase, child, level + 1).0);
            // child's chain in `self` vs `removed`:
            self.lemma_remove_preserves_chain(vbase, child, level + 1);
            // The PTE content of `base` at `idx` is same in removed (only subtable is modified)
            // We need: removed.pt_mem.read(base, idx) == self.pt_mem.read(base, idx)
            // This follows because base != child (wf: no self-reference) and
            // lemma_remove_preserves_tables_outside_chain for base w.r.t. child's chain
            let chain2 = self.collect_table_chain(vbase, child, level + 1);
            // base is not in chain2 (base has level `level`, chain2 entries have levels >= level+1)
            assert(!chain2.contains(base)) by {
                if chain2.contains(base) {
                    self.lemma_chain_level_ge(vbase, child, level + 1, base);
                    assert(self.pt_mem.level(base) >= level + 1);
                    assert(false);
                }
            };
            self.lemma_remove_preserves_tables_outside_chain(vbase, child, level + 1, base);
            assert(removed.pt_mem.contents[base] == self.pt_mem.contents[base]);
            let pte_after = E::spec_from_u64(removed.pt_mem.read(base, idx));
            E::lemma_eq_by_u64(pte, pte_after);
            // Now chain for `removed` starting at `base` also follows child
            // and the chain from child is the same by induction
        } else {
            // Not a table pointer: chain is just [base], and removed either == self or wrote (base, idx)
            // Either way, the chain is just [base] both before and after
        }
    }

    /// Lemma. `remove` does not change the root of the page table.
    pub proof fn lemma_remove_preserves_root(self, vbase: SpecVAddr, base: SpecPAddr, level: nat)
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
        ensures
            self.remove(vbase, base, level).0.pt_mem.root == self.pt_mem.root,
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));
        if self.pte_points_to_table(pte, level) {
            self.lemma_remove_preserves_root(vbase, pte.spec_addr(), level + 1)
        }
    }

    /// Lemma. `remove` does not change the construction of a node that is not in the
    /// removal chain.
    pub proof fn lemma_remove_preserves_unrelated_node(
        self,
        vbase: SpecVAddr,
        base: SpecPAddr,
        level: nat,
        base2: SpecPAddr,
        level2: nat,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            self.pt_mem.contains_table(base2),
            self.pt_mem.level(base2) == level2,
            level < self.constants.arch.level_count(),
            level <= level2 < self.constants.arch.level_count(),
            !self.collect_table_chain(vbase, base, level).contains(base2),
        ensures
            self.construct_node(base2, level2) == self.remove(vbase, base, level).0.construct_node(
                base2,
                level2,
            ),
        decreases self.constants.arch.level_count() - level2,
    {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        let s2 = self.remove(vbase, base, level).0;
        self.lemma_remove_preserves_wf(vbase, base, level);
        self.lemma_remove_preserves_tables_outside_chain(vbase, base, level, base2);
        assert(self.pt_mem.contents[base2] == s2.pt_mem.contents[base2]);

        let node = self.construct_node(base2, level2);
        let node2 = s2.construct_node(base2, level2);
        self.construct_node_facts(base2, level2);
        s2.construct_node_facts(base2, level2);

        assert(node.entries.len() == node2.entries.len());
        assert forall|i: int| 0 <= i < self.constants.arch.entry_count(level2) implies {
            node.entries[i] == node2.entries[i]
        } by {
            let entry = node.entries[i];
            let entry2 = node2.entries[i];
            let pte = E::spec_from_u64(self.pt_mem.read(base2, i as nat));
            E::lemma_from_u64_wf(self.pt_mem.read(base2, i as nat));
            assert(self.pt_mem.accessible(base2, i as nat));
            let pte2 = E::spec_from_u64(s2.pt_mem.read(base2, i as nat));
            E::lemma_eq_by_u64(pte, pte2);

            match entry {
                NodeEntry::Node(node_) => {
                    assert(self.pte_points_to_table(pte, level2));
                    assert(self.pt_mem.contains_table(pte.spec_addr()));
                    self.lemma_table_not_in_chain_implies_child_not_in_chain(
                        vbase,
                        base,
                        level,
                        base2,
                        i as nat,
                    );
                    self.lemma_remove_preserves_unrelated_node(
                        vbase,
                        base,
                        level,
                        pte.spec_addr(),
                        level2 + 1,
                    );
                },
                NodeEntry::Frame(frame) => {
                    assert(self.pte_points_to_frame(pte, level2));
                },
                NodeEntry::Empty => {
                    assert(!pte.spec_valid());
                },
            }
        }
        assert(node.entries == node2.entries);
    }

    /// Lemma. The implementation-level removal is consistent with the tree model.
    pub proof fn lemma_remove_consistent_with_model(
        self,
        vbase: SpecVAddr,
        base: SpecPAddr,
        level: nat,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
            vbase.aligned(self.constants.arch.leaf_frame_size().as_nat()),
        ensures
            ({
                let (s2, res) = self.remove(vbase, base, level);
                let node = self.construct_node(base, level);
                let node2 = s2.construct_node(base, level);
                let path = PTTreePath::from_vaddr(
                    vbase,
                    self.constants.arch,
                    level,
                    (self.constants.arch.level_count() - 1) as nat,
                );
                (node2, res) == node.remove(path)
            }),
        decreases self.constants.arch.level_count() - level,
    {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        let s2 = self.remove(vbase, base, level).0;
        self.lemma_remove_preserves_wf(vbase, base, level);
        self.lemma_remove_preserves_old_tables(vbase, base, level, base);

        let node = self.construct_node(base, level);
        let node2 = s2.construct_node(base, level);
        self.construct_node_facts(base, level);
        s2.construct_node_facts(base, level);

        let arch = self.constants.arch;
        let end = (arch.level_count() - 1) as nat;
        let path = PTTreePath::from_vaddr(vbase, arch, level, end);
        // Precondition of `remove`: node.wf and path.valid
        self.lemma_construct_node_wf(base, level);
        s2.lemma_construct_node_wf(base, level);

        let (idx, remain) = path.step();
        let entry = node.entries[idx as int];
        let entry2 = node2.entries[idx as int];
        assert(self.pt_mem.accessible(base, idx));
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
        let pte2 = E::spec_from_u64(s2.pt_mem.read(base, idx));

        let right = node.remove(path).0;
        node.lemma_remove_preserves_wf(path);

        if pte.spec_valid() {
            if level >= self.constants.arch.level_count() - 1 {
                // Leaf node
                if vbase.aligned(self.constants.arch.frame_size(level).as_nat()) {
                    // Update frame entry to empty
                    assert(s2.pt_mem == self.pt_mem.write(
                        base,
                        idx,
                        E::spec_empty().spec_to_u64(),
                    ));
                    E::lemma_eq_by_u64(pte2, E::spec_empty());
                    assert(entry2 == NodeEntry::Empty);
                    assert(node2.entries == right.entries);
                } else {
                    // Not aligned to frame size, so the entry is not removed
                    assert(s2 == self);
                }
            } else {
                // Intermediate node
                if pte.spec_huge() {
                    if vbase.aligned(self.constants.arch.frame_size(level).as_nat()) {
                        PTTreePath::lemma_from_vaddr_step(vbase, arch, level, end);
                        lemma_aligned_implies_remain_zero(vbase, arch, level, end);
                        assert(remain.is_zero());
                        // Update frame entry to empty
                        assert(s2.pt_mem == self.pt_mem.write(
                            base,
                            idx,
                            E::spec_empty().spec_to_u64(),
                        ));
                        E::lemma_eq_by_u64(pte2, E::spec_empty());
                        assert(right.entries == node.entries.update(idx as int, NodeEntry::Empty));
                        assert forall|i| 0 <= i < node2.entries.len() implies node2.entries[i]
                            == right.entries[i] by {
                            if i == idx {
                                // Entry `i` is updated to empty
                                assert(node2.entries[i] == NodeEntry::Empty);
                                assert(right.entries[i] == NodeEntry::Empty);
                            } else {
                                // Other entries are unchanged
                                if node2.entries[i] is Node {
                                    let pte_i = E::spec_from_u64(self.pt_mem.read(base, i as nat));
                                    assert(self.pt_mem.accessible(base, i as nat));
                                    if self.pte_points_to_table(pte_i, level) {
                                        assert(self.pt_mem.contains_table(pte_i.spec_addr()));
                                        self.lemma_other_index_not_in_chain(
                                            vbase,
                                            base,
                                            level,
                                            i as nat,
                                        );
                                        self.lemma_remove_preserves_unrelated_node(
                                            vbase,
                                            base,
                                            level,
                                            pte_i.spec_addr(),
                                            level + 1,
                                        );
                                    }
                                } else {
                                    assert(node2.entries[i] == node.entries[i]);
                                }
                            }
                        }
                        assert(node2.entries == right.entries);
                    } else {
                        // Not aligned to frame size, so the entry is not removed
                        assert(s2 == self);
                        assert(!remain.is_zero()) by {
                            if remain.is_zero() {
                                PTTreePath::lemma_from_vaddr_step(vbase, arch, level, end);
                                lemma_remain_zero_implies_aligned(vbase, arch, level, end);
                                assert(vbase.aligned(
                                    self.constants.arch.frame_size(level).as_nat(),
                                ));
                            }
                        }
                        assert(node2 == right);
                    }
                } else {
                    // `pte` points to a subtable
                    let subtable_base = pte.spec_addr();
                    let subnode: PTTreeNode = entry->Node_0;
                    let new_subnode = subnode.remove(remain).0;

                    // Recursive remove from the subtable
                    self.lemma_remove_consistent_with_model(vbase, subtable_base, level + 1);
                    PTTreePath::lemma_from_vaddr_step(vbase, arch, level, end);
                    assert(s2.construct_node(subtable_base, level + 1) == new_subnode);
                    assert(right == node.update(idx, NodeEntry::Node(new_subnode)));

                    // The content of table `base` is unchanged
                    self.lemma_table_chain_entries_valid(vbase, subtable_base, level + 1);
                    self.lemma_remove_preserves_tables_outside_chain(
                        vbase,
                        subtable_base,
                        level + 1,
                        base,
                    );
                    assert(s2.pt_mem.contents[base] == self.pt_mem.contents[base]);

                    assert forall|i| 0 <= i < node2.entries.len() implies node2.entries[i]
                        == right.entries[i] by {
                        E::lemma_eq_by_u64(
                            E::spec_from_u64(s2.pt_mem.read(base, i as nat)),
                            E::spec_from_u64(self.pt_mem.read(base, i as nat)),
                        );
                        if i == idx {
                            // Entry `i` is the subtree constructed from `subtable_base`
                            assert(node2.entries[i] == NodeEntry::Node(
                                s2.construct_node(subtable_base, level + 1),
                            ));
                        } else {
                            // Other entries are unchanged
                            let pte_i = E::spec_from_u64(self.pt_mem.read(base, i as nat));
                            assert(self.pt_mem.accessible(base, i as nat));
                            if self.pte_points_to_table(pte_i, level) {
                                assert(self.pt_mem.contains_table(pte_i.spec_addr()));
                                self.lemma_other_index_not_in_chain(vbase, base, level, i as nat);
                                self.lemma_remove_preserves_unrelated_node(
                                    vbase,
                                    base,
                                    level,
                                    pte_i.spec_addr(),
                                    level + 1,
                                );
                            }
                            assert(node2.entries[i] == node.entries[i]);
                        }
                    }
                    assert(node2.entries == right.entries);
                }
            }
        }
    }

    /// Lemma. Deallocating an intermediate table preserves wf.
    pub proof fn lemma_dealloc_intermediate_table_preserves_wf(
        self,
        base: SpecPAddr,
        level: nat,
        idx: nat,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count() - 1,
            self.pt_mem.accessible(base, idx),
            ({
                let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
                pte.spec_valid() && !pte.spec_huge() && self.is_table_empty(pte.spec_addr())
            }),
        ensures
            ({
                let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
                let pt_mem = self.pt_mem.dealloc_table(pte.spec_addr());
                let pt_mem = pt_mem.write(base, idx, E::spec_empty().spec_to_u64());
                Self::new(pt_mem, self.constants).wf()
            }),
    {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
        let pt_mem = self.pt_mem.dealloc_table(pte.spec_addr()).write(
            base,
            idx,
            E::spec_empty().spec_to_u64(),
        );
        let s2 = Self::new(pt_mem, self.constants);

        assert forall|base2: SpecPAddr, idx2: nat| pt_mem.accessible(base2, idx2) implies {
            let level2 = pt_mem.level(base2);
            let pte2 = E::spec_from_u64(pt_mem.read(base2, idx2));
            let addr = pte2.spec_addr();
            &&& (level2 == s2.constants.arch.level_count() - 1 && pte2.spec_valid())
                ==> !pte2.spec_huge()
            &&& s2.pte_points_to_table(pte2, level2) ==> {
                &&& addr != pt_mem.root
                &&& pt_mem.contains_table(addr)
                &&& pt_mem.level(addr) == level2 + 1
            }
            &&& s2.pte_points_to_frame(pte2, level2) ==> {
                addr.aligned(s2.constants.arch.frame_size(level2).as_nat())
            }
        } by {
            let level2 = pt_mem.level(base2);
            let val = pt_mem.read(base2, idx2);
            let pte2 = E::spec_from_u64(val);

            if base2 == base && idx2 == idx {
                // `(base2, idx2)` is the entry we just inserted
                E::lemma_eq_by_u64(pte2, E::spec_empty());
            } else {
                assert(self.pt_mem.accessible(base2, idx2));
                E::lemma_eq_by_u64(pte2, E::spec_from_u64(self.pt_mem.read(base2, idx2)));
                if s2.pte_points_to_table(pte2, level2) {
                    // wf ensures no double reference
                    assert(pte2.spec_addr() != pte.spec_addr());
                }
            }
        }
        assert forall|base1: SpecPAddr, idx1: nat, base2: SpecPAddr, idx2: nat|
            pt_mem.accessible(base1, idx1) && pt_mem.accessible(base2, idx2) implies {
            let pte1 = E::spec_from_u64(pt_mem.read(base1, idx1));
            let pte2 = E::spec_from_u64(pt_mem.read(base2, idx2));
            ({
                &&& s2.pte_points_to_table(pte1, pt_mem.level(base1))
                &&& s2.pte_points_to_table(pte2, pt_mem.level(base2))
            }) ==> {
                ||| base1 == base2 && idx1 == idx2
                ||| (pte1.spec_addr() != pte2.spec_addr())
            }
        } by {
            let pte1 = E::spec_from_u64(pt_mem.read(base1, idx1));
            let pte2 = E::spec_from_u64(pt_mem.read(base2, idx2));
            if s2.pte_points_to_table(pte1, pt_mem.level(base1)) && s2.pte_points_to_table(
                pte2,
                pt_mem.level(base2),
            ) {
                assert(base1 != pte.spec_addr() && base2 != pte.spec_addr());
                assert(self.pt_mem.accessible(base1, idx1));
                assert(self.pt_mem.accessible(base2, idx2));
            }
        }
    }

    /// Lemma. `prune` mantains the page table wf.
    pub proof fn lemma_prune_preserves_wf(self, vaddr: SpecVAddr, base: SpecPAddr, level: nat)
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
        ensures
            self.prune(vaddr, base, level).wf(),
            self.prune(vaddr, base, level).constants == self.constants,
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vaddr, level);
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if self.pte_points_to_table(pte, level) {
            self.lemma_prune_preserves_wf(vaddr, pte.spec_addr(), level + 1);
            self.lemma_prune_preserves_lower_tables(vaddr, pte.spec_addr(), level + 1, base);
            self.lemma_prune_preserves_lower_tables(
                vaddr,
                pte.spec_addr(),
                level + 1,
                pte.spec_addr(),
            );
            let s2 = self.prune(vaddr, pte.spec_addr(), level + 1);
            if s2.is_table_empty(pte.spec_addr()) {
                s2.lemma_dealloc_intermediate_table_preserves_wf(base, level, idx);
            }
        }
    }

    /// Lemma. `prune` does not remove tables with level lower than the current level.
    pub proof fn lemma_prune_preserves_lower_tables(
        self,
        vaddr: SpecVAddr,
        base: SpecPAddr,
        level: nat,
        base2: SpecPAddr,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
            self.pt_mem.contains_table(base2),
            self.pt_mem.level(base2) <= level,
        ensures
            self.prune(vaddr, base, level).pt_mem.contains_table(base2),
            self.prune(vaddr, base, level).pt_mem.level(base2) == self.pt_mem.level(base2),
            self.pt_mem.level(base2) < level ==> self.prune(
                vaddr,
                base,
                level,
            ).pt_mem.contents[base2] == self.pt_mem.contents[base2],
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vaddr, level);
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if self.pte_points_to_table(pte, level) {
            self.lemma_prune_preserves_wf(vaddr, pte.spec_addr(), level + 1);
            // `base`, `pte.spec_addr()`, `base2` are not affected after `prune`
            self.lemma_prune_preserves_lower_tables(vaddr, pte.spec_addr(), level + 1, base);
            self.lemma_prune_preserves_lower_tables(
                vaddr,
                pte.spec_addr(),
                level + 1,
                pte.spec_addr(),
            );
            self.lemma_prune_preserves_lower_tables(vaddr, pte.spec_addr(), level + 1, base2);
        }
    }

    /// Lemma. `prune` does not change the root of the page table.
    pub proof fn lemma_prune_preserves_root(self, vaddr: SpecVAddr, base: SpecPAddr, level: nat)
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
        ensures
            self.prune(vaddr, base, level).pt_mem.root == self.pt_mem.root,
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vaddr, level);
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if self.pte_points_to_table(pte, level) {
            self.lemma_prune_preserves_wf(vaddr, pte.spec_addr(), level + 1);
            self.lemma_prune_preserves_root(vaddr, pte.spec_addr(), level + 1);
            self.lemma_prune_preserves_lower_tables(vaddr, pte.spec_addr(), level + 1, base);
            self.lemma_prune_preserves_lower_tables(
                vaddr,
                pte.spec_addr(),
                level + 1,
                pte.spec_addr(),
            );
        }
    }

    /// Lemma. `prune` only modifies tables that lie on the collected table chain for the
    /// provided `vaddr` — all tables outside that chain are preserved unchanged.
    pub proof fn lemma_prune_preserves_tables_outside_chain(
        self,
        vaddr: SpecVAddr,
        base: SpecPAddr,
        level: nat,
        base2: SpecPAddr,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
            self.pt_mem.contains_table(base2),
            !self.collect_table_chain(vaddr, base, level).contains(base2),
        ensures
            self.prune(vaddr, base, level).pt_mem.contains_table(base2),
            self.prune(vaddr, base, level).pt_mem.level(base2) == self.pt_mem.level(base2),
            self.prune(vaddr, base, level).pt_mem.contents[base2] == self.pt_mem.contents[base2],
        decreases self.constants.arch.level_count() - level,
    {
        let tables = self.collect_table_chain(vaddr, base, level);

        let idx = self.constants.arch.pte_index(vaddr, level);
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if self.pte_points_to_table(pte, level) {
            // PTE points to a child table: continue walk into the child table
            let s2 = self.prune(vaddr, pte.spec_addr(), level + 1);
            self.lemma_prune_preserves_wf(vaddr, pte.spec_addr(), level + 1);
            self.lemma_prune_preserves_lower_tables(vaddr, pte.spec_addr(), level + 1, base);
            self.lemma_prune_preserves_lower_tables(
                vaddr,
                pte.spec_addr(),
                level + 1,
                pte.spec_addr(),
            );
            let tables2 = self.collect_table_chain(vaddr, pte.spec_addr(), level + 1);

            assert(tables == Seq::new(1, |_i| base).add(tables2));
            lemma_not_in_seq_implies_not_in_subseq(tables, tables2, base, base2);
            assert(!tables2.contains(base2));
            self.lemma_prune_preserves_tables_outside_chain(
                vaddr,
                pte.spec_addr(),
                level + 1,
                base2,
            );

            assert(s2.pt_mem.contents[base2] == self.pt_mem.contents[base2]);
            if s2.is_table_empty(pte.spec_addr()) {
                // Child table became empty after prune: deallocate it and update the parent PTE
                s2.lemma_dealloc_intermediate_table_preserves_wf(base, level, idx);
                assert(s2.pt_mem.dealloc_table(pte.spec_addr()).accessible(base, idx));

                let chain = self.collect_table_chain(vaddr, base, level);
                assert(chain.contains(chain[0]));
                assert(chain.contains(chain[1]));
                assert(base2 != pte.spec_addr() && base2 != base);

                assert(self.prune(vaddr, base, level).pt_mem.contents[base2]
                    == self.pt_mem.contents[base2]);
            }
        }
    }

    /// Lemma. `prune` does not change the constructed node representation for any
    /// node that is not on the pruned path — nodes outside the collected chain remain
    /// structurally identical after pruning.
    pub proof fn lemma_prune_preserves_unrelated_node(
        self,
        vaddr: SpecVAddr,
        base: SpecPAddr,
        level: nat,
        base2: SpecPAddr,
        level2: nat,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            self.pt_mem.contains_table(base2),
            self.pt_mem.level(base2) == level2,
            level <= level2 < self.constants.arch.level_count(),
            !self.collect_table_chain(vaddr, base, level).contains(base2),
        ensures
            self.construct_node(base2, level2) == self.prune(vaddr, base, level).construct_node(
                base2,
                level2,
            ),
        decreases self.constants.arch.level_count() - level2,
    {
        let s2 = self.prune(vaddr, base, level);
        self.lemma_prune_preserves_wf(vaddr, base, level);
        self.lemma_prune_preserves_tables_outside_chain(vaddr, base, level, base2);
        assert(self.pt_mem.contents[base2] == s2.pt_mem.contents[base2]);

        let node = self.construct_node(base2, level2);
        self.construct_node_facts(base2, level2);
        let node2 = s2.construct_node(base2, level2);
        s2.construct_node_facts(base2, level2);

        assert(node.entries.len() == node2.entries.len());
        assert forall|i: int| 0 <= i < self.constants.arch.entry_count(level2) implies {
            node.entries[i] == node2.entries[i]
        } by {
            let entry = node.entries[i];
            let pte = E::spec_from_u64(self.pt_mem.read(base2, i as nat));
            E::lemma_from_u64_wf(self.pt_mem.read(base2, i as nat));
            assert(self.pt_mem.accessible(base2, i as nat));
            let pte2 = E::spec_from_u64(s2.pt_mem.read(base2, i as nat));
            E::lemma_eq_by_u64(pte, pte2);

            match entry {
                NodeEntry::Node(node) => {
                    assert(self.pte_points_to_table(pte, level2));
                    assert(self.pt_mem.contains_table(pte.spec_addr()));
                    self.lemma_table_not_in_chain_implies_child_not_in_chain(
                        vaddr,
                        base,
                        level,
                        base2,
                        i as nat,
                    );
                    self.lemma_prune_preserves_unrelated_node(
                        vaddr,
                        base,
                        level,
                        pte.spec_addr(),
                        level2 + 1,
                    );
                },
                NodeEntry::Frame(frame) => {
                    assert(self.pte_points_to_frame(pte, level2));
                },
                NodeEntry::Empty => {
                    assert(!pte.spec_valid());
                },
            }
        }
        assert(node.entries == node2.entries);
    }

    /// Lemma. The implementation-level prune is consistent with the tree model.
    pub proof fn lemma_prune_consistent_with_model(
        self,
        vaddr: SpecVAddr,
        base: SpecPAddr,
        level: nat,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
        ensures
            ({
                let s2 = self.prune(vaddr, base, level);
                let node = self.construct_node(base, level);
                let node2 = s2.construct_node(base, level);
                let path = PTTreePath::from_vaddr(
                    vaddr,
                    self.constants.arch,
                    level,
                    (self.constants.arch.level_count() - 1) as nat,
                );
                node2 == node.prune(path)
            }),
        decreases self.constants.arch.level_count() - level,
    {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        let s2 = self.prune(vaddr, base, level);
        self.lemma_prune_preserves_wf(vaddr, base, level);
        self.lemma_prune_preserves_lower_tables(vaddr, base, level, base);

        let node = self.construct_node(base, level);
        let node2 = s2.construct_node(base, level);
        self.construct_node_facts(base, level);
        s2.construct_node_facts(base, level);

        let arch = self.constants.arch;
        let end = (arch.level_count() - 1) as nat;
        let path = PTTreePath::from_vaddr(vaddr, arch, level, end);
        self.lemma_construct_node_wf(base, level);
        s2.lemma_construct_node_wf(base, level);

        let (idx, remain) = path.step();
        let entry = node.entries[idx as int];
        assert(self.pt_mem.accessible(base, idx));
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));

        let right = node.prune(path);
        node.lemma_prune_preserves_wf(path);

        if self.pte_points_to_table(pte, level) {
            // `pte` points to a subtable
            let subtable_base = pte.spec_addr();
            let subnode: PTTreeNode = entry->Node_0;

            let sm = self.prune(vaddr, subtable_base, level + 1);
            let new_subnode = subnode.prune(remain);
            // Recursive call shows subnode is updated according to model
            self.lemma_prune_preserves_wf(vaddr, subtable_base, level + 1);
            self.lemma_prune_consistent_with_model(vaddr, subtable_base, level + 1);
            PTTreePath::lemma_from_vaddr_step(vaddr, arch, level, end);
            assert(sm.construct_node(subtable_base, level + 1) == new_subnode);

            // `base`, `pte.spec_addr()`, `base2` are not affected after `prune`
            self.lemma_prune_preserves_lower_tables(vaddr, subtable_base, level + 1, base);
            self.lemma_prune_preserves_lower_tables(vaddr, subtable_base, level + 1, subtable_base);
            // The content of table `base` is not affected after `prune`
            assert(sm.pt_mem.contents[base] == self.pt_mem.contents[base]);

            sm.lemma_construct_node_empty(pte.spec_addr());
            if sm.is_table_empty(subtable_base) {
                // Lemma shows `new_subnode` is empty
                assert(right == node.update(idx, NodeEntry::Empty));
                assert(s2.pt_mem == sm.pt_mem.dealloc_table(subtable_base).write(
                    base,
                    idx,
                    E::spec_empty().spec_to_u64(),
                ));
                assert forall|i| 0 <= i < node2.entries.len() implies node2.entries[i]
                    == right.entries[i] by {
                    if i == idx {
                        // Entry `i` is empty (removed)
                        E::lemma_eq_by_u64(
                            E::spec_from_u64(s2.pt_mem.read(base, idx)),
                            E::spec_empty(),
                        );
                        assert(node2.entries[i] is Empty);
                    } else {
                        // Other entries are unchanged
                        E::lemma_eq_by_u64(
                            E::spec_from_u64(sm.pt_mem.read(base, i as nat)),
                            E::spec_from_u64(self.pt_mem.read(base, i as nat)),
                        );
                        E::lemma_eq_by_u64(
                            E::spec_from_u64(s2.pt_mem.read(base, i as nat)),
                            E::spec_from_u64(sm.pt_mem.read(base, i as nat)),
                        );
                        let pte_i = E::spec_from_u64(self.pt_mem.read(base, i as nat));
                        assert(self.pt_mem.accessible(base, i as nat));
                        if self.pte_points_to_table(pte_i, level) {
                            assert(self.pt_mem.contains_table(pte_i.spec_addr()));
                            self.lemma_other_index_not_in_chain(vaddr, base, level, i as nat);
                            self.lemma_prune_preserves_unrelated_node(
                                vaddr,
                                base,
                                level,
                                pte_i.spec_addr(),
                                level + 1,
                            );
                        }
                        assert(node2.entries[i] == node.entries[i]);
                    }
                }
                assert(node2.entries == right.entries);
            } else {
                // Lemma shows `new_subnode` is not empty
                assert(right == node.update(idx, NodeEntry::Node(new_subnode)));
                assert(s2 == sm);

                assert forall|i| 0 <= i < node2.entries.len() implies node2.entries[i]
                    == right.entries[i] by {
                    E::lemma_eq_by_u64(
                        E::spec_from_u64(s2.pt_mem.read(base, i as nat)),
                        E::spec_from_u64(self.pt_mem.read(base, i as nat)),
                    );
                    if i == idx {
                        // Entry `i` is the subtree constructed from `subtable_base`
                        assert(node2.entries[i] == NodeEntry::Node(new_subnode));
                    } else {
                        // Other entries are unchanged
                        let pte_i = E::spec_from_u64(self.pt_mem.read(base, i as nat));
                        assert(self.pt_mem.accessible(base, i as nat));
                        if self.pte_points_to_table(pte_i, level) {
                            self.lemma_other_index_not_in_chain(vaddr, base, level, i as nat);
                            self.lemma_prune_preserves_unrelated_node(
                                vaddr,
                                base,
                                level,
                                pte_i.spec_addr(),
                                level + 1,
                            );
                        }
                        assert(node2.entries[i] == node.entries[i]);
                    }
                }
                assert(node2.entries == right.entries);
            }
        }
    }

    /// Lemma. `prune` can only remove tables, not add them. Any table in the result of `prune`
    /// also exists in `self` at the same level.
    pub proof fn lemma_prune_table_in_original(
        self,
        vaddr: SpecVAddr,
        base: SpecPAddr,
        level: nat,
        base2: SpecPAddr,
    )
        requires
            self.wf(),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
            self.prune(vaddr, base, level).pt_mem.contains_table(base2),
        ensures
            self.pt_mem.contains_table(base2),
            self.pt_mem.level(base2) == self.prune(vaddr, base, level).pt_mem.level(base2),
        decreases self.constants.arch.level_count() - level,
    {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        let idx = self.constants.arch.pte_index(vaddr, level);
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if self.pte_points_to_table(pte, level) {
            let sub_pruned = self.prune(vaddr, pte.spec_addr(), level + 1);
            self.lemma_prune_preserves_wf(vaddr, pte.spec_addr(), level + 1);
            self.lemma_prune_preserves_lower_tables(vaddr, pte.spec_addr(), level + 1, base);
            self.lemma_prune_preserves_lower_tables(
                vaddr,
                pte.spec_addr(),
                level + 1,
                pte.spec_addr(),
            );

            if sub_pruned.is_table_empty(pte.spec_addr()) {
                // pruned = sub_pruned.dealloc_table(pte.spec_addr()).write(...)
                // pruned.pt_mem.tables == sub_pruned.pt_mem.tables.remove(pte.spec_addr())
                broadcast use SpecPageTableMem::dealloc_table_facts;

                assert(sub_pruned.pt_mem.dealloc_table_pre(pte.spec_addr()));
                let after_dealloc = sub_pruned.pt_mem.dealloc_table(pte.spec_addr());
                assert(SpecPageTableMem::dealloc_table_spec(
                    sub_pruned.pt_mem,
                    after_dealloc,
                    pte.spec_addr(),
                ));
                // after_dealloc.tables == sub_pruned.pt_mem.tables.remove(pte.spec_addr())
                // write doesn't change tables, so pruned.pt_mem.tables == after_dealloc.tables
                // base2 is in pruned.pt_mem, which is after_dealloc, so base2 != pte.spec_addr()
                assert(base2 != pte.spec_addr());
                // base2 is in sub_pruned (since after_dealloc.tables ⊆ sub_pruned.pt_mem.tables and base2 != pte)
                assert(sub_pruned.pt_mem.contains_table(base2));
                // by induction, base2 is in self
                self.lemma_prune_table_in_original(vaddr, pte.spec_addr(), level + 1, base2);
            } else {
                // pruned == sub_pruned
                assert(sub_pruned.pt_mem.contains_table(base2));
                self.lemma_prune_table_in_original(vaddr, pte.spec_addr(), level + 1, base2);
            }
        }
        // else pruned == self

    }

    /// Lemma. `prune` after `remove` will eliminate empty nodes.
    pub proof fn lemma_prune_after_remove_preserves_all_nonempty(
        self,
        vbase: SpecVAddr,
        base: SpecPAddr,
        level: nat,
    )
        requires
            self.wf(),
            self.all_nonempty_above(level),
            self.pt_mem.contains_table_with_level(base, level),
            level < self.constants.arch.level_count(),
        ensures
            self.remove(vbase, base, level).1 is Ok ==> self.remove(vbase, base, level).0.prune(
                vbase,
                base,
                level,
            ).all_nonempty_above(level),
        decreases self.constants.arch.level_count() - level,
    {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        let (removed, res) = self.remove(vbase, base, level);
        self.lemma_remove_preserves_wf(vbase, base, level);
        self.lemma_remove_preserves_old_tables(vbase, base, level, base);
        let pruned = removed.prune(vbase, base, level);
        let idx = self.constants.arch.pte_index(vbase, level);
        assert(self.pt_mem.accessible(base, idx));
        let pte = E::spec_from_u64(self.pt_mem.read(base, idx));

        if res is Ok {
            assert(pte.spec_valid());
            if level >= self.constants.arch.level_count() - 1 {
                // Leaf node
                assert(vbase.aligned(self.constants.arch.frame_size(level).as_nat()));
                // Update entry (base, idx)
                assert(removed.pt_mem == self.pt_mem.write(
                    base,
                    idx,
                    E::spec_empty().spec_to_u64(),
                ));
                assert(pruned.all_nonempty_above(level));
            } else {
                if pte.spec_huge() {
                    assert(vbase.aligned(self.constants.arch.frame_size(level).as_nat()));
                    // Update entry (base, idx)
                    assert(removed.pt_mem == self.pt_mem.write(
                        base,
                        idx,
                        E::spec_empty().spec_to_u64(),
                    ));
                    assert(forall|base2: SpecPAddr| #[trigger]
                        removed.pt_mem.contains_table(base2) && base2 != base
                            ==> removed.pt_mem.contents[base2] == self.pt_mem.contents[base2]);
                    assert forall|base2: SpecPAddr|
                        removed.pt_mem.contains_table(base2) && base2
                            != base implies removed.is_table_empty(base2) == self.is_table_empty(
                        base2,
                    ) by {
                        assert(forall|idx2: nat|
                            idx2 < self.constants.arch.entry_count(self.pt_mem.level(base2))
                                ==> removed.pt_mem.read(base2, idx2) == self.pt_mem.read(
                                base2,
                                idx2,
                            ));
                    }
                    assert forall|base2: SpecPAddr, level2: nat|
                        removed.pt_mem.contains_table_with_level(base2, level2) && level2
                            > level implies !removed.is_table_empty(base2) by {
                        assert(base2 != base);
                        assert(self.pt_mem.contains_table_with_level(base2, level2));
                    }
                    assert(pruned == removed);
                    assert(pruned.all_nonempty_above(level));
                } else {
                    // Intermediate node
                    self.lemma_remove_preserves_old_tables(vbase, base, level, pte.spec_addr());
                    assert(removed == self.remove(vbase, pte.spec_addr(), level + 1).0);
                    // base (level `level`) cannot be in a chain starting at level+1
                    assert(!self.collect_table_chain(vbase, pte.spec_addr(), level + 1).contains(
                        base,
                    )) by {
                        if self.collect_table_chain(vbase, pte.spec_addr(), level + 1).contains(
                            base,
                        ) {
                            self.lemma_chain_level_ge(vbase, pte.spec_addr(), level + 1, base);
                            assert(self.pt_mem.level(base) >= level + 1);
                            assert(false);
                        }
                    };
                    self.lemma_remove_preserves_tables_outside_chain(
                        vbase,
                        pte.spec_addr(),
                        level + 1,
                        base,
                    );
                    assert(removed.pt_mem.contents[base] == self.pt_mem.contents[base]);
                    let pte2 = E::spec_from_u64(removed.pt_mem.read(base, idx));
                    assert(pte2 == pte);
                    assert(pte2.spec_valid() && !pte2.spec_huge() && level
                        < self.constants.arch.level_count() - 1);

                    let sub_pruned = removed.prune(vbase, pte.spec_addr(), level + 1);
                    removed.lemma_prune_preserves_wf(vbase, pte.spec_addr(), level + 1);
                    assert(sub_pruned.wf());

                    removed.lemma_prune_preserves_lower_tables(
                        vbase,
                        pte.spec_addr(),
                        level + 1,
                        pte.spec_addr(),
                    );
                    removed.lemma_prune_preserves_lower_tables(
                        vbase,
                        pte.spec_addr(),
                        level + 1,
                        base,
                    );
                    assert(sub_pruned.pt_mem.contains_table(base));
                    assert(sub_pruned.pt_mem.contains_table(pte.spec_addr()));
                    assert(pte.spec_addr() != sub_pruned.pt_mem.root);
                    assert(pte.spec_addr() != base);
                    // sub_pruned.pt_mem.contains_table(base) and base != pte.spec_addr(), so accessible is preserved
                    assert(sub_pruned.pt_mem.accessible(base, idx));
                    broadcast use SpecPageTableMem::dealloc_table_facts;

                    assert(sub_pruned.pt_mem.dealloc_table(pte.spec_addr()).accessible(base, idx))
                        by {
                        SpecPageTableMem::lemma_dealloc_table_preserves_accessibility(
                            sub_pruned.pt_mem,
                            sub_pruned.pt_mem.dealloc_table(pte.spec_addr()),
                            pte.spec_addr(),
                            base,
                            idx,
                        );
                    };

                    self.lemma_prune_after_remove_preserves_all_nonempty(
                        vbase,
                        pte.spec_addr(),
                        level + 1,
                    );
                    assert(sub_pruned.all_nonempty_above(level + 1));

                    assert(removed.constants == self.constants);

                    if sub_pruned.is_table_empty(pte2.spec_addr()) {
                        assert(pruned.pt_mem == sub_pruned.pt_mem.dealloc_table(
                            pte2.spec_addr(),
                        ).write(base, idx, E::spec_empty().spec_to_u64()));
                    } else {
                        assert(pruned == sub_pruned);
                    }
                    assert forall|base2: SpecPAddr|
                        pruned.pt_mem.contains_table_with_level(base2, level + 1) && base2
                            != pte2.spec_addr() implies !pruned.is_table_empty(base2) by {
                        // base2 is in sub_pruned (since pruned = sub_pruned.dealloc(pte2).write and base2 != pte2)
                        assert(sub_pruned.pt_mem.contains_table_with_level(base2, level + 1));
                        // base2 is in removed (prune can only remove tables)
                        removed.lemma_prune_table_in_original(
                            vbase,
                            pte.spec_addr(),
                            level + 1,
                            base2,
                        );
                        assert(removed.pt_mem.contains_table_with_level(base2, level + 1));
                        // base2 is at level+1 and != pte.spec_addr() (the chain head),
                        // so it cannot be the head and hence not in the chain.
                        assert(!removed.collect_table_chain(
                            vbase,
                            pte.spec_addr(),
                            level + 1,
                        ).contains(base2)) by {
                            if removed.collect_table_chain(
                                vbase,
                                pte.spec_addr(),
                                level + 1,
                            ).contains(base2) {
                                removed.lemma_table_at_chain_start_level_is_head(
                                    vbase,
                                    pte.spec_addr(),
                                    level + 1,
                                    base2,
                                );
                                assert(false);
                            }
                        };
                        removed.lemma_prune_preserves_tables_outside_chain(
                            vbase,
                            pte.spec_addr(),
                            level + 1,
                            base2,
                        );
                        assert(pruned.pt_mem.contents[base2] == removed.pt_mem.contents[base2]);
                        // base2 is in self (remove preserves tables outside chain)
                        assert(!self.collect_table_chain(
                            vbase,
                            pte.spec_addr(),
                            level + 1,
                        ).contains(base2)) by {
                            self.lemma_remove_preserves_chain(vbase, pte.spec_addr(), level + 1);
                            if self.collect_table_chain(vbase, pte.spec_addr(), level + 1).contains(
                                base2,
                            ) {
                                assert(removed.collect_table_chain(
                                    vbase,
                                    pte.spec_addr(),
                                    level + 1,
                                ).contains(base2));
                                assert(false);
                            }
                        };
                        self.lemma_remove_preserves_table_set(vbase, pte.spec_addr(), level + 1);
                        self.lemma_remove_preserves_tables_outside_chain(
                            vbase,
                            pte.spec_addr(),
                            level + 1,
                            base2,
                        );
                        assert(removed.pt_mem.contents[base2] == self.pt_mem.contents[base2]);
                        assert(forall|idx2: nat|
                            idx2 < self.constants.arch.entry_count(level + 1)
                                ==> pruned.pt_mem.read(base2, idx2) == self.pt_mem.read(
                                base2,
                                idx2,
                            ));
                        assert(self.pt_mem.contains_table_with_level(base2, level + 1));
                        assert(!self.is_table_empty(base2));
                    }
                    assert forall|base2: SpecPAddr, level2: nat|
                        pruned.pt_mem.contains_table_with_level(base2, level2) && level2
                            > level implies !pruned.is_table_empty(base2) by {
                        if level2 > level + 1 {
                            assert(sub_pruned.pt_mem.contains_table_with_level(base2, level2));
                            assert(sub_pruned.pt_mem.contents[base2]
                                == pruned.pt_mem.contents[base2]);
                            assert(forall|idx2: nat|
                                idx2 < self.constants.arch.entry_count(level2)
                                    ==> sub_pruned.pt_mem.read(base2, idx2) == pruned.pt_mem.read(
                                    base2,
                                    idx2,
                                ));
                        }
                    }
                }
            }
        }
    }
}

/// Lemma. If a seqence does not contain a value, then its subsequence does not contain it either.
pub proof fn lemma_not_in_seq_implies_not_in_subseq<T>(
    seq1: Seq<T>,
    seq2: Seq<T>,
    start: T,
    needle: T,
)
    requires
        seq1 == Seq::new(1, |_i| start).add(seq2),
        !seq1.contains(needle),
    ensures
        start != needle,
        !seq2.contains(needle),
{
    assert(seq1[0] == start);
    assert(seq1.contains(seq1[0]));
    if seq2.contains(needle) {
        let i = choose|i| 0 <= i < seq2.len() && seq2[i] == needle;
        assert(seq1[i + 1] == needle);
        assert(seq1.contains(needle));
    }
}

} // verus!
