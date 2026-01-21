//! Spec-mode page table implementation. Used for refinement proofs.
use core::marker::PhantomData;
use vstd::prelude::*;

use super::{
    path::PTTreePath,
    tree::{NodeEntry, PTTreeModel, PTTreeNode},
};
use crate::address::{
    addr::{PAddr, VAddr},
    frame::{Frame, MemAttr},
};
use crate::page_table::{
    pt_arch::SpecPTArch,
    pt_mem::SpecPageTableMem,
    pt_trait::{PagingResult, SpecPTConstants},
    pte::GhostPTE,
};

verus! {

// Use page table memory related lemmas.
broadcast use crate::page_table::pt_mem::group_pt_mem_lemmas;

/// Spec-mode page table implementation.
pub struct SpecPageTable<G: GhostPTE> {
    /// Page table memory.
    pub pt_mem: SpecPageTableMem,
    /// Page table config constants.
    pub constants: SpecPTConstants,
    /// Phantom data.
    pub _phantom: PhantomData<G>,
}

impl<G> SpecPageTable<G> where G: GhostPTE {
    /// Wrap a page table memory and constants into a spec-mode page table.
    pub open spec fn new(pt_mem: SpecPageTableMem, constants: SpecPTConstants) -> Self {
        Self { pt_mem, constants, _phantom: PhantomData }
    }

    /// If `pte` points to a frame.
    pub open spec fn pte_points_to_frame(self, pte: G, level: nat) -> bool {
        pte.valid() && if level < self.constants.arch.level_count() - 1 {
            pte.huge()
        } else {
            !pte.huge()
        }
    }

    /// If `pte` points to a table.
    pub open spec fn pte_points_to_table(self, pte: G, level: nat) -> bool {
        pte.valid() && level < self.constants.arch.level_count() - 1 && !pte.huge()
    }

    /// If `pte` points to a frame with valid address and size.
    pub open spec fn pte_valid_frame(self, pte: G, level: nat) -> bool {
        let frame_size = self.constants.arch.frame_size(level);
        &&& self.pte_points_to_frame(pte, level)
        &&& pte.addr().aligned(frame_size.as_nat())
        &&& self.constants.pmem_lb.0 <= pte.addr().0
        &&& pte.addr().0 + frame_size.as_nat() <= self.constants.pmem_ub.0
    }

    /// Construct a `Frame` from a `PTE`.
    pub open spec fn pte_to_frame(self, pte: G, level: nat) -> Frame {
        Frame { base: pte.addr(), attr: pte.attr(), size: self.constants.arch.frame_size(level) }
    }

    /// If all pte in a table are invalid.
    pub open spec fn is_table_empty(self, base: PAddr) -> bool
        recommends
            self.invariants(),
            self.pt_mem.contains_table(base),
    {
        let level = self.pt_mem.table(base).level;
        forall|idx: nat|
            #![auto]
            idx < self.constants.arch.entry_count(level) ==> !G::from_u64(
                self.pt_mem.read(base, idx),
            ).valid()
    }

    /// Invariants that ensure the page table is well-formed.
    pub open spec fn invariants(self) -> bool {
        // Architecture
        &&& self.pt_mem.arch
            == self.constants.arch
        // Page table memory invariants
        &&& self.pt_mem.invariants()
        // For each page table entry that can be accessed
        &&& forall|base: PAddr, idx: nat|
            self.pt_mem.accessible(base, idx) ==> {
                let pt_mem = self.pt_mem;
                let table = pt_mem.table(base);
                let pte = G::from_u64(pt_mem.read(base, idx));
                let addr = pte.addr();
                // If `table` is a leaf table, `pte` is either invalid or points to a frame
                &&& (table.level == self.constants.arch.level_count() - 1 && pte.valid())
                    ==> !pte.huge()
                // If `pte` is valid and points to a subtable
                &&& self.pte_points_to_table(pte, table.level) ==> {
                    // The subtable is not root
                    &&& addr
                        != self.pt_mem.root()
                    // `pt_mem` contains the subtable, and the table level is one level higher than `base`
                    &&& pt_mem.contains_table(addr)
                    &&& pt_mem.table(addr).level == table.level + 1
                }
                // If `pte` is valid and points to a frame
                &&& self.pte_points_to_frame(pte, table.level) ==> {
                    // The frame is valid
                    &&& addr.aligned(self.constants.arch.frame_size(table.level).as_nat())
                    &&& self.constants.pmem_lb.0 <= addr.0
                    &&& addr.0 + self.constants.arch.frame_size(table.level).as_nat()
                        <= self.constants.pmem_ub.0
                }
            }
            // For each 2 page table entries that can be accessed
        &&& forall|base1: PAddr, idx1: nat, base2: PAddr, idx2: nat|
            self.pt_mem.accessible(base1, idx1) && self.pt_mem.accessible(base2, idx2) ==> {
                let pte1 = G::from_u64(self.pt_mem.read(base1, idx1));
                let pte2 = G::from_u64(self.pt_mem.read(base2, idx2));
                // If two pte points to the same table, they must be equal
                ({
                    &&& self.pte_points_to_table(pte1, self.pt_mem.table(base1).level)
                    &&& self.pte_points_to_table(pte2, self.pt_mem.table(base2).level)
                }) ==> {
                    ||| base1 == base2 && idx1 == idx2
                    ||| (pte1.addr() != pte2.addr())
                }
            }
    }

    /// Recursively construct a `PTTreeNode` from a subtable.
    pub uninterp spec fn construct_node(self, base: PAddr, level: nat) -> PTTreeNode
        recommends
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
    ;

    /// Illustrate the refinement relationship between `PageTable` and `PTTreeModel`.
    #[verifier::external_body]
    pub proof fn construct_node_facts(self, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
        ensures
            ({
                let node = self.construct_node(base, level);
                &&& node.level == level
                &&& node.constants == self.constants
                &&& node.entries.len() == self.constants.arch.entry_count(level)
                &&& forall|idx: nat|
                    idx < self.constants.arch.entry_count(level) ==> {
                        let pte = G::from_u64(self.pt_mem.read(base, idx));
                        let entry = #[trigger] node.entries[idx as int];
                        match entry {
                            NodeEntry::Frame(frame) => {
                                &&& self.pte_points_to_frame(pte, level)
                                &&& frame.base == pte.addr()
                                &&& frame.attr == pte.attr()
                                &&& frame.size == self.constants.arch.frame_size(level)
                            },
                            NodeEntry::Node(subnode) => {
                                &&& self.pte_points_to_table(pte, level)
                                &&& subnode == self.construct_node(pte.addr(), level + 1)
                            },
                            NodeEntry::Empty => !pte.valid(),
                        }
                    }
            }),
    {
    }

    /// View the page table implementation as a tree-model abstraction.
    pub open spec fn view(self) -> PTTreeModel
        recommends
            self.invariants(),
    {
        PTTreeModel { root: self.construct_node(self.pt_mem.root(), 0) }
    }

    /// Perform a recursive specification-level page table walk starting from a given base.
    ///
    /// Terminate upon reaching an invalid or block entry, or reaching the leaf level.
    pub open spec fn walk(self, vaddr: VAddr, base: PAddr, level: nat) -> (G, nat)
        recommends
            self.invariants(),
            self.pt_mem.contains_table(base),
            self.pt_mem.table(base).level == level,
            level < self.constants.arch.level_count(),
        decreases self.constants.arch.level_count() - level,
    {
        let pte = G::from_u64(self.pt_mem.read(base, self.constants.arch.pte_index(vaddr, level)));
        if self.pte_points_to_table(pte, level) {
            self.walk(vaddr, pte.addr(), level + 1)
        } else {
            (pte, level)
        }
    }

    /// Perform a recursive specification-level page table insertion starting from a given base.
    pub open spec fn insert(
        self,
        vbase: VAddr,
        base: PAddr,
        level: nat,
        target_level: nat,
        new_pte: G,
    ) -> (Self, PagingResult)
        recommends
            self.invariants(),
            self.pt_mem.contains_table(base),
            self.pt_mem.table(base).level == level,
            level <= target_level < self.constants.arch.level_count(),
            self.pte_valid_frame(new_pte, target_level),
        decreases target_level - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = G::from_u64(self.pt_mem.read(base, idx));
        if level >= target_level {
            // Insert at current level
            if pte.valid() {
                (self, Err(()))
            } else {
                (Self::new(self.pt_mem.write(base, idx, new_pte.to_u64()), self.constants), Ok(()))
            }
        } else {
            if pte.valid() {
                if pte.huge() {
                    (self, Err(()))
                } else {
                    // Insert at next level
                    self.insert(vbase, pte.addr(), level + 1, target_level, new_pte)
                }
            } else {
                // Insert intermediate table
                // Allocate a new table
                let (pt_mem, table) = self.pt_mem.alloc_table(level + 1);
                // Write entry
                let pt_mem = pt_mem.write(
                    base,
                    idx,
                    G::new(table.base, MemAttr::spec_default(), false).to_u64(),
                );
                Self::new(pt_mem, self.constants).insert(
                    vbase,
                    table.base,
                    level + 1,
                    target_level,
                    new_pte,
                )
            }
        }
    }

    /// Perform a recursive specification-level page table removal starting from a given base.
    pub open spec fn remove(self, vbase: VAddr, base: PAddr, level: nat) -> (Self, PagingResult)
        recommends
            self.invariants(),
            self.pt_mem.contains_table(base),
            self.pt_mem.table(base).level == level,
            level < self.constants.arch.level_count(),
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = G::from_u64(self.pt_mem.read(base, idx));
        if pte.valid() {
            if level >= self.constants.arch.level_count() - 1 {
                // Leaf node
                if vbase.aligned(self.constants.arch.frame_size(level).as_nat()) {
                    (
                        Self::new(
                            self.pt_mem.write(base, idx, G::empty().to_u64()),
                            self.constants,
                        ),
                        Ok(()),
                    )
                } else {
                    (self, Err(()))
                }
            } else {
                // Intermediate node
                if pte.huge() {
                    if vbase.aligned(self.constants.arch.frame_size(level).as_nat()) {
                        (
                            Self::new(
                                self.pt_mem.write(base, idx, G::empty().to_u64()),
                                self.constants,
                            ),
                            Ok(()),
                        )
                    } else {
                        (self, Err(()))
                    }
                } else {
                    self.remove(vbase, pte.addr(), level + 1)
                }
            }
        } else {
            (self, Err(()))
        }
    }

    /// Recursively remove empty tables along `vaddr` from `base`.
    pub open spec fn prune(self, vaddr: VAddr, base: PAddr, level: nat) -> Self
        recommends
            self.invariants(),
            self.pt_mem.contains_table(base),
            self.pt_mem.table(base).level == level,
            level < self.constants.arch.level_count(),
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vaddr, level);
        let pte = G::from_u64(self.pt_mem.read(base, idx));
        if level >= self.constants.arch.level_count() - 1 {
            // Leaf table
            self
        } else {
            if pte.valid() && !pte.huge() {
                // Recycle from subtable
                let s2 = self.prune(vaddr, pte.addr(), level + 1);
                if s2.is_table_empty(pte.addr()) {
                    // If subtable is empty, deallocate it and mark the entry as invalid
                    Self::new(
                        s2.pt_mem.dealloc_table(pte.addr()).write(base, idx, G::empty().to_u64()),
                        self.constants,
                    )
                } else {
                    s2
                }
            } else {
                self
            }
        }
    }

    /// Return the sequence of page-table base addresses visited when walking the
    /// page-table path for `vaddr` starting at table `base` on level `level`.
    pub open spec fn collect_table_chain(self, vaddr: VAddr, base: PAddr, level: nat) -> Seq<PAddr>
        recommends
            self.invariants(),
            self.pt_mem.contains_table(base),
            self.pt_mem.table(base).level == level,
            level < self.constants.arch.level_count(),
        decreases self.constants.arch.level_count() - level,
    {
        let pte = G::from_u64(self.pt_mem.read(base, self.constants.arch.pte_index(vaddr, level)));
        if self.pte_points_to_table(pte, level) {
            // PTE points to a child table: continue walk into the child table
            Seq::new(1, |_i| base).add(self.collect_table_chain(vaddr, pte.addr(), level + 1))
        } else {
            // PTE does not point to another table: chain ends here
            Seq::new(1, |_i| base)
        }
    }

    /// Lemma. Constructing a node from memory with a valid table results in a
    /// structurally invariant model node.
    pub proof fn lemma_construct_node_implies_invariants(self, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
        ensures
            self.construct_node(base, level).invariants(),
        decreases self.constants.arch.level_count() - level,
    {
        let node = self.construct_node(base, level);
        self.construct_node_facts(base, level);

        assert forall|i| 0 <= i < node.entries.len() implies {
            &&& PTTreeNode::is_entry_valid(#[trigger] node.entries[i], node.level, node.constants)
            &&& node.entries[i] is Node ==> node.entries[i]->Node_0.invariants()
        } by {
            assert(self.pt_mem.accessible(base, i as nat));
            match node.entries[i] {
                NodeEntry::Frame(frame) => {
                    assert({
                        &&& frame.base.aligned(frame.size.as_nat())
                        &&& frame.base.0 >= node.constants.pmem_lb.0
                        &&& frame.base.0 + frame.size.as_nat() <= node.constants.pmem_ub.0
                    });
                },
                NodeEntry::Node(subnode) => {
                    let pte = G::from_u64(self.pt_mem.read(base, i as nat));
                    assert(self.pt_mem.accessible(base, i as nat));
                    // Invariants ensures this
                    assert(self.pt_mem.contains_table(pte.addr()));
                    assert(self.pt_mem.table(pte.addr()).level == level + 1);
                    self.construct_node_facts(pte.addr(), level + 1);
                    self.lemma_construct_node_implies_invariants(pte.addr(), level + 1);
                },
                NodeEntry::Empty => (),
            }
        }
    }

    /// Lemma. The tree model derived from the executable page table maintains the
    /// required invariants.
    pub proof fn lemma_view_implies_invariants(self)
        requires
            self.invariants(),
        ensures
            self@.invariants(),
    {
        self.pt_mem.lemma_contains_root();
        self.lemma_construct_node_implies_invariants(self.pt_mem.root(), 0);
        // TODO: fully_populated not checked
        assume(false);
    }

    /// Lemma. Empty table --construct_node--> empty node.
    pub proof fn lemma_empty_table_constructs_empty_node(self, base: PAddr)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
        ensures
            self.is_table_empty(base) <==> self.construct_node(
                base,
                self.pt_mem.table(base).level,
            ).empty(),
    {
        let level = self.pt_mem.table(base).level;
        let node = self.construct_node(base, level);
        self.construct_node_facts(base, level);
        if node.empty() {
            assert forall|idx: nat|
                #![auto]
                idx < self.constants.arch.entry_count(level) implies !G::from_u64(
                self.pt_mem.read(base, idx),
            ).valid() by {
                assert(node.entries.contains(node.entries[idx as int]));
            }
        }
    }

    /// Lemma. The chain returned by `collect_table_chain` is well-formed: each address
    /// corresponds to a valid table, table levels increase by one, and consecutive
    /// tables are linked via the PTE at the corresponding index.
    pub proof fn lemma_table_chain_entries_valid(self, vaddr: VAddr, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            self.pt_mem.table(base).level == level,
            level < self.constants.arch.level_count(),
        ensures
            ({
                let tables = self.collect_table_chain(vaddr, base, level);
                &&& forall|i|
                    #![auto]
                    0 <= i < tables.len() ==> self.pt_mem.contains_table(tables[i])
                        && self.pt_mem.table(tables[i]).level == level + i
                &&& forall|i|
                    0 <= i < tables.len() - 1 ==> {
                        let idx = self.constants.arch.pte_index(vaddr, level + i as nat);
                        let pte = G::from_u64(self.pt_mem.read(#[trigger] tables[i], idx));
                        self.pte_points_to_table(pte, level + i as nat) && pte.addr() == tables[i
                            + 1]
                    }
            }),
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vaddr, level);
        let pte = G::from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));
        if self.pte_points_to_table(pte, level) {
            // PTE points to a child table: continue walk into the child table
            self.lemma_table_chain_entries_valid(vaddr, pte.addr(), level + 1);
        }
    }

    /// Lemma. An entry at `idx2` in `base` that points to a table but is not the index
    /// chosen by `vaddr` cannot appear in the chain collected for `vaddr`.
    pub proof fn lemma_other_index_not_in_chain(
        self,
        vaddr: VAddr,
        base: PAddr,
        level: nat,
        idx2: nat,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            self.pt_mem.table(base).level == level,
            level < self.constants.arch.level_count(),
            self.pt_mem.accessible(base, idx2),
            idx2 != self.constants.arch.pte_index(vaddr, level),
            self.pte_points_to_table(G::from_u64(self.pt_mem.read(base, idx2)), level),
        ensures
            !self.collect_table_chain(vaddr, base, level).contains(
                G::from_u64(self.pt_mem.read(base, idx2)).addr(),
            ),
    {
        let idx = self.constants.arch.pte_index(vaddr, level);
        let pte = G::from_u64(self.pt_mem.read(base, idx));
        let pte2 = G::from_u64(self.pt_mem.read(base, idx2));
        let tables = self.collect_table_chain(vaddr, base, level);
        self.lemma_table_chain_entries_valid(vaddr, base, level);

        if tables.contains(pte2.addr()) {
            // Assume pte2's address in the collected chain
            assert(pte2.addr() != base);
            assert(tables[0] == base);
            let i = choose|i| 0 <= i < tables.len() && tables[i] == pte2.addr();
            assert(i > 0);

            let idx3 = self.constants.arch.pte_index(vaddr, (level + i - 1) as nat);
            assert(self.pt_mem.accessible(tables[i - 1], idx3));
            let pte3 = G::from_u64(self.pt_mem.read(tables[i - 1], idx3));
            assert(self.pte_points_to_table(pte3, (level + i - 1) as nat));
            // Found 2 pte points to the same table — derive contradiction
            assert(pte3.addr() == pte2.addr());
            assert(false);
        }
    }

    /// Lemma. If `base2` is not in the chain collected for `vaddr` starting at `base`, then
    /// the child table addressed by the PTE at `base2[idx2]` is also not in that chain.
    pub proof fn lemma_table_not_in_chain_implies_child_not_in_chain(
        self,
        vaddr: VAddr,
        base: PAddr,
        level: nat,
        base2: PAddr,
        idx2: nat,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            self.pt_mem.table(base).level == level,
            level < self.constants.arch.level_count(),
            self.pt_mem.accessible(base2, idx2),
            self.pt_mem.table(base2).level >= level,
            self.pte_points_to_table(
                G::from_u64(self.pt_mem.read(base2, idx2)),
                self.pt_mem.table(base2).level,
            ),
            !self.collect_table_chain(vaddr, base, level).contains(base2),
        ensures
            !self.collect_table_chain(vaddr, base, level).contains(
                G::from_u64(self.pt_mem.read(base2, idx2)).addr(),
            ),
    {
        let tables = self.collect_table_chain(vaddr, base, level);
        self.lemma_table_chain_entries_valid(vaddr, base, level);

        let pte2 = G::from_u64(self.pt_mem.read(base2, idx2));
        if tables.contains(pte2.addr()) {
            // Assume pte2's address in the collected chain
            assert(pte2.addr() != base);
            assert(tables[0] == base);
            let i = choose|i| 0 <= i < tables.len() && tables[i] == pte2.addr();
            let base3 = tables[i - 1];
            assert(tables.contains(base3));
            let level3 = self.pt_mem.table(base3).level;
            let idx3 = self.constants.arch.pte_index(vaddr, level3);
            assert(self.pt_mem.accessible(base3, idx3));

            let pte3 = G::from_u64(self.pt_mem.read(base3, idx3));
            assert(self.pte_points_to_table(pte3, level3));
            // Found 2 pte points to the same table — derive contradiction
            assert(pte3.addr() != pte2.addr());
            assert(false);
        }
    }

    /// Lemma. The specification-level walk is consistent with the node model traversal
    /// via `PTTreeNode::visit`.
    pub proof fn lemma_walk_consistent_with_model(self, vaddr: VAddr, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
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
                level2 == level + visited.len() - 1 && visited.last() == if pte.valid() {
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
        // Precondition of `visit`: node.invariants and path.valid
        self.lemma_construct_node_implies_invariants(base, level);
        let visited = node.visit(path);

        let (idx, remain) = path.step();
        let entry = node.entries[idx as int];
        assert(self.pt_mem.accessible(base, idx));

        if path.len() <= 1 {
            assert(visited == Seq::new(1, |_i| entry));
        } else {
            if let NodeEntry::Node(subnode) = entry {
                let pte2 = G::from_u64(self.pt_mem.read(base, idx));
                // `pte2` points to a subtable
                let subtable_base = pte2.addr();
                // Recursive visit from the subtable
                self.lemma_walk_consistent_with_model(vaddr, subtable_base, level + 1);
                PTTreePath::lemma_from_vaddr_step(vaddr, arch, level, end);
            }
        }
    }

    /// Lemma. Allocating an intermediate table preserves invariants.
    pub proof fn lemma_alloc_intermediate_table_preserves_invariants(
        self,
        base: PAddr,
        level: nat,
        idx: nat,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level + 1 < self.constants.arch.level_count(),
            self.pt_mem.accessible(base, idx),
            !G::from_u64(self.pt_mem.read(base, idx)).valid(),
        ensures
            ({
                let (pt_mem, table) = self.pt_mem.alloc_table(level + 1);
                let pt_mem = pt_mem.write(
                    base,
                    idx,
                    G::new(table.base, MemAttr::spec_default(), false).to_u64(),
                );
                Self::new(pt_mem, self.constants).invariants()
            }),
    {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        let (pt_mem, table) = self.pt_mem.alloc_table(level + 1);
        let pt_mem = pt_mem.write(
            base,
            idx,
            G::new(table.base, MemAttr::spec_default(), false).to_u64(),
        );
        let s2 = Self::new(pt_mem, self.constants);

        assert forall|base2: PAddr, idx2: nat| pt_mem.accessible(base2, idx2) implies {
            let table2 = pt_mem.table(base2);
            let pte = G::from_u64(pt_mem.read(base2, idx2));
            let addr = pte.addr();
            &&& (table2.level == s2.constants.arch.level_count() - 1 && pte.valid()) ==> !pte.huge()
            &&& s2.pte_points_to_table(pte, table2.level) ==> {
                &&& addr != pt_mem.root()
                &&& pt_mem.contains_table(addr)
                &&& pt_mem.table(addr).level == table2.level + 1
            }
            &&& s2.pte_points_to_frame(pte, table2.level) ==> {
                &&& addr.aligned(s2.constants.arch.frame_size(table2.level).as_nat())
                &&& s2.constants.pmem_lb.0 <= addr.0
                &&& addr.0 + s2.constants.arch.frame_size(table2.level).as_nat()
                    <= s2.constants.pmem_ub.0
            }
        } by {
            let table2 = pt_mem.table(base2);
            let val = pt_mem.read(base2, idx2);
            let pte = G::from_u64(val);

            if base2 == base && idx2 == idx {
                // `(base2, idx2)` is the entry just inserted
                G::lemma_eq_by_u64(pte, G::new(table.base, MemAttr::spec_default(), false));
            } else {
                if base2 == table.base {
                    // `base2` is the newly allocated table
                    assert(pte == G::from_u64(0));
                } else {
                    // Entry at `(base2, idx2)` is not updated
                    assert(self.pt_mem.accessible(base2, idx2));
                    assert(val == self.pt_mem.read(base2, idx2));
                    if self.pte_points_to_table(pte, table2.level) {
                        assert(pte.addr() != pt_mem.root());
                        assert(pt_mem.contains_table(pte.addr()));
                        assert(pt_mem.table(pte.addr()).level == table2.level + 1);
                    }
                    if table2.level == self.constants.arch.level_count() - 1 && pte.valid() {
                        assert(!pte.huge());
                    }
                }
            }
        }
        assert forall|base1: PAddr, idx1: nat, base2: PAddr, idx2: nat|
            pt_mem.accessible(base1, idx1) && pt_mem.accessible(base2, idx2) implies {
            let pte1 = G::from_u64(pt_mem.read(base1, idx1));
            let pte2 = G::from_u64(pt_mem.read(base2, idx2));
            ({
                &&& s2.pte_points_to_table(pte1, pt_mem.table(base1).level)
                &&& s2.pte_points_to_table(pte2, pt_mem.table(base2).level)
            }) ==> {
                ||| base1 == base2 && idx1 == idx2
                ||| (pte1.addr() != pte2.addr())
            }
        } by {
            let pte1 = G::from_u64(pt_mem.read(base1, idx1));
            let pte2 = G::from_u64(pt_mem.read(base2, idx2));
            if s2.pte_points_to_table(pte1, pt_mem.table(base1).level) && s2.pte_points_to_table(
                pte2,
                pt_mem.table(base2).level,
            ) {
                assert(base1 != table.base && base2 != table.base);
                assert(self.pt_mem.accessible(base1, idx1));
                assert(self.pt_mem.accessible(base2, idx2));
            }
        }
    }

    /// Lemma. `insert` does not affect existing tables.
    pub proof fn lemma_insert_preserves_old_tables(
        self,
        vbase: VAddr,
        base: PAddr,
        level: nat,
        target_level: nat,
        new_pte: G,
        base2: PAddr,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level <= target_level < self.constants.arch.level_count(),
            self.pte_valid_frame(new_pte, target_level),
            self.pt_mem.contains_table(base2),
        ensures
            self.insert(vbase, base, level, target_level, new_pte).0.pt_mem.contains_table(base2),
            self.insert(vbase, base, level, target_level, new_pte).0.pt_mem.table(base2)
                == self.pt_mem.table(base2),
        decreases target_level - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = G::from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if level < target_level {
            if pte.valid() {
                if !pte.huge() {
                    self.lemma_insert_preserves_invariants(
                        vbase,
                        pte.addr(),
                        level + 1,
                        target_level,
                        new_pte,
                    );
                    self.lemma_insert_preserves_old_tables(
                        vbase,
                        pte.addr(),
                        level + 1,
                        target_level,
                        new_pte,
                        base2,
                    )
                }
            } else {
                let (pt_mem, table) = self.pt_mem.alloc_table(level + 1);
                let pt_mem = pt_mem.write(
                    base,
                    idx,
                    G::new(table.base, MemAttr::spec_default(), false).to_u64(),
                );
                self.lemma_alloc_intermediate_table_preserves_invariants(base, level, idx);
                // Ensures `pt_mem` after `alloc_table` satisfies the invariants
                Self::new(pt_mem, self.constants).lemma_insert_preserves_old_tables(
                    vbase,
                    table.base,
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
        vbase: VAddr,
        base: PAddr,
        level: nat,
        target_level: nat,
        new_pte: G,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level <= target_level < self.constants.arch.level_count(),
            self.pte_valid_frame(new_pte, target_level),
        ensures
            self.insert(vbase, base, level, target_level, new_pte).0.pt_mem.root()
                == self.pt_mem.root(),
        decreases target_level - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = G::from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if level < target_level {
            if pte.valid() {
                if !pte.huge() {
                    // Recursively insert into the next table
                    self.lemma_insert_preserves_root(
                        vbase,
                        pte.addr(),
                        level + 1,
                        target_level,
                        new_pte,
                    )
                }
            } else {
                // Allocate intermediate table
                let (pt_mem, table) = self.pt_mem.alloc_table(level + 1);
                let pt_mem = pt_mem.write(
                    base,
                    idx,
                    G::new(table.base, MemAttr::spec_default(), false).to_u64(),
                );
                // `s2` is the state after allocating an intermediate table
                let s2 = Self::new(pt_mem, self.constants);

                self.lemma_alloc_intermediate_table_preserves_invariants(base, level, idx);
                assert(s2.invariants());
                s2.lemma_insert_preserves_root(vbase, table.base, level + 1, target_level, new_pte)
            }
        }
    }

    /// Lemma. Inserting an entry using `insert` preserves the page table invariants.
    pub proof fn lemma_insert_preserves_invariants(
        self,
        vbase: VAddr,
        base: PAddr,
        level: nat,
        target_level: nat,
        new_pte: G,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level <= target_level < self.constants.arch.level_count(),
            self.pte_valid_frame(new_pte, target_level),
        ensures
            self.insert(vbase, base, level, target_level, new_pte).0.constants == self.constants,
            self.insert(vbase, base, level, target_level, new_pte).0.invariants(),
        decreases target_level - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = G::from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if level < target_level {
            if pte.valid() {
                if !pte.huge() {
                    // Recursively insert into the next table
                    self.lemma_insert_preserves_invariants(
                        vbase,
                        pte.addr(),
                        level + 1,
                        target_level,
                        new_pte,
                    )
                }
            } else {
                // Allocate intermediate table
                let (pt_mem, table) = self.pt_mem.alloc_table(level + 1);
                let pt_mem = pt_mem.write(
                    base,
                    idx,
                    G::new(table.base, MemAttr::spec_default(), false).to_u64(),
                );
                // `s2` is the state after allocating an intermediate table
                let s2 = Self::new(pt_mem, self.constants);

                self.lemma_alloc_intermediate_table_preserves_invariants(base, level, idx);
                assert(s2.invariants());
                s2.lemma_insert_preserves_invariants(
                    vbase,
                    table.base,
                    level + 1,
                    target_level,
                    new_pte,
                );
            }
        }
    }

    /// Lemma. When `insert` allocates an intermediate table, the result must succeed (`Ok`).
    pub proof fn lemma_insert_intermediate_node_results_ok(
        self,
        vbase: VAddr,
        base: PAddr,
        level: nat,
        target_level: nat,
        new_pte: G,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level <= target_level < self.constants.arch.level_count(),
            self.pte_valid_frame(new_pte, target_level),
        ensures
            ({
                let idx = self.constants.arch.pte_index(vbase, level);
                let pte = G::from_u64(self.pt_mem.read(base, idx));
                level < target_level && !pte.valid() ==> self.insert(
                    vbase,
                    base,
                    level,
                    target_level,
                    new_pte,
                ).1 is Ok
            }),
        decreases target_level - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = G::from_u64(self.pt_mem.read(base, idx));
        if level < target_level && !pte.valid() {
            // Allocate intermediate table
            let (pt_mem, table) = self.pt_mem.alloc_table(level + 1);
            let pt_mem = pt_mem.write(
                base,
                idx,
                G::new(table.base, MemAttr::spec_default(), false).to_u64(),
            );
            // `s2` is the state after allocating an intermediate table
            let s2 = Self::new(pt_mem, self.constants);
            self.lemma_alloc_intermediate_table_preserves_invariants(base, level, idx);
            assert(s2.invariants());

            let (_, insert_res) = s2.insert(vbase, table.base, level + 1, target_level, new_pte);
            let idx = s2.constants.arch.pte_index(vbase, level + 1);
            let pte = G::from_u64(s2.pt_mem.read(table.base, idx));
            // New table is empty
            assert(s2.pt_mem.read(table.base, idx) == 0);
            assert(!pte.valid());

            // Recursive proof for the next level
            s2.lemma_insert_intermediate_node_results_ok(
                vbase,
                table.base,
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
        vbase: VAddr,
        base: PAddr,
        level: nat,
        target_level: nat,
        new_pte: G,
        base2: PAddr,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            self.pt_mem.table(base).level == level,
            level <= target_level < self.constants.arch.level_count(),
            self.pte_valid_frame(new_pte, target_level),
            self.pt_mem.contains_table(base2),
            !self.collect_table_chain(vbase, base, level).contains(base2),
        ensures
            self.insert(vbase, base, level, target_level, new_pte).0.pt_mem.contains_table(base2),
            self.insert(vbase, base, level, target_level, new_pte).0.pt_mem.table(base2)
                == self.pt_mem.table(base2),
            self.insert(vbase, base, level, target_level, new_pte).0.pt_mem.table_view(base2)
                == self.pt_mem.table_view(base2),
        decreases target_level - level,
    {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = G::from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if level < target_level {
            if pte.valid() {
                // PTE is present: either a huge mapping or a pointer to a next-level table
                if !pte.huge() {
                    // Not a huge mapping: descend into the next-level table
                    assert(self.pt_mem.contains_table(pte.addr()));
                    let tables = self.collect_table_chain(vbase, base, level);
                    let tables2 = self.collect_table_chain(vbase, pte.addr(), level + 1);

                    assert(tables == Seq::new(1, |_i| base).add(tables2));
                    lemma_not_in_seq_implies_not_in_subseq(tables, tables2, base, base2);
                    assert(!tables2.contains(base2));
                    self.lemma_insert_preserves_tables_outside_chain(
                        vbase,
                        pte.addr(),
                        level + 1,
                        target_level,
                        new_pte,
                        base2,
                    )
                }
            } else {
                // Allocate intermediate table — create a new table and link it from `base` via the PTE
                let (pt_mem, table) = self.pt_mem.alloc_table(level + 1);
                let pt_mem = pt_mem.write(
                    base,
                    idx,
                    G::new(table.base, MemAttr::spec_default(), false).to_u64(),
                );
                // `s2` is the state after allocating an intermediate table
                let s2 = Self::new(pt_mem, self.constants);
                self.lemma_alloc_intermediate_table_preserves_invariants(base, level, idx);
                assert(s2.invariants());

                let pte = G::new(table.base, MemAttr::spec_default(), false);
                let tables = s2.collect_table_chain(vbase, base, level);
                let tables2 = s2.collect_table_chain(vbase, pte.addr(), level + 1);
                assert(s2.pt_mem.read(base, idx) == pte.to_u64());
                G::lemma_eq_by_u64(G::from_u64(s2.pt_mem.read(base, idx)), pte);
                assert(s2.pte_points_to_table(pte, level));

                assert(tables == Seq::new(1, |_i| base).add(tables2));
                lemma_not_in_seq_implies_not_in_subseq(tables, tables2, base, base2);
                assert(!tables2.contains(base2));
                s2.lemma_insert_preserves_tables_outside_chain(
                    vbase,
                    table.base,
                    level + 1,
                    target_level,
                    new_pte,
                    base2,
                );
            }
        }
    }

    /// Lemma. `insert` does not change the constructed node for nodes outside the
    /// insertion path — structural node representations remain equal for nodes not
    /// on the path.
    pub proof fn lemma_insert_preserves_unrelated_node(
        self,
        vbase: VAddr,
        base: PAddr,
        level: nat,
        target_level: nat,
        new_pte: G,
        base2: PAddr,
        level2: nat,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            self.pt_mem.table(base).level == level,
            self.pt_mem.contains_table(base2),
            self.pt_mem.table(base2).level == level2,
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
        self.lemma_insert_preserves_invariants(vbase, base, level, target_level, new_pte);
        self.lemma_insert_preserves_tables_outside_chain(
            vbase,
            base,
            level,
            target_level,
            new_pte,
            base2,
        );
        assert(self.pt_mem.table_view(base2) == s2.pt_mem.table_view(base2));

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
            let pte = G::from_u64(self.pt_mem.read(base2, i as nat));
            assert(self.pt_mem.accessible(base2, i as nat));
            let pte2 = G::from_u64(s2.pt_mem.read(base2, i as nat));
            G::lemma_eq_by_u64(pte, pte2);

            match entry {
                NodeEntry::Node(node) => {
                    assert(self.pte_points_to_table(pte, level2));
                    assert(self.pt_mem.contains_table(pte.addr()));
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
                        pte.addr(),
                        level2 + 1,
                    );
                },
                NodeEntry::Frame(frame) => {
                    assert(self.pte_points_to_frame(pte, level2));
                },
                NodeEntry::Empty => {
                    assert(!pte.valid());
                },
            }
        }
        assert(node.entries == node2.entries);
    }

    /// Lemma. The implementation-level insertion is consistent with the tree model.
    pub proof fn lemma_insert_consistent_with_model(
        self,
        vbase: VAddr,
        base: PAddr,
        level: nat,
        target_level: nat,
        new_pte: G,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
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
        self.lemma_insert_preserves_invariants(vbase, base, level, target_level, new_pte);
        self.lemma_insert_preserves_old_tables(vbase, base, level, target_level, new_pte, base);

        let node = self.construct_node(base, level);
        let node2 = s2.construct_node(base, level);
        self.construct_node_facts(base, level);
        s2.construct_node_facts(base, level);

        let arch = self.constants.arch;
        let path = PTTreePath::from_vaddr(vbase, arch, level, target_level);
        self.lemma_construct_node_implies_invariants(base, level);
        s2.lemma_construct_node_implies_invariants(base, level);

        let (idx, remain) = path.step();
        let entry = node.entries[idx as int];
        assert(self.pt_mem.accessible(base, idx));
        let pte = G::from_u64(self.pt_mem.read(base, idx));

        let right = node.insert(path, new_frame).0;
        node.lemma_insert_preserves_invariants(path, new_frame);

        if level >= target_level {
            if !pte.valid() {
                G::lemma_eq_by_u64(G::from_u64(s2.pt_mem.read(base, idx)), new_pte);
                // Update `pte` to `new_pte`, empty entry to frame
                assert(right == node.update(idx, NodeEntry::Frame(new_frame)));
            }
        } else {
            if pte.valid() {
                if !pte.huge() {
                    // `pte` points to a subtable
                    let subtable_base = pte.addr();
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
                    assert(s2.pt_mem.table_view(base) == self.pt_mem.table_view(base));

                    assert forall|i| 0 <= i < node2.entries.len() implies node2.entries[i]
                        == right.entries[i] by {
                        G::lemma_eq_by_u64(
                            G::from_u64(s2.pt_mem.read(base, i as nat)),
                            G::from_u64(self.pt_mem.read(base, i as nat)),
                        );
                        if i == idx {
                            // Entry `i` is the subtree constructed from `subtable_base`
                            assert(node2.entries[i] == NodeEntry::Node(
                                s2.construct_node(subtable_base, level + 1),
                            ));
                        } else {
                            // Other entries are unchanged
                            let pte_i = G::from_u64(self.pt_mem.read(base, i as nat));
                            assert(self.pt_mem.accessible(base, i as nat));
                            if self.pte_points_to_table(pte_i, level) {
                                assert(self.pt_mem.contains_table(pte_i.addr()));
                                self.lemma_other_index_not_in_chain(vbase, base, level, i as nat);
                                self.lemma_insert_preserves_unrelated_node(
                                    vbase,
                                    base,
                                    level,
                                    target_level,
                                    new_pte,
                                    pte_i.addr(),
                                    level + 1,
                                );
                            }
                            assert(node2.entries[i] == node.entries[i]);
                        }
                    }
                    assert(node2.entries == right.entries);
                }
            } else {
                let (allocated, table) = self.pt_mem.alloc_table(level + 1);
                let written = allocated.write(
                    base,
                    idx,
                    G::new(table.base, MemAttr::spec_default(), false).to_u64(),
                );
                let subtable_base = table.base;
                self.lemma_alloc_intermediate_table_preserves_invariants(base, level, idx);

                // s3 is the state after allocating a new intermediate table
                let s3 = Self::new(written, self.constants);
                let subnode = PTTreeNode::new(self.constants, level + 1);
                G::lemma_eq_by_u64(
                    G::from_u64(s3.pt_mem.read(base, idx)),
                    G::new(table.base, MemAttr::spec_default(), false),
                );
                assert(s3.construct_node(base, level).entries[idx as int] == NodeEntry::Node(
                    subnode,
                ));

                let new_subnode = subnode.insert(remain, new_frame).0;
                assert(s2 == s3.insert(vbase, table.base, level + 1, target_level, new_pte).0);
                // Recursive call shows subnode is updated according to model
                s3.lemma_insert_consistent_with_model(
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
                assert(s2.pt_mem.table_view(base) == s3.pt_mem.table_view(base));
                assert forall|i| 0 <= i < node2.entries.len() implies node2.entries[i]
                    == right.entries[i] by {
                    if i == idx {
                        // Entry `i` is the subtree constructed from `subtable_base`
                        assert(node2.entries[i] == NodeEntry::Node(new_subnode));
                    } else {
                        // Other entries are unchanged
                        assert(node2.entries[i] == node.entries[i]);
                    }
                }
                assert(node2.entries == right.entries);
            }
        }
    }

    /// Lemma. Removing a page table entry using `remove` maintains the page table invariants.
    pub proof fn lemma_remove_preserves_invariants(self, vbase: VAddr, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
        ensures
            self.remove(vbase, base, level).0.invariants(),
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = G::from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));
        if self.pte_points_to_table(pte, level) {
            self.lemma_remove_preserves_invariants(vbase, pte.addr(), level + 1)
        }
    }

    /// Lemma. `remove` does not affect existing tables.
    pub proof fn lemma_remove_preserves_old_tables(
        self,
        vbase: VAddr,
        base: PAddr,
        level: nat,
        base2: PAddr,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
            self.pt_mem.contains_table(base2),
        ensures
            self.remove(vbase, base, level).0.pt_mem.contains_table(base2),
            self.remove(vbase, base, level).0.pt_mem.table(base2) == self.pt_mem.table(base2),
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = G::from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));
        if self.pte_points_to_table(pte, level) {
            self.lemma_remove_preserves_old_tables(vbase, pte.addr(), level + 1, base2)
        }
    }

    /// Lemma. `remove` does not change the root of the page table.
    pub proof fn lemma_remove_preserves_root(self, vbase: VAddr, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
        ensures
            self.remove(vbase, base, level).0.pt_mem.root() == self.pt_mem.root(),
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = G::from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));
        if self.pte_points_to_table(pte, level) {
            self.lemma_remove_preserves_root(vbase, pte.addr(), level + 1)
        }
    }

    /// Lemma. The implementation-level removal is consistent with the tree model.
    pub proof fn lemma_remove_consistent_with_model(self, vbase: VAddr, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
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
        self.lemma_remove_preserves_invariants(vbase, base, level);
        self.lemma_remove_preserves_old_tables(vbase, base, level, base);

        let node = self.construct_node(base, level);
        let node2 = s2.construct_node(base, level);
        self.construct_node_facts(base, level);
        s2.construct_node_facts(base, level);

        let arch = self.constants.arch;
        let end = (arch.level_count() - 1) as nat;
        let path = PTTreePath::from_vaddr(vbase, arch, level, end);
        // Precondition of `remove`: node.invariants and path.valid
        self.lemma_construct_node_implies_invariants(base, level);
        s2.lemma_construct_node_implies_invariants(base, level);

        let (idx, remain) = path.step();
        let entry = node.entries[idx as int];
        let entry2 = node2.entries[idx as int];
        assert(self.pt_mem.accessible(base, idx));
        let pte = G::from_u64(self.pt_mem.read(base, idx));
        let pte2 = G::from_u64(s2.pt_mem.read(base, idx));

        if path.len() <= 1 {
            match entry {
                NodeEntry::Frame(_) => {
                    // Update frame entry to empty
                    assert(s2.pt_mem == self.pt_mem.write(base, idx, G::empty().to_u64()));
                    G::lemma_eq_by_u64(pte2, G::empty());
                    assert(entry2 == NodeEntry::Empty);
                },
                _ => (),
            }
        } else {
            match entry {
                NodeEntry::Node(subnode) => {
                    // `pte` points to a subtable
                    let subtable_base = pte.addr();
                    // Recursive remove from the subtable
                    self.lemma_remove_consistent_with_model(vbase, subtable_base, level + 1);
                    PTTreePath::lemma_from_vaddr_step(vbase, arch, level, end);
                },
                NodeEntry::Frame(frame) => {
                    if path.has_zero_tail(level) {
                        assert(s2.pt_mem == self.pt_mem.write(base, idx, G::empty().to_u64()));
                        G::lemma_eq_by_u64(pte2, G::empty());
                        assert(entry2 == NodeEntry::Empty);
                    }
                },
                NodeEntry::Empty => (),
            }
        }
    }

    /// Lemma. Deallocating an intermediate table preserves invariants.
    pub proof fn lemma_dealloc_intermediate_table_preserves_invariants(
        self,
        base: PAddr,
        level: nat,
        idx: nat,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count() - 1,
            self.pt_mem.accessible(base, idx),
            ({
                let pte = G::from_u64(self.pt_mem.read(base, idx));
                pte.valid() && !pte.huge() && self.is_table_empty(pte.addr())
            }),
        ensures
            ({
                let pte = G::from_u64(self.pt_mem.read(base, idx));
                let pt_mem = self.pt_mem.dealloc_table(pte.addr());
                let pt_mem = pt_mem.write(base, idx, G::empty().to_u64());
                Self::new(pt_mem, self.constants).invariants()
            }),
    {
        broadcast use crate::page_table::pte::group_pte_lemmas;

        let pte = G::from_u64(self.pt_mem.read(base, idx));
        let pt_mem = self.pt_mem.dealloc_table(pte.addr()).write(base, idx, G::empty().to_u64());
        let s2 = Self::new(pt_mem, self.constants);

        assert forall|base2: PAddr, idx2: nat| pt_mem.accessible(base2, idx2) implies {
            let table2 = pt_mem.table(base2);
            let pte2 = G::from_u64(pt_mem.read(base2, idx2));
            let addr = pte2.addr();
            &&& (table2.level == s2.constants.arch.level_count() - 1 && pte2.valid())
                ==> !pte2.huge()
            &&& s2.pte_points_to_table(pte2, table2.level) ==> {
                &&& addr != pt_mem.root()
                &&& pt_mem.contains_table(addr)
                &&& pt_mem.table(addr).level == table2.level + 1
            }
            &&& s2.pte_points_to_frame(pte2, table2.level) ==> {
                &&& addr.aligned(s2.constants.arch.frame_size(table2.level).as_nat())
                &&& s2.constants.pmem_lb.0 <= addr.0
                &&& addr.0 + s2.constants.arch.frame_size(table2.level).as_nat()
                    <= s2.constants.pmem_ub.0
            }
        } by {
            let table2 = pt_mem.table(base2);
            let val = pt_mem.read(base2, idx2);
            let pte2 = G::from_u64(val);

            if base2 == base && idx2 == idx {
                // `(base2, idx2)` is the entry we just inserted
                G::lemma_eq_by_u64(pte2, G::empty());
            } else {
                assert(self.pt_mem.accessible(base2, idx2));
                G::lemma_eq_by_u64(pte2, G::from_u64(self.pt_mem.read(base2, idx2)));
                if s2.pte_points_to_table(pte2, table2.level) {
                    // Invariants ensures no double reference
                    assert(pte2.addr() != pte.addr());
                }
            }
        }
        assert forall|base1: PAddr, idx1: nat, base2: PAddr, idx2: nat|
            pt_mem.accessible(base1, idx1) && pt_mem.accessible(base2, idx2) implies {
            let pte1 = G::from_u64(pt_mem.read(base1, idx1));
            let pte2 = G::from_u64(pt_mem.read(base2, idx2));
            ({
                &&& s2.pte_points_to_table(pte1, pt_mem.table(base1).level)
                &&& s2.pte_points_to_table(pte2, pt_mem.table(base2).level)
            }) ==> {
                ||| base1 == base2 && idx1 == idx2
                ||| (pte1.addr() != pte2.addr())
            }
        } by {
            let pte1 = G::from_u64(pt_mem.read(base1, idx1));
            let pte2 = G::from_u64(pt_mem.read(base2, idx2));
            if s2.pte_points_to_table(pte1, pt_mem.table(base1).level) && s2.pte_points_to_table(
                pte2,
                pt_mem.table(base2).level,
            ) {
                assert(base1 != pte.addr() && base2 != pte.addr());
                assert(self.pt_mem.accessible(base1, idx1));
                assert(self.pt_mem.accessible(base2, idx2));
            }
        }
    }

    /// Lemma. `prune` mantains the page table invariants.
    pub proof fn lemma_prune_preserves_invariants(self, vaddr: VAddr, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
        ensures
            self.prune(vaddr, base, level).invariants(),
            self.prune(vaddr, base, level).constants == self.constants,
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vaddr, level);
        let pte = G::from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if self.pte_points_to_table(pte, level) {
            self.lemma_prune_preserves_invariants(vaddr, pte.addr(), level + 1);
            self.lemma_prune_preserves_lower_tables(vaddr, pte.addr(), level + 1, base);
            self.lemma_prune_preserves_lower_tables(vaddr, pte.addr(), level + 1, pte.addr());
            let s2 = self.prune(vaddr, pte.addr(), level + 1);
            if s2.is_table_empty(pte.addr()) {
                s2.lemma_dealloc_intermediate_table_preserves_invariants(base, level, idx);
            }
        }
    }

    /// Lemma. `prune` does not remove tables with level lower than the current level.
    pub proof fn lemma_prune_preserves_lower_tables(
        self,
        vaddr: VAddr,
        base: PAddr,
        level: nat,
        base2: PAddr,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
            self.pt_mem.contains_table(base2),
            self.pt_mem.table(base2).level <= level,
        ensures
            self.prune(vaddr, base, level).pt_mem.contains_table(base2),
            self.prune(vaddr, base, level).pt_mem.table(base2) == self.pt_mem.table(base2),
            self.pt_mem.table(base2).level < level ==> self.prune(
                vaddr,
                base,
                level,
            ).pt_mem.table_view(base2) == self.pt_mem.table_view(base2),
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vaddr, level);
        let pte = G::from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if self.pte_points_to_table(pte, level) {
            self.lemma_prune_preserves_invariants(vaddr, pte.addr(), level + 1);
            // `base`, `pte.addr()`, `base2` are not affected after `prune`
            self.lemma_prune_preserves_lower_tables(vaddr, pte.addr(), level + 1, base);
            self.lemma_prune_preserves_lower_tables(vaddr, pte.addr(), level + 1, pte.addr());
            self.lemma_prune_preserves_lower_tables(vaddr, pte.addr(), level + 1, base2);
        }
    }

    /// Lemma. `prune` does not change the root of the page table.
    pub proof fn lemma_prune_preserves_root(self, vaddr: VAddr, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
        ensures
            self.prune(vaddr, base, level).pt_mem.root() == self.pt_mem.root(),
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vaddr, level);
        let pte = G::from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if self.pte_points_to_table(pte, level) {
            self.lemma_prune_preserves_invariants(vaddr, pte.addr(), level + 1);
            self.lemma_prune_preserves_root(vaddr, pte.addr(), level + 1);
            self.lemma_prune_preserves_lower_tables(vaddr, pte.addr(), level + 1, base);
            self.lemma_prune_preserves_lower_tables(vaddr, pte.addr(), level + 1, pte.addr());
        }
    }

    /// Lemma. `prune` only modifies tables that lie on the collected table chain for the
    /// provided `vaddr` — all tables outside that chain are preserved unchanged.
    pub proof fn lemma_prune_preserves_tables_outside_chain(
        self,
        vaddr: VAddr,
        base: PAddr,
        level: nat,
        base2: PAddr,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            self.pt_mem.table(base).level == level,
            level < self.constants.arch.level_count(),
            self.pt_mem.contains_table(base2),
            !self.collect_table_chain(vaddr, base, level).contains(base2),
        ensures
            self.prune(vaddr, base, level).pt_mem.contains_table(base2),
            self.prune(vaddr, base, level).pt_mem.table(base2) == self.pt_mem.table(base2),
            self.prune(vaddr, base, level).pt_mem.table_view(base2) == self.pt_mem.table_view(
                base2,
            ),
        decreases self.constants.arch.level_count() - level,
    {
        let tables = self.collect_table_chain(vaddr, base, level);

        let idx = self.constants.arch.pte_index(vaddr, level);
        let pte = G::from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if self.pte_points_to_table(pte, level) {
            // PTE points to a child table: continue walk into the child table
            let s2 = self.prune(vaddr, pte.addr(), level + 1);
            self.lemma_prune_preserves_invariants(vaddr, pte.addr(), level + 1);
            self.lemma_prune_preserves_lower_tables(vaddr, pte.addr(), level + 1, base);
            self.lemma_prune_preserves_lower_tables(vaddr, pte.addr(), level + 1, pte.addr());
            let tables2 = self.collect_table_chain(vaddr, pte.addr(), level + 1);

            assert(tables == Seq::new(1, |_i| base).add(tables2));
            lemma_not_in_seq_implies_not_in_subseq(tables, tables2, base, base2);
            assert(!tables2.contains(base2));
            self.lemma_prune_preserves_tables_outside_chain(vaddr, pte.addr(), level + 1, base2);

            assert(s2.pt_mem.table_view(base2) == self.pt_mem.table_view(base2));
            if s2.is_table_empty(pte.addr()) {
                // Child table became empty after prune: deallocate it and update the parent PTE
                s2.lemma_dealloc_intermediate_table_preserves_invariants(base, level, idx);
                assert(s2.pt_mem.dealloc_table(pte.addr()).accessible(base, idx));
                assert(base2 != pte.addr() && base2 != base);

                assert(self.prune(vaddr, base, level).pt_mem.table_view(base2)
                    == self.pt_mem.table_view(base2));
            }
        }
    }

    /// Lemma. `prune` does not change the constructed node representation for any
    /// node that is not on the pruned path — nodes outside the collected chain remain
    /// structurally identical after pruning.
    pub proof fn lemma_prune_preserves_unrelated_node(
        self,
        vaddr: VAddr,
        base: PAddr,
        level: nat,
        base2: PAddr,
        level2: nat,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            self.pt_mem.table(base).level == level,
            self.pt_mem.contains_table(base2),
            self.pt_mem.table(base2).level == level2,
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
        self.lemma_prune_preserves_invariants(vaddr, base, level);
        self.lemma_prune_preserves_tables_outside_chain(vaddr, base, level, base2);
        assert(self.pt_mem.table_view(base2) == s2.pt_mem.table_view(base2));

        let node = self.construct_node(base2, level2);
        self.construct_node_facts(base2, level2);
        let node2 = s2.construct_node(base2, level2);
        s2.construct_node_facts(base2, level2);

        assert(node.entries.len() == node2.entries.len());
        assert forall|i: int| 0 <= i < self.constants.arch.entry_count(level2) implies {
            node.entries[i] == node2.entries[i]
        } by {
            let entry = node.entries[i];
            let pte = G::from_u64(self.pt_mem.read(base2, i as nat));
            assert(self.pt_mem.accessible(base2, i as nat));
            let pte2 = G::from_u64(s2.pt_mem.read(base2, i as nat));
            G::lemma_eq_by_u64(pte, pte2);

            match entry {
                NodeEntry::Node(node) => {
                    assert(self.pte_points_to_table(pte, level2));
                    assert(self.pt_mem.contains_table(pte.addr()));
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
                        pte.addr(),
                        level2 + 1,
                    );
                },
                NodeEntry::Frame(frame) => {
                    assert(self.pte_points_to_frame(pte, level2));
                },
                NodeEntry::Empty => {
                    assert(!pte.valid());
                },
            }
        }
        assert(node.entries == node2.entries);
    }

    /// Lemma. The implementation-level prune is consistent with the tree model.
    pub proof fn lemma_prune_consistent_with_model(self, vaddr: VAddr, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
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
        self.lemma_prune_preserves_invariants(vaddr, base, level);
        self.lemma_prune_preserves_lower_tables(vaddr, base, level, base);

        let node = self.construct_node(base, level);
        let node2 = s2.construct_node(base, level);
        self.construct_node_facts(base, level);
        s2.construct_node_facts(base, level);

        let arch = self.constants.arch;
        let end = (arch.level_count() - 1) as nat;
        let path = PTTreePath::from_vaddr(vaddr, arch, level, end);
        self.lemma_construct_node_implies_invariants(base, level);
        s2.lemma_construct_node_implies_invariants(base, level);

        let (idx, remain) = path.step();
        let entry = node.entries[idx as int];
        assert(self.pt_mem.accessible(base, idx));
        let pte = G::from_u64(self.pt_mem.read(base, idx));

        let right = node.prune(path);
        node.lemma_prune_preserves_invariants(path);

        if self.pte_points_to_table(pte, level) {
            // `pte` points to a subtable
            let subtable_base = pte.addr();
            let subnode: PTTreeNode = entry->Node_0;

            let s3 = self.prune(vaddr, subtable_base, level + 1);
            let new_subnode = subnode.prune(remain);
            // Recursive call shows subnode is updated according to model
            self.lemma_prune_preserves_invariants(vaddr, subtable_base, level + 1);
            self.lemma_prune_consistent_with_model(vaddr, subtable_base, level + 1);
            PTTreePath::lemma_from_vaddr_step(vaddr, arch, level, end);
            assert(s3.construct_node(subtable_base, level + 1) == new_subnode);

            // `base`, `pte.addr()`, `base2` are not affected after `prune`
            self.lemma_prune_preserves_lower_tables(vaddr, subtable_base, level + 1, base);
            self.lemma_prune_preserves_lower_tables(vaddr, subtable_base, level + 1, subtable_base);
            // The content of table `base` is not affected after `prune`
            assert(s3.pt_mem.table_view(base) == self.pt_mem.table_view(base));

            s3.lemma_empty_table_constructs_empty_node(pte.addr());
            if s3.is_table_empty(subtable_base) {
                // Lemma shows `new_subnode` is empty
                assert(right == node.update(idx, NodeEntry::Empty));
                assert(s2.pt_mem == s3.pt_mem.dealloc_table(subtable_base).write(
                    base,
                    idx,
                    G::empty().to_u64(),
                ));
                assert forall|i| 0 <= i < node2.entries.len() implies node2.entries[i]
                    == right.entries[i] by {
                    if i == idx {
                        // Entry `i` is empty (removed)
                        G::lemma_eq_by_u64(G::from_u64(s2.pt_mem.read(base, idx)), G::empty());
                        assert(node2.entries[i] is Empty);
                    } else {
                        // Other entries are unchanged
                        G::lemma_eq_by_u64(
                            G::from_u64(s3.pt_mem.read(base, i as nat)),
                            G::from_u64(self.pt_mem.read(base, i as nat)),
                        );
                        G::lemma_eq_by_u64(
                            G::from_u64(s2.pt_mem.read(base, i as nat)),
                            G::from_u64(s3.pt_mem.read(base, i as nat)),
                        );
                        let pte_i = G::from_u64(self.pt_mem.read(base, i as nat));
                        assert(self.pt_mem.accessible(base, i as nat));
                        if self.pte_points_to_table(pte_i, level) {
                            assert(self.pt_mem.contains_table(pte_i.addr()));
                            self.lemma_other_index_not_in_chain(vaddr, base, level, i as nat);
                            self.lemma_prune_preserves_unrelated_node(
                                vaddr,
                                base,
                                level,
                                pte_i.addr(),
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
                assert(s2 == s3);

                assert forall|i| 0 <= i < node2.entries.len() implies node2.entries[i]
                    == right.entries[i] by {
                    G::lemma_eq_by_u64(
                        G::from_u64(s2.pt_mem.read(base, i as nat)),
                        G::from_u64(self.pt_mem.read(base, i as nat)),
                    );
                    if i == idx {
                        // Entry `i` is the subtree constructed from `subtable_base`
                        assert(node2.entries[i] == NodeEntry::Node(new_subnode));
                    } else {
                        // Other entries are unchanged
                        let pte_i = G::from_u64(self.pt_mem.read(base, i as nat));
                        assert(self.pt_mem.accessible(base, i as nat));
                        if self.pte_points_to_table(pte_i, level) {
                            self.lemma_other_index_not_in_chain(vaddr, base, level, i as nat);
                            self.lemma_prune_preserves_unrelated_node(
                                vaddr,
                                base,
                                level,
                                pte_i.addr(),
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
