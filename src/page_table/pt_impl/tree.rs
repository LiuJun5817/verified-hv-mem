//! Abstraction of the page table as a tree model. Used for refinement proofs.
use vstd::prelude::*;

use super::path::PTTreePath;
use crate::address::{
    addr::{SpecPAddr, SpecVAddr},
    frame::SpecFrame,
};
use crate::page_table::{
    pt_arch::SpecPTArch,
    pt_trait::{PageTableState, PagingResult, SpecPTConstants},
};

verus! {

// Use path related lemmas.
broadcast use super::path::group_pt_tree_path_lemmas;

/// Represents a node in the page table tree, which can be either an intermediate node
/// or a leaf node mapping to a physical frame.
pub struct PTTreeNode {
    /// Page table config constants.
    pub constants: SpecPTConstants,
    /// The level of the node in the page table hierarchy.
    pub level: nat,
    /// The entries of the node, which can be either sub-nodes, frames, or empty entries.
    pub entries: Seq<NodeEntry>,
}

/// Represents an entry in the page table node, which can be a sub-node, a physical frame,
/// or an empty entry.
pub enum NodeEntry {
    /// A sub-node in the page table, representing an intermediate level of the page table hierarchy.
    Node(PTTreeNode),
    /// A physical frame mapped by the node, representing a leaf node in the page table tree.
    Frame(SpecFrame),
    /// An empty entry in the page table, indicating that the corresponding virtual address range
    /// is not currently mapped or allocated.
    Empty,
}

impl PTTreeNode {
    /// If a node entry at the specified level is valid under the given configuration.
    pub open spec fn is_entry_valid(
        entry: NodeEntry,
        level: nat,
        constants: SpecPTConstants,
    ) -> bool
        recommends
            level < constants.arch.level_count(),
    {
        match entry {
            NodeEntry::Node(node) => if level < constants.arch.level_count() - 1 {
                &&& node.level == level
                    + 1
                // All nodes share the same configuration.
                &&& node.constants == constants
            } else {
                false
            },
            NodeEntry::Frame(frame) => {
                &&& frame.size == constants.arch.frame_size(level)
                &&& frame.base.aligned(frame.size.as_nat())
                &&& frame.base.0 >= constants.pmem_lb.0
                &&& frame.base.0 + frame.size.as_nat() <= constants.pmem_ub.0
            },
            NodeEntry::Empty => true,
        }
    }

    /// Well-formedness of the node. Recursively checks the wf of the node and its sub-nodes.
    ///
    /// This ensures a sub-tree is well-formed, and all mappings are valid and aligned.
    pub open spec fn wf(self) -> bool
        decreases self.constants.arch.level_count() - self.level,
    {
        &&& self.constants.arch.valid()
        &&& self.level < self.constants.arch.level_count()
        &&& self.entries.len() == self.constants.arch.entry_count(
            self.level,
        )
        // wf satisfied recursively
        &&& forall|entry: NodeEntry| #[trigger]
            self.entries.contains(entry) ==> {
                &&& Self::is_entry_valid(entry, self.level, self.constants)
                &&& entry is Node ==> entry->Node_0.wf()
            }
    }

    /// Additional wf. If there are no empty nodes in a subtree.
    pub open spec fn fully_populated(self) -> bool
        recommends
            self.wf(),
        decreases self.constants.arch.level_count() - self.level,
    {
        &&& if self.level >= self.constants.arch.level_count() - 1 {
            // Leaf node must have at least one frame entry
            exists|entry: NodeEntry| #[trigger] self.entries.contains(entry) && entry is Frame
        } else {
            // Intermediate node must have at least one sub-node or frame entry
            // Only root node can have empty entries
            exists|entry: NodeEntry| #[trigger]
                self.entries.contains(entry) && (entry is Node || entry is Frame)
        }
        // Nonempty property satisfied recursively
        &&& forall|entry: NodeEntry| #[trigger]
            self.entries.contains(entry) && Self::is_entry_valid(entry, self.level, self.constants)
                && entry is Node ==> entry->Node_0.fully_populated()
    }

    /// If all entries are empty.
    pub open spec fn empty(self) -> bool {
        forall|entry: NodeEntry| #[trigger] self.entries.contains(entry) ==> entry is Empty
    }

    /// Creates an empty node.
    pub open spec fn new(constants: SpecPTConstants, level: nat) -> Self
        recommends
            level < constants.arch.level_count(),
            constants.arch.valid(),
    {
        Self {
            constants,
            level,
            entries: Seq::new(constants.arch.entry_count(level), |_i| NodeEntry::Empty),
        }
    }

    /// Update an entry in the node at the specified index.
    pub open spec fn update(self, index: nat, entry: NodeEntry) -> Self
        recommends
            index < self.entries.len(),
            Self::is_entry_valid(entry, self.level, self.constants),
    {
        Self { entries: self.entries.update(index as int, entry), ..self }
    }

    /// Visit the tree along `path` and return the sequence of entries visited.
    ///
    /// If a reached entry is `Empty` and `path` is not empty, then the visit
    /// terminates early and returns the sequence of entries visited so far.
    pub open spec fn visit(self, path: PTTreePath) -> Seq<NodeEntry>
        recommends
            self.wf(),
            path.valid(self.constants.arch, self.level),
        decreases path.len(),
    {
        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        if path.len() <= 1 {
            Seq::new(1, |_i| entry)
        } else {
            match entry {
                NodeEntry::Node(node) => Seq::new(1, |_i| entry).add(node.visit(remain)),
                _ => Seq::new(1, |_i| entry),
            }
        }
    }

    /// Inserts a frame at `path`, creates intermediate nodes if needed.
    ///
    /// Does nothing if target slot is non-empty.
    pub open spec fn insert(self, path: PTTreePath, frame: SpecFrame) -> (Self, PagingResult)
        recommends
            self.wf(),
            path.valid(self.constants.arch, self.level),
            Self::is_entry_valid(
                NodeEntry::Frame(frame),
                (self.level + path.len() - 1) as nat,
                self.constants,
            ),
        decreases path.len(),
    {
        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        if path.len() <= 1 {
            match entry {
                NodeEntry::Empty => (self.update(idx, NodeEntry::Frame(frame)), Ok(())),
                _ => (self, Err(())),
            }
        } else {
            match entry {
                NodeEntry::Node(node) => {
                    let (node, res) = node.insert(remain, frame);
                    (self.update(idx, NodeEntry::Node(node)), res)
                },
                NodeEntry::Empty => {
                    let (node, res) = Self::new(self.constants, self.level + 1).insert(
                        remain,
                        frame,
                    );
                    (self.update(idx, NodeEntry::Node(node)), res)
                },
                _ => (self, Err(())),
            }
        }
    }

    /// Removes a frame at `path` by setting it to `Empty`.
    ///
    /// Does nothing if the entry at `path` is already `Empty`.
    pub open spec fn remove(self, path: PTTreePath) -> (Self, PagingResult)
        recommends
            self.wf(),
            path.valid(self.constants.arch, self.level),
        decreases path.len(),
    {
        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        if path.len() <= 1 {
            match entry {
                NodeEntry::Frame(_) => (self.update(idx, NodeEntry::Empty), Ok(())),
                _ => (self, Err(())),
            }
        } else {
            match entry {
                NodeEntry::Node(node) => {
                    let (node, res) = node.remove(remain);
                    (self.update(idx, NodeEntry::Node(node)), res)
                },
                NodeEntry::Frame(frame) => {
                    if remain.is_zero() {
                        (self.update(idx, NodeEntry::Empty), Ok(()))
                    } else {
                        (self, Err(()))
                    }
                },
                _ => (self, Err(())),
            }
        }
    }

    /// Recursively eliminate empty nodes along `path`.
    pub open spec fn prune(self, path: PTTreePath) -> Self
        recommends
            self.wf(),
            path.valid(self.constants.arch, self.level),
        decreases path.len(),
    {
        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        if path.len() <= 1 {
            // Leaf node.
            self
        } else {
            match entry {
                NodeEntry::Node(node) => {
                    // Recycle subnode.
                    let new_node = node.prune(remain);
                    if new_node.empty() {
                        // If subnode is empty, mark the entry as empty.
                        self.update(idx, NodeEntry::Empty)
                    } else {
                        // Otherwise, update the entry
                        self.update(idx, NodeEntry::Node(new_node))
                    }
                },
                _ => self,  // entry is Frame
            }
        }
    }

    /// Returns the longest prefix of `path` that can reach an entry without early terminating.
    pub open spec fn real_path(self, path: PTTreePath) -> PTTreePath
        recommends
            self.wf(),
            path.valid(self.constants.arch, self.level),
    {
        path.trim(self.visit(path).len())
    }

    /// If `visit(path)` terminates exactly at a frame.
    pub open spec fn is_frame_path(self, path: PTTreePath) -> bool
        recommends
            self.wf(),
    {
        path.valid(self.constants.arch, self.level) && self.visit(path).last() is Frame
            && self.visit(path).len() == path.len()
    }

    /// Collect all paths that terminate at a frame as a map.
    pub open spec fn path_mappings(self) -> Map<PTTreePath, SpecFrame>
        recommends
            self.wf(),
    {
        Map::new(|path| self.is_frame_path(path), |path| self.visit(path).last()->Frame_0)
    }

    /// Lemma. `new` implies wf.
    pub proof fn lemma_new_implies_wf(constants: SpecPTConstants, level: nat)
        requires
            level < constants.arch.level_count(),
            constants.arch.valid(),
        ensures
            Self::new(constants, level).wf(),
    {
    }

    /// Lemma. `update` preserves wf.
    pub proof fn lemma_update_preserves_wf(self, index: nat, entry: NodeEntry)
        requires
            self.wf(),
            0 <= index < self.entries.len(),
            Self::is_entry_valid(entry, self.level, self.constants),
            entry is Node ==> entry->Node_0.wf(),
        ensures
            self.update(index, entry).wf(),
    {
        let new = self.update(index, entry);
        assert forall|entry2: NodeEntry| #[trigger]
            new.entries.contains(entry2) implies Self::is_entry_valid(
            entry2,
            self.level,
            self.constants,
        ) by {
            if entry2 != entry {
                assert(self.entries.contains(entry2));
            }
        }
        assert forall|entry2: NodeEntry| #[trigger]
            new.entries.contains(entry2) implies match entry2 {
            NodeEntry::Node(node) => node.wf(),
            _ => true,
        } by {
            if entry2 != entry {
                assert(self.entries.contains(entry2));
            }
        }
    }

    /* `visit` related lemmas */
    /// Lemma. Length of `visit(path)` is between 1 and `path.len()`.
    pub proof fn lemma_visit_length_bounds(self, path: PTTreePath)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
        ensures
            1 <= self.visit(path).len() <= path.len(),
        decreases path.len(),
    {
        if path.len() <= 1 {
            assert(self.visit(path).len() == 1);
        } else {
            let (idx, remain) = path.step();
            let entry = self.entries[idx as int];
            assert(self.entries.contains(entry));
            match entry {
                NodeEntry::Node(node) => {
                    node.lemma_visit_length_bounds(remain);
                },
                _ => assert(self.visit(path).len() == 1),
            }
        }
    }

    /// Lemma. Every entry returned by `visit` satisfies `is_entry_valid`.
    pub proof fn lemma_visited_entries_satisfy_wf(self, path: PTTreePath)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
        ensures
            forall|i: int|
                #![auto]
                0 <= i < self.visit(path).len() ==> Self::is_entry_valid(
                    self.visit(path)[i],
                    self.level + i as nat,
                    self.constants,
                ),
        decreases path.len(),
    {
        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        assert(self.entries.contains(entry));
        assert(Self::is_entry_valid(entry, self.level, self.constants));
        if path.len() > 1 {
            match entry {
                NodeEntry::Node(node) => {
                    assert(self.visit(path) === Seq::new(1, |_i| entry).add(node.visit(remain)));
                    // Recursively prove `node.visit(remain)` satisfies the wf
                    node.lemma_visited_entries_satisfy_wf(remain);
                },
                _ => (),
            }
        }
    }

    /// Lemma. All visited entries except the final one must be sub-nodes.
    pub proof fn lemma_visited_entry_is_node_except_final(self, path: PTTreePath)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
        ensures
            forall|i| 0 <= i < self.visit(path).len() - 1 ==> self.visit(path)[i] is Node,
        decreases path.len(),
    {
        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        assert(self.entries.contains(entry));
        assert(Self::is_entry_valid(entry, self.level, self.constants));
        if path.len() > 1 {
            match entry {
                NodeEntry::Node(node) => {
                    assert(self.visit(path) === Seq::new(1, |_i| entry).add(node.visit(remain)));
                    // Recursively prove `node.visit(remain)`
                    node.lemma_visited_entry_is_node_except_final(remain);
                },
                _ => (),
            }
        }
    }

    /// Lemma. If `prefix` is a prefix of `path`, then the visit sequence of `prefix`
    /// is a prefix of that of `path`.
    pub proof fn lemma_visit_preserves_prefix(self, path: PTTreePath, prefix: PTTreePath)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
            path.has_prefix(prefix),
        ensures
            self.visit(prefix).len() <= self.visit(path).len(),
            forall|i|
                0 <= i < self.visit(prefix).len() ==> self.visit(prefix)[i] === self.visit(path)[i],
        decreases path.len(),
    {
        let visited = self.visit(path);
        let p_visited = self.visit(prefix);
        let (idx, remain) = path.step();
        let (p_idx, p_remain) = prefix.step();
        assert(p_idx == idx);
        let entry = self.entries[p_idx as int];
        assert(self.entries.contains(entry));

        if prefix.len() > 1 {
            match entry {
                NodeEntry::Node(node) => {
                    assert(visited == Seq::new(1, |_i| entry).add(node.visit(remain)));
                    assert(p_visited == Seq::new(1, |_i| entry).add(node.visit(p_remain)));
                    // Recursively prove `node.visit(remain)`
                    node.lemma_visit_preserves_prefix(remain, p_remain);
                    assert forall|i| 0 < i < p_visited.len() implies p_visited[i] == visited[i] by {
                        assert(p_visited[i] == node.visit(p_remain)[i - 1]);
                        assert(visited[i] == node.visit(remain)[i - 1]);
                    }
                },
                _ => (),
            }
        }
    }

    /* `real_path` related lemmas */
    /// Lemma. If `path` is valid, then `real_path(path)` is also valid.
    pub proof fn lemma_real_path_valid(self, path: PTTreePath)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
        ensures
            self.real_path(path).valid(self.constants.arch, self.level),
    {
        self.lemma_visit_length_bounds(path);
    }

    /// Lemma. `real_path(path)` is a prefix of `path`.
    pub proof fn lemma_real_path_is_prefix(self, path: PTTreePath)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
        ensures
            path.has_prefix(self.real_path(path)),
    {
        self.lemma_visit_length_bounds(path);
    }

    /// Lemma. `self.real_path(path).step() == (idx, node.real_path(remain))`
    pub proof fn lemma_real_path_step(self, path: PTTreePath)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
            path.len() > 1,
            self.entries[path.step().0 as int] is Node,
        ensures
            ({
                let (idx, remain) = path.step();
                let node = self.entries[idx as int]->Node_0;
                self.real_path(path).step() == (idx, node.real_path(remain))
            }),
    {
        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        assert(self.entries.contains(entry));
        let node: PTTreeNode = entry->Node_0;

        assert(self.visit(path) == Seq::new(1, |_i| entry).add(node.visit(remain)));
        self.lemma_visit_length_bounds(path);
        node.lemma_visit_length_bounds(remain);
        // Left side
        let rp1 = self.real_path(path);
        let len1 = self.visit(path).len() as int;
        assert(rp1.0 == path.0.take(len1));
        // Right side
        let rp2 = node.real_path(remain);
        let len2 = node.visit(remain).len() as int;
        assert(rp2.0 == path.0.skip(1).take(len2));

        assert(len1 == len2 + 1);
        // `skip` and `take` are exchangeable
        assert(path.0.take(len2 + 1).skip(1) == path.0.skip(1).take(len2));
    }

    /// Lemma. The entry sequence visited by `path` and `real_path(path)` are the same.
    pub proof fn lemma_real_path_visits_same_entry(self, path: PTTreePath)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
        ensures
            self.visit(self.real_path(path)) == self.visit(path),
        decreases path.len(),
    {
        let r_path = self.real_path(path);
        let visited = self.visit(path);
        let r_visited = self.visit(r_path);

        let (idx, remain) = path.step();
        let (r_idx, r_remain) = r_path.step();
        self.lemma_visit_length_bounds(path);
        self.lemma_visit_length_bounds(r_path);
        assert(idx == r_idx);
        let entry = self.entries[r_idx as int];
        assert(self.entries.contains(entry));

        if r_path.len() <= 1 {
            assert(r_visited == Seq::new(1, |_i| entry));
            assert(visited == Seq::new(1, |_i| entry));
        } else {
            match entry {
                NodeEntry::Node(node) => {
                    assert(r_visited == Seq::new(1, |_i| entry).add(node.visit(r_remain)));
                    assert(visited == Seq::new(1, |_i| entry).add(node.visit(remain)));
                    // Prove `r_remain` is the real path of `remain`
                    assert(node.real_path(remain).0 == path.0.skip(1).take(visited.len() - 1));
                    assert(r_remain.0 == path.0.skip(1).take(visited.len() - 1));
                    assert(r_remain == node.real_path(remain));
                    // Recursively prove `node.visit(remain)`
                    node.lemma_real_path_visits_same_entry(remain);
                },
                _ => {
                    assert(r_visited == Seq::new(1, |_i| entry));
                    assert(visited == Seq::new(1, |_i| entry));
                },
            }
        }
    }

    /* `path_mappings` related lemmas */
    /// Lemma. All `(path, frame)` mappings have valid size and alignment.
    pub proof fn lemma_path_mappings_valid(self)
        requires
            self.wf(),
            self.level == 0,
        ensures
            forall|path, frame| #[trigger]
                self.path_mappings().contains_pair(path, frame) ==> {
                    &&& frame.size == self.constants.arch.frame_size((path.len() - 1) as nat)
                    &&& path.to_vaddr(self.constants.arch).aligned(frame.size.as_nat())
                    &&& frame.base.aligned(frame.size.as_nat())
                    &&& frame.base.0 >= self.constants.pmem_lb.0
                    &&& frame.base.0 + frame.size.as_nat() <= self.constants.pmem_ub.0
                },
    {
        assert forall|path, frame| #[trigger]
            self.path_mappings().contains_pair(path, frame) implies {
            &&& frame.size == self.constants.arch.frame_size((path.len() - 1) as nat)
            &&& path.to_vaddr(self.constants.arch).aligned(frame.size.as_nat())
            &&& frame.base.aligned(frame.size.as_nat())
            &&& frame.base.0 >= self.constants.pmem_lb.0
            &&& frame.base.0 + frame.size.as_nat() <= self.constants.pmem_ub.0
        } by {
            // Prove the reached frame satisfy the wf
            self.lemma_visited_entries_satisfy_wf(path);
            assert(PTTreeNode::is_entry_valid(
                NodeEntry::Frame(frame),
                (path.len() - 1) as nat,
                self.constants,
            ));
            assert(self.constants.arch.is_valid_frame_size(frame.size));

            // Prove alignment
            assert(frame.base.aligned(frame.size.as_nat()));
            assert(frame.base.0 >= self.constants.pmem_lb.0);
            assert(frame.base.0 + frame.size.as_nat() <= self.constants.pmem_ub.0);
            path.lemma_to_vaddr_frame_alignment(self.constants.arch);
        }
    }

    /// Lemma. Path mappings can not have 2 keys `a` and `b` such that `a` is prefix of `b`.
    pub proof fn lemma_path_mappings_nonprefix(self)
        requires
            self.wf(),
        ensures
            forall|path1, path2|
                self.path_mappings().contains_key(path1) && self.path_mappings().contains_key(path2)
                    ==> path1 == path2 || !path1.has_prefix(path2),
    {
        assert forall|path1, path2|
            self.path_mappings().contains_key(path1) && self.path_mappings().contains_key(
                path2,
            ) implies path1 == path2 || !path1.has_prefix(path2) by {
            if path1 != path2 {
                if path1.has_prefix(path2) {
                    // Proof by contradiction
                    let visited1 = self.visit(path1);
                    let visited2 = self.visit(path2);
                    assert(visited1.len() == path1.len());
                    assert(visited2.len() == path2.len());
                    // Prove `path2.len() - 1` and `path1.len() - 1` are different
                    if path1.len() == path2.len() {
                        path1.lemma_prefix_eq_full(path2);
                    }
                    assert(path2.len() < path1.len());
                    self.lemma_visit_preserves_prefix(path1, path2);
                    assert(visited1[path2.len() - 1] == visited2.last());
                    assert(visited2.last() is Frame);
                    assert(visited1.last() is Frame);
                    // `visited1` cannot have 2 frames (lemma), contradiction
                    self.lemma_visited_entry_is_node_except_final(path1);
                }
            }
        }
    }

    /// Lemma. All `(path, frame)` mappings do not overlap in virtual memory.
    pub proof fn lemma_path_mappings_nonoverlap_in_vmem(self)
        requires
            self.wf(),
            self.level == 0,
        ensures
            forall|path1, path2, frame1, frame2|
                self.path_mappings().contains_pair(path1, frame1)
                    && self.path_mappings().contains_pair(path2, frame2) ==> path1 == path2
                    || !SpecVAddr::overlap(
                    path1.to_vaddr(self.constants.arch),
                    frame1.size.as_nat(),
                    path2.to_vaddr(self.constants.arch),
                    frame2.size.as_nat(),
                ),
    {
        assert forall|path1, path2, frame1, frame2|
            self.path_mappings().contains_pair(path1, frame1) && self.path_mappings().contains_pair(
                path2,
                frame2,
            ) implies path1 == path2 || !SpecVAddr::overlap(
            path1.to_vaddr(self.constants.arch),
            frame1.size.as_nat(),
            path2.to_vaddr(self.constants.arch),
            frame2.size.as_nat(),
        ) by {
            if path1 != path2 {
                self.lemma_path_mappings_nonprefix();
                assert(!path1.has_prefix(path2));
                assert(!path2.has_prefix(path1));
                PTTreePath::lemma_first_diff_idx_exists(path1, path2);
                let first_diff_idx = PTTreePath::first_diff_idx(path1, path2);
                assert(path1.0[first_diff_idx] != path2.0[first_diff_idx]);

                self.lemma_path_mappings_valid();
                if path1.0[first_diff_idx] < path2.0[first_diff_idx] {
                    PTTreePath::lemma_path_order_implies_vaddr_order(
                        self.constants.arch,
                        path1,
                        path2,
                    );
                    assert(path1.to_vaddr(self.constants.arch).0 + frame1.size.as_nat()
                        <= path2.to_vaddr(self.constants.arch).0);
                } else {
                    PTTreePath::lemma_path_order_implies_vaddr_order(
                        self.constants.arch,
                        path2,
                        path1,
                    );
                    assert(path2.to_vaddr(self.constants.arch).0 + frame2.size.as_nat()
                        <= path1.to_vaddr(self.constants.arch).0);
                }
            }
        }
    }

    /// Lemma. `path_mappings` has at most one path `path` such that `path.to_vaddr() == vbase`.
    pub proof fn lemma_path_mappings_has_at_most_one_path_for_vbase(self, vbase: SpecVAddr)
        requires
            self.wf(),
            self.level == 0,
        ensures
            forall|path1: PTTreePath, path2: PTTreePath|
                #![auto]
                {
                    &&& self.path_mappings().contains_key(path1)
                    &&& self.path_mappings().contains_key(path2)
                    &&& path1.to_vaddr(self.constants.arch) == vbase
                    &&& path2.to_vaddr(self.constants.arch) == vbase
                } ==> path1 == path2,
    {
        assert forall|path1: PTTreePath, path2: PTTreePath|
            #![auto]
            {
                &&& self.path_mappings().contains_key(path1)
                &&& self.path_mappings().contains_key(path2)
                &&& path1.to_vaddr(self.constants.arch) == vbase
                &&& path2.to_vaddr(self.constants.arch) == vbase
            } implies path1 == path2 by {
            if path1 != path2 {
                // Proof by contradiction
                self.lemma_path_mappings_nonprefix();
                PTTreePath::lemma_nonprefix_implies_vaddr_inequality(
                    self.constants.arch,
                    path1,
                    path2,
                );
                assert(path1.to_vaddr(self.constants.arch) != path2.to_vaddr(self.constants.arch));
            }
        }
    }

    /// Lemma. `self.fully_populated()` implies `!self.path_mappings().empty()`.
    pub proof fn lemma_fully_populated_implies_path_mappings_nonempty(self)
        requires
            self.wf(),
            self.fully_populated(),
            self.level > 0,
        ensures
            exists|path: PTTreePath| self.path_mappings().contains_key(path),
        decreases self.constants.arch.level_count() - self.level,
    {
        if self.level >= self.constants.arch.level_count() - 1 {
            let idx: int = choose|i| 0 <= i < self.entries.len() && self.entries[i] is Frame;
            let path = PTTreePath(Seq::new(1, |_i| idx as nat));
            // `self.visit(path)` reachs a `Frame` entry
            assert(self.path_mappings().contains_key(path));
        } else {
            let idx: int = choose|i|
                0 <= i < self.entries.len() && (self.entries[i] is Frame
                    || self.entries[i] is Node);
            let entry = self.entries[idx];
            assert(self.entries.contains(entry));
            if let NodeEntry::Node(node) = entry {
                node.lemma_fully_populated_implies_path_mappings_nonempty();
                let remain = choose|subpath| node.path_mappings().contains_key(subpath);
                // Construct path from subpath
                let path = PTTreePath(Seq::new(1, |_i| idx as nat).add(remain.0));
                assert(path.0.skip(1) == remain.0);
                assert(self.path_mappings().contains_key(path));
            } else {
                let path = PTTreePath(Seq::new(1, |_i| idx as nat));
                // `self.visit(path)` reachs a `Frame` entry
                assert(self.path_mappings().contains_key(path));
            }
        }
    }

    /* insert related lemmas */
    /// Lemma. `insert` preserves wf.
    pub proof fn lemma_insert_preserves_wf(self, path: PTTreePath, frame: SpecFrame)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
            Self::is_entry_valid(
                NodeEntry::Frame(frame),
                (self.level + path.len() - 1) as nat,
                self.constants,
            ),
        ensures
            self.insert(path, frame).0.wf(),
        decreases path.len(),
    {
        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        assert(self.entries.contains(entry));
        if path.len() <= 1 {
            // Base case, proved by lemma
            self.lemma_update_preserves_wf(idx, NodeEntry::Frame(frame));
        } else {
            match entry {
                NodeEntry::Node(node) => {
                    assert(Self::is_entry_valid(entry, self.level, self.constants));
                    assert(node.wf());
                    // Recursively prove `node.insert(remain, frame)`
                    node.lemma_insert_preserves_wf(remain, frame);
                    // `node.update(remain, frame)` satisfies wf,
                    // so the updated `self` also satisfy wf by lemma
                    self.lemma_update_preserves_wf(
                        idx,
                        NodeEntry::Node(node.insert(remain, frame).0),
                    );
                },
                NodeEntry::Empty => {
                    let new = PTTreeNode::new(self.constants, self.level + 1);
                    // `new` satisfies wf by construction
                    assert(new.wf());
                    // Recursively prove `new.insert(remain, frame)`
                    new.lemma_insert_preserves_wf(remain, frame);
                    // `new.insert(remain, frame)` satisfies wf,
                    // so the updated `self` also satisfy wf by lemma
                    self.lemma_update_preserves_wf(
                        idx,
                        NodeEntry::Node(new.insert(remain, frame).0),
                    );
                },
                _ => (),
            }
        }
    }

    /// Lemma. `path_mappings` after `insert` contains the new mapping.
    pub proof fn lemma_path_mappings_after_insertion_contains_new_mapping(
        self,
        path: PTTreePath,
        frame: SpecFrame,
    )
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
            self.insert(path, frame).1 is Ok,
        ensures
            self.insert(path, frame).0.path_mappings().contains_pair(path, frame),
        decreases path.len(),
    {
        let new = self.insert(path, frame);
        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        assert(self.entries.contains(entry));
        if path.len() <= 1 {
            match entry {
                NodeEntry::Empty => assert(new.0.visit(path) == Seq::new(
                    1,
                    |_i| NodeEntry::Frame(frame),
                )),
                _ => (),  // unreachable
            }
        } else {
            match entry {
                NodeEntry::Node(node) => {
                    assert(Self::is_entry_valid(entry, self.level, self.constants));
                    assert(node.wf());
                    // Recursively prove `node.insert(remain, frame)`
                    node.lemma_path_mappings_after_insertion_contains_new_mapping(remain, frame);
                },
                NodeEntry::Empty => {
                    let node = PTTreeNode::new(self.constants, self.level + 1);
                    // `node` satisfies wf by construction
                    assert(node.wf());
                    // Recursively prove `node.insert(remain, frame)`
                    node.lemma_path_mappings_after_insertion_contains_new_mapping(remain, frame);
                },
                _ => (),  // unreachable
            }
        }
    }

    /// Lemma. `path_mappings` after `insert` is a superset of `path_mappings` before.
    pub proof fn lemma_path_mappings_after_insertion_is_superset(
        self,
        path: PTTreePath,
        frame: SpecFrame,
    )
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
        ensures
            forall|path2: PTTreePath, frame2: SpecFrame| #[trigger]
                self.path_mappings().contains_pair(path2, frame2) ==> self.insert(
                    path,
                    frame,
                ).0.path_mappings().contains_pair(path2, frame2),
        decreases path.len(),
    {
        let new = self.insert(path, frame).0;
        assert forall|path2: PTTreePath, frame2: SpecFrame| #[trigger]
            self.path_mappings().contains_pair(
                path2,
                frame2,
            ) implies new.path_mappings().contains_pair(path2, frame2) by {
            let (idx, remain) = path.step();
            let (idx2, remain2) = path2.step();
            let entry = self.entries[idx as int];
            assert(self.entries.contains(entry));
            // Postcondition satisfied obviously if `path.len() == 1`
            if path.len() > 1 {
                if idx == idx2 {
                    // `path` and `path2` share same step
                    match entry {
                        NodeEntry::Node(node) => {
                            assert(node.path_mappings().contains_pair(remain2, frame2));
                            // Recursively prove `node.insert(remain, frame)`
                            node.lemma_path_mappings_after_insertion_is_superset(remain, frame);
                            assert(node.insert(remain, frame).0.path_mappings().contains_pair(
                                remain2,
                                frame2,
                            ));
                        },
                        _ => assert(new == self),
                    }
                } else {
                    // `path` and `path2` do not share any prefix
                    match entry {
                        NodeEntry::Node(node) => assert(new == self.update(
                            idx,
                            NodeEntry::Node(node.insert(remain, frame).0),
                        )),
                        NodeEntry::Empty => assert(new == self.update(
                            idx,
                            NodeEntry::Node(
                                Self::new(self.constants, self.level + 1).insert(remain, frame).0,
                            ),
                        )),
                        _ => assert(new == self),
                    }
                    // `self.entries` only updates at `idx`
                    assert(self.entries[idx2 as int] == new.entries[idx2 as int]);
                }
            }
        }
    }

    // Lemma. `insert` does not affect other mappings.
    pub proof fn lemma_insert_not_affect_other_mappings(self, path: PTTreePath, frame: SpecFrame)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
            Self::is_entry_valid(
                NodeEntry::Frame(frame),
                (self.level + path.len() - 1) as nat,
                self.constants,
            ),
            self.insert(path, frame).1 is Ok,
        ensures
            forall|path2: PTTreePath, frame2: SpecFrame| #[trigger]
                self.insert(path, frame).0.path_mappings().contains_pair(path2, frame2) ==> path2
                    == path || self.path_mappings().contains_pair(path2, frame2),
        decreases path.len(),
    {
        let new = self.insert(path, frame).0;
        self.lemma_insert_preserves_wf(path, frame);

        assert forall|path2: PTTreePath, frame2: SpecFrame| #[trigger]
            new.path_mappings().contains_pair(path2, frame2) implies path2 == path
            || self.path_mappings().contains_pair(path2, frame2) by {
            let (idx, remain) = path.step();
            let (idx2, remain2) = path2.step();

            let entry = self.entries[idx as int];
            assert(self.entries.contains(entry));
            let new_entry = new.entries[idx as int];
            assert(new.entries.contains(new_entry));
            let entry2 = self.entries[idx2 as int];
            assert(self.entries.contains(entry2));
            let new_entry2 = new.entries[idx2 as int];
            assert(new.entries.contains(new_entry2));

            if path.len() <= 1 {
                // Base case, `new_entry` is the inserted frame while other entries unchanged
                assert(new_entry == NodeEntry::Frame(frame));
                if idx == idx2 {
                    assert(path2.0 == path.0);
                } else {
                    // `path2` points to an unchanged entry
                    assert(self.path_mappings().contains_pair(path2, frame2));
                }
            } else {
                if idx == idx2 {
                    // `path` and `path2` share same step
                    match (entry, new_entry) {
                        (NodeEntry::Node(node), NodeEntry::Node(new_node)) => {
                            // `node` becomes `new_node` after `insert`
                            assert(new_node == node.insert(remain, frame).0);
                            assert(new_node.path_mappings().contains_pair(remain2, frame2));
                            // Recursive prove that `new_node` has one more mapping than `node`
                            node.lemma_insert_not_affect_other_mappings(remain, frame);
                            assert(remain == remain2 || node.path_mappings().contains_pair(
                                remain2,
                                frame2,
                            ));
                            if remain == remain2 {
                                path.lemma_eq_step(path2);
                            } else {
                                assert(self.path_mappings().contains_pair(path2, frame2));
                            }
                        },
                        (NodeEntry::Empty, NodeEntry::Node(new_node)) => {
                            let node = Self::new(self.constants, self.level + 1);
                            // `node` becomes `new_node` after `insert`
                            assert(new_node == node.insert(remain, frame).0);
                            assert(new_node.path_mappings().contains_pair(remain2, frame2));
                            // Recursive prove that `new_node` has one more mapping than `node`
                            node.lemma_insert_not_affect_other_mappings(remain, frame);
                            assert(remain == remain2 || node.path_mappings().contains_pair(
                                remain2,
                                frame2,
                            ));
                            if remain == remain2 {
                                path.lemma_eq_step(path2);
                            } else {
                                assert(self.path_mappings().contains_pair(path2, frame2));
                            }
                        },
                        (_, NodeEntry::Frame(_)) | (_, NodeEntry::Empty) => {
                            // `new.path_mappings()` must contain `(path, frame)`, so `new_entry`
                            // cannot be frame or empty at this level
                            self.lemma_path_mappings_after_insertion_contains_new_mapping(
                                path,
                                frame,
                            );
                            assert(false);  // unreachable
                        },
                        _ => assert(false),  // unreachable
                    }
                } else {
                    // `path` and `path2` do not share any prefix
                    match entry {
                        NodeEntry::Node(node) => assert(new == self.update(
                            idx,
                            NodeEntry::Node(node.insert(remain, frame).0),
                        )),
                        NodeEntry::Empty => assert(new == self.update(
                            idx,
                            NodeEntry::Node(
                                Self::new(self.constants, self.level + 1).insert(remain, frame).0,
                            ),
                        )),
                        _ => (),  // unreachable
                    }
                    // `self.entries` only updates at `idx`
                    assert(entry2 == new_entry2);
                    assert(self.path_mappings().contains_pair(path2, frame2));
                }
            }
        }
    }

    /// Lemma. `insert` adds a mapping to `path_mappings`.
    pub proof fn lemma_insert_adds_path_mapping(self, path: PTTreePath, frame: SpecFrame)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
            Self::is_entry_valid(
                NodeEntry::Frame(frame),
                (self.level + path.len() - 1) as nat,
                self.constants,
            ),
            self.insert(path, frame).1 is Ok,
        ensures
            self.insert(path, frame).0.path_mappings() == self.path_mappings().insert(path, frame),
    {
        let new = self.insert(path, frame).0;
        // `new.path_mappings()` contains the new mapping `(path, frame)`
        self.lemma_path_mappings_after_insertion_contains_new_mapping(path, frame);
        // `new.path_mappings()` is a superset of `self.path_mappings()`
        self.lemma_path_mappings_after_insertion_is_superset(path, frame);
        // Other mappings are preserved
        self.lemma_insert_not_affect_other_mappings(path, frame);

        // `new.path_mappings()` is a subset of `self.path_mappings().insert(path, frame)`
        assert forall|path2: PTTreePath, frame2: SpecFrame| #[trigger]
            new.path_mappings().contains_pair(path2, frame2) implies self.path_mappings().insert(
            path,
            frame,
        ).contains_pair(path2, frame2) by {
            if path2 == path {
                assert(frame2 == frame);
            }
        }
        // `self.path_mappings().insert(path, frame)` is a subset of `new.path_mappings()`
        assert forall|path2: PTTreePath, frame2: SpecFrame| #[trigger]
            self.path_mappings().insert(path, frame).contains_pair(
                path2,
                frame2,
            ) implies new.path_mappings().contains_pair(path2, frame2) by {
            if path2 == path {
                assert(new.path_mappings().contains_pair(path, frame));
            } else {
                assert(self.path_mappings().contains_pair(path2, frame2));
            }
        }
        lemma_map_eq_pair(self.path_mappings().insert(path, frame), new.path_mappings());
    }

    /// Lemma. `insert` fails for `path` implies `self.path_mappings()` contains `path2`
    /// such that `path2` is a prefix of `path` or `path` is a prefix of `path2`.
    pub proof fn lemma_insert_fails_implies_prefix(self, path: PTTreePath, frame: SpecFrame)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
            self.insert(path, frame).1 is Err,
            self.fully_populated(),
        ensures
            exists|path2: PTTreePath| #[trigger]
                self.path_mappings().contains_key(path2) && (path2.has_prefix(path)
                    || path.has_prefix(path2)),
        decreases path.len(),
    {
        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        assert(self.entries.contains(entry));
        if path.len() <= 1 {
            match entry {
                NodeEntry::Frame(_) => {
                    assert(self.path_mappings().contains_key(path));
                },
                NodeEntry::Node(node) => {
                    node.lemma_fully_populated_implies_path_mappings_nonempty();
                    let remain2 = choose|path: PTTreePath| node.path_mappings().contains_key(path);
                    let path2 = PTTreePath(Seq::new(1, |_i| idx).add(remain2.0));
                    assert(path2.0.skip(1) == remain2.0);
                    assert(self.path_mappings().contains_key(path2));
                    assert(path2.has_prefix(path));
                },
                _ => assert(false),
            }
        } else {
            match entry {
                NodeEntry::Frame(_) => {
                    let path2 = PTTreePath(Seq::new(1, |_i| idx));
                    assert(self.path_mappings().contains_key(path2));
                    assert(path.has_prefix(path2));
                },
                NodeEntry::Node(node) => {
                    node.lemma_insert_fails_implies_prefix(remain, frame);
                    let remain2 = choose|subpath2: PTTreePath| #[trigger]
                        node.path_mappings().contains_key(subpath2) && (subpath2.has_prefix(remain)
                            || remain.has_prefix(subpath2));
                    let path2 = PTTreePath(Seq::new(1, |_i| idx).add(remain2.0));
                    assert(path2.0.skip(1) == remain2.0);
                    assert(self.path_mappings().contains_key(path2));
                    if remain2.has_prefix(remain) {
                        path2.lemma_prefix_step(path);
                    } else {
                        path.lemma_prefix_step(path2);
                    }
                },
                NodeEntry::Empty => self.lemma_empty_entry_implies_insert_ok(path, frame),
            }
        }
    }

    /// Lemma. If an empty entry is reached during `insert`, the result must be `Ok`.
    pub proof fn lemma_empty_entry_implies_insert_ok(self, path: PTTreePath, frame: SpecFrame)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
            self.entries[path.0[0] as int] is Empty,
        ensures
            self.insert(path, frame).1 is Ok,
        decreases path.len(),
    {
        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        assert(self.entries.contains(entry));
        if path.len() > 1 {
            let node = PTTreeNode::new(self.constants, self.level + 1);
            node.lemma_empty_entry_implies_insert_ok(remain, frame);
        }
    }

    /// Lemma. `insert` always succeeds if `self` is empty.
    pub proof fn lemma_empty_implies_insert_ok(self, path: PTTreePath, frame: SpecFrame)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
            self.empty(),
        ensures
            self.insert(path, frame).1 is Ok,
    {
        let (idx, _) = path.step();
        let entry = self.entries[idx as int];
        assert(self.entries.contains(entry));
        assert(entry is Empty);
        self.lemma_empty_entry_implies_insert_ok(path, frame);
    }

    /// Lemma. If `self.insert(path, frame)` succeeds, then `self.visit(path)` reaches an empty entry.
    pub proof fn lemma_insert_ok_implies_visit_reaches_empty(self, path: PTTreePath, frame: SpecFrame)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
            self.insert(path, frame).1 is Ok,
        ensures
            self.visit(path).last() is Empty,
        decreases path.len(),
    {
        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        assert(self.entries.contains(entry));
        if path.len() > 1 {
            match entry {
                NodeEntry::Node(node) => {
                    node.lemma_insert_ok_implies_visit_reaches_empty(remain, frame);
                },
                _ => (),
            }
        }
    }

    /// Lemma. `insert` preserves `fully_populated` property.
    pub proof fn lemma_insert_preserves_fully_populated(self, path: PTTreePath, frame: SpecFrame)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
            self.insert(path, frame).1 is Ok,
            self.fully_populated() || self.empty(),
        ensures
            self.insert(path, frame).0.fully_populated(),
        decreases path.len(),
    {
        let new = self.insert(path, frame).0;

        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        assert(self.entries.contains(entry));
        if path.len() <= 1 {
            match entry {
                NodeEntry::Empty => {
                    // New entry ensures node is fully_populated
                    assert(new.entries.contains(new.entries[idx as int]));
                    assert forall|entry|
                        #![auto]
                        new.entries.contains(entry)
                            && entry is Node implies entry->Node_0.fully_populated() by {
                        assert(self.entries.contains(entry));
                    }
                    assert(new.fully_populated());
                },
                _ => (),
            }
        } else {
            match entry {
                NodeEntry::Node(node) => {
                    // Subnode is fully_populated after insertion
                    node.lemma_insert_preserves_fully_populated(remain, frame);
                    assert(new.entries.contains(new.entries[idx as int]));
                    assert forall|entry|
                        #![auto]
                        new.entries.contains(entry)
                            && entry is Node implies entry->Node_0.fully_populated() by {
                        if entry != new.entries[idx as int] {
                            assert(self.entries.contains(entry));
                        }
                    }
                    assert(new.fully_populated());
                },
                NodeEntry::Empty => {
                    let node = PTTreeNode::new(self.constants, self.level + 1);
                    // Subnode is fully populated after insertion
                    node.lemma_insert_preserves_fully_populated(remain, frame);
                    assert(new.entries.contains(new.entries[idx as int]));
                    assert forall|entry|
                        #![auto]
                        new.entries.contains(entry)
                            && entry is Node implies entry->Node_0.fully_populated() by {
                        if entry != new.entries[idx as int] {
                            assert(self.entries.contains(entry));
                        }
                    }
                    assert(new.fully_populated());
                },
                _ => (),
            }
        }
    }

    /* remove related lemmas */
    /// Lemma. `remove` preserves wf.
    pub proof fn lemma_remove_preserves_wf(self, path: PTTreePath)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
        ensures
            self.remove(path).0.wf(),
        decreases path.len(),
    {
        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        assert(self.entries.contains(entry));
        if path.len() <= 1 {
            // Base case, proved by lemma
            self.lemma_update_preserves_wf(idx, NodeEntry::Empty);
        } else {
            match entry {
                NodeEntry::Node(node) => {
                    assert(Self::is_entry_valid(entry, self.level, self.constants));
                    assert(node.wf());
                    // Recursively prove `node.remove(remain)`
                    node.lemma_remove_preserves_wf(remain);
                    // `node.remove(remain)` satisfies wf,
                    // so the updated `self` also satisfy wf by lemma
                    self.lemma_update_preserves_wf(idx, NodeEntry::Node(node.remove(remain).0));
                },
                NodeEntry::Frame(_) => {
                    if remain.is_zero() {
                        self.lemma_update_preserves_wf(idx, NodeEntry::Empty);
                    }
                },
                _ => (),
            }
        }
    }

    /// Lemma. `path_mappings` after removal does not contain the removed mapping.
    pub proof fn lemma_path_mappings_after_removal_not_contain_mapping(self, path: PTTreePath)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
            self.remove(path).1 is Ok,
        ensures
            !self.remove(path).0.path_mappings().contains_key(self.real_path(path)),
        decreases path.len(),
    {
        let new = self.remove(path).0;
        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        assert(self.entries.contains(entry));
        if path.len() <= 1 {
            match entry {
                NodeEntry::Frame(_) => assert(new.visit(path) == Seq::new(
                    1,
                    |_i| NodeEntry::Empty,
                )),
                _ => (),
            }
        } else {
            match entry {
                NodeEntry::Node(node) => {
                    assert(Self::is_entry_valid(entry, self.level, self.constants));
                    assert(node.wf());
                    // Recursively prove `node.remove(remain)`
                    node.lemma_path_mappings_after_removal_not_contain_mapping(remain);
                    self.lemma_real_path_step(path);
                },
                _ => (),
            }
        }
    }

    /// Lemma. `path_mappings` after `remove` is subset of before.
    pub proof fn lemma_path_mappings_after_removal_is_subset(self, path: PTTreePath)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
            self.remove(path).1 is Ok,
        ensures
            forall|path2: PTTreePath, frame2: SpecFrame| #[trigger]
                self.remove(path).0.path_mappings().contains_pair(path2, frame2)
                    ==> self.path_mappings().contains_pair(path2, frame2),
        decreases path.len(),
    {
        let new = self.remove(path).0;
        assert forall|path2: PTTreePath, frame2: SpecFrame| #[trigger]
            new.path_mappings().contains_pair(
                path2,
                frame2,
            ) implies self.path_mappings().contains_pair(path2, frame2) by {
            let (idx, remain) = path.step();
            let (idx2, remain2) = path2.step();
            let entry = self.entries[idx as int];
            assert(self.entries.contains(entry));
            // Postcondition satisfied obviously if `path.len() == 1`
            if path.len() > 1 {
                if idx == idx2 {
                    // `path` and `path2` share same step
                    match entry {
                        NodeEntry::Node(node) => {
                            assert(node.remove(remain).0.path_mappings().contains_pair(
                                remain2,
                                frame2,
                            ));
                            // Recursively prove `node.remove(remain)`
                            node.lemma_path_mappings_after_removal_is_subset(remain);
                            assert(node.path_mappings().contains_pair(remain2, frame2));
                        },
                        _ => (),
                    }
                } else {
                    // `path` and `path2` do not share any prefix
                    match entry {
                        NodeEntry::Node(node) => assert(new == self.update(
                            idx,
                            NodeEntry::Node(node.remove(remain).0),
                        )),
                        _ => (),
                    }
                    // `self.entries` only updates at `idx`
                    assert(self.entries[idx2 as int] == new.entries[idx2 as int]);
                }
            }
        }
    }

    /// Lemma. `remove` does not affect other mappings.
    pub proof fn lemma_remove_not_affect_other_mappings(self, path: PTTreePath)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
            self.remove(path).1 is Ok,
        ensures
            forall|path2: PTTreePath, frame2: SpecFrame| #[trigger]
                self.path_mappings().contains_pair(path2, frame2) ==> path2 == self.real_path(path)
                    || self.remove(path).0.path_mappings().contains_pair(path2, frame2),
        decreases path.len(),
    {
        let new = self.remove(path).0;
        self.lemma_remove_preserves_wf(path);

        assert forall|path2: PTTreePath, frame2: SpecFrame| #[trigger]
            self.path_mappings().contains_pair(path2, frame2) implies path2 == self.real_path(path)
            || new.path_mappings().contains_pair(path2, frame2) by {
            let (idx, remain) = path.step();
            let (idx2, remain2) = path2.step();

            let entry = self.entries[idx as int];
            assert(self.entries.contains(entry));
            let new_entry = new.entries[idx as int];
            assert(new.entries.contains(new_entry));
            let entry2 = self.entries[idx2 as int];
            assert(self.entries.contains(entry2));
            let new_entry2 = new.entries[idx2 as int];
            assert(new.entries.contains(new_entry2));

            if path.len() <= 1 {
                if idx == idx2 {
                    match entry {
                        NodeEntry::Frame(_) => {
                            assert(path2.0 == path.0.take(1));
                        },
                        _ => assert(new == self),
                    }
                } else {
                    // `path2` points to an unchanged entry
                    assert(new.path_mappings().contains_pair(path2, frame2));
                }
            } else {
                if idx == idx2 {
                    // `path` and `path2` share same step
                    match (entry, new_entry) {
                        (NodeEntry::Node(node), NodeEntry::Node(new_node)) => {
                            // `node` becomes `new_node` after `remove`
                            assert(new_node == node.remove(remain).0);
                            assert(node.path_mappings().contains_pair(remain2, frame2));
                            // Recursive prove that `new_node` has one less mapping than `node`
                            node.lemma_remove_not_affect_other_mappings(remain);
                            assert(remain2 == node.real_path(remain)
                                || new_node.path_mappings().contains_pair(remain2, frame2));
                            if remain2 == node.real_path(remain) {
                                self.lemma_real_path_step(path);
                                self.lemma_real_path_is_prefix(path);
                                path.lemma_prefix_step(self.real_path(path));
                            } else {
                                assert(new.path_mappings().contains_pair(path2, frame2));
                            }
                        },
                        (NodeEntry::Node(node), NodeEntry::Frame(_))
                        | (NodeEntry::Node(node), NodeEntry::Empty) => {
                            assert(new_entry == NodeEntry::Node(node.remove(remain).0));
                            assert(false);  // unreachable
                        },
                        (NodeEntry::Frame(_), _) => {
                            if remain.0 == seq![0nat; remain.len()] {
                                assert(path2.0 == path.0.take(1));
                            }
                        },
                        _ => (),
                    }
                } else {
                    // `path` and `path2` do not share any prefix
                    match entry {
                        NodeEntry::Node(node) => assert(new == self.update(
                            idx,
                            NodeEntry::Node(node.remove(remain).0),
                        )),
                        _ => (),
                    }
                    // `self.entries` only updates at `idx`
                    assert(entry2 == new_entry2);
                    assert(new.path_mappings().contains_pair(path2, frame2));
                }
            }
        }
    }

    /// Lemma. `remove` removes a mapping from `path_mappings`.
    pub proof fn lemma_remove_removes_path_mapping(self, path: PTTreePath)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
            self.remove(path).1 is Ok,
        ensures
            self.remove(path).0.path_mappings() == self.path_mappings().remove(
                self.real_path(path),
            ),
    {
        let new = self.remove(path).0;
        self.lemma_remove_preserves_wf(path);
        let real_path = self.real_path(path);

        // `new.path_mappings()` does not contain the mapping `(path, frame)`
        self.lemma_path_mappings_after_removal_not_contain_mapping(path);
        // `new.path_mappings()` is a subset of `self.path_mappings()`
        self.lemma_path_mappings_after_removal_is_subset(path);
        // Other mappings are preserved
        self.lemma_remove_not_affect_other_mappings(path);

        // `new.path_mappings()` is a subset of `self.path_mappings().remove(path)`
        assert forall|path2: PTTreePath, frame2: SpecFrame| #[trigger]
            new.path_mappings().contains_pair(path2, frame2) implies self.path_mappings().remove(
            real_path,
        ).contains_pair(path2, frame2) by {
            assert(path2 != real_path);
        }
        // `self.path_mappings().remove(path)` is a subset of `new.path_mappings()`
        assert forall|path2: PTTreePath, frame2: SpecFrame| #[trigger]
            self.path_mappings().remove(real_path).contains_pair(
                path2,
                frame2,
            ) implies new.path_mappings().contains_pair(path2, frame2) by {
            assert(path2 != real_path);
            assert(self.path_mappings().contains_pair(path2, frame2));
        }
        lemma_map_eq_pair(self.path_mappings().remove(real_path), new.path_mappings());
    }

    /// Lemma. If `path2` is contained in `self.path_mappings()`, and `path2` is a real prefix
    /// of `path`, then `self.remove(path)` succeeds.
    pub proof fn lemma_remove_real_prefix_ok(self, path: PTTreePath, path2: PTTreePath)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
            self.path_mappings().contains_key(path2),
            path.has_real_prefix(path2),
        ensures
            self.remove(path).1 is Ok,
        decreases path2.len(),
    {
        let (idx, remain) = path.step();
        let (idx2, remain2) = path2.step();
        assert(idx == idx2);
        let entry = self.entries[idx as int];
        assert(self.entries.contains(entry));
        if path2.len() > 1 {
            assert(entry is Node);
            entry->Node_0.lemma_remove_real_prefix_ok(remain, remain2);
        }
    }

    /// Lemma. If `self.remove(path)` succeeds, then `self.visit(path)` reaches a frame.
    pub proof fn lemma_remove_ok_implies_visit_reaches_frame(self, path: PTTreePath)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
            self.remove(path).1 is Ok,
        ensures
            self.visit(path).last() is Frame,
            path.has_zero_tail(self.visit(path).len()),
        decreases path.len(),
    {
        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        assert(self.entries.contains(entry));
        if path.len() > 1 {
            match entry {
                NodeEntry::Node(node) => {
                    node.lemma_remove_ok_implies_visit_reaches_frame(remain);
                    assert forall|i| self.visit(path).len() <= i < path.len() implies path.0[i]
                        == 0 by {
                        assert(path.0[i] == remain.0[i - 1]);
                    }
                },
                NodeEntry::Frame(_) => {
                    assert forall|i| self.visit(path).len() <= i < path.len() implies path.0[i]
                        == 0 by {
                        assert(path.0[i] == remain.0[i - 1]);
                    }
                },
                NodeEntry::Empty => (),
            }
        }
    }

    /// Lemma. `remove` always fails if `self` is empty.
    pub proof fn lemma_empty_implies_remove_fail(self, path: PTTreePath)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
            self.empty(),
        ensures
            self.remove(path).1 is Err,
    {
        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        assert(self.entries.contains(entry));
        assert(entry is Empty);
    }

    /* prune related lemmas */
    /// Lemma. `prune` preserves wf.
    pub proof fn lemma_prune_preserves_wf(self, path: PTTreePath)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
        ensures
            self.prune(path).wf(),
        decreases path.len(),
    {
        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        assert(self.entries.contains(entry));
        if path.len() > 1 && entry is Node {
            let node = entry->Node_0;
            let new_node = node.prune(remain);
            if new_node.empty() {
                self.lemma_update_preserves_wf(idx, NodeEntry::Empty);
            } else {
                node.lemma_prune_preserves_wf(remain);
                self.lemma_update_preserves_wf(idx, NodeEntry::Node(new_node));
            }
        }
    }

    /// Lemma. `prune` does not introduce new frame paths.
    pub proof fn lemma_prune_not_add_frame_path(self, path: PTTreePath, path2: PTTreePath)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
            self.prune(path).is_frame_path(path2),
        ensures
            self.is_frame_path(path2),
            self.prune(path).visit(path2).last() == self.visit(path2).last(),
        decreases path.len(),
    {
        let new = self.prune(path);
        self.lemma_prune_preserves_wf(path);

        let (idx, remain) = path.step();
        let (idx2, remain2) = path2.step();
        let entry = self.entries[idx as int];
        assert(self.entries.contains(entry));

        if path.len() > 1 {
            if entry is Node {
                let new_node = entry->Node_0.prune(remain);
                // Only entry at `idx` is updated, and the updated entry(`idx`)
                // must be empty or a node.
                if new_node.empty() {
                    assert(new == self.update(idx, NodeEntry::Empty));
                } else {
                    assert(new == self.update(idx, NodeEntry::Node(new_node)));
                }
            }
            if idx == idx2 {
                if path2.len() > 1 {
                    // `entry` is a node or frame.
                    match entry {
                        NodeEntry::Node(node) => {
                            let new_node = node.prune(remain);
                            node.lemma_prune_not_add_frame_path(remain, remain2);
                        },
                        NodeEntry::Frame(_) => {
                            assert(new == self);
                        },
                        _ => assert(false),
                    }
                } else {
                    // `path2` is a frame path, so `entry` must be a frame.
                    assert(entry is Frame);
                }
            } else {
                // Entry at `idx2` is not updated.
                assert(new.entries[idx2 as int] == self.entries[idx2 as int]);
            }
        }
    }

    /// Lemma. `prune` does not remove existing frame paths.
    pub proof fn lemma_prune_not_remove_frame_path(self, path: PTTreePath, path2: PTTreePath)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
            self.is_frame_path(path2),
        ensures
            self.prune(path).is_frame_path(path2),
            self.prune(path).visit(path2).last() == self.visit(path2).last(),
        decreases path.len(),
    {
        let new = self.prune(path);

        let (idx, remain) = path.step();
        let (idx2, remain2) = path2.step();
        let entry = self.entries[idx as int];
        assert(self.entries.contains(entry));

        if path.len() > 1 {
            if entry is Node {
                let new_node = entry->Node_0.prune(remain);
                // Only entry at `idx` is updated, and the updated entry(`idx`)
                // must be empty or a node.
                if new_node.empty() {
                    assert(new == self.update(idx, NodeEntry::Empty));
                } else {
                    assert(new == self.update(idx, NodeEntry::Node(new_node)));
                }
            }
            if idx == idx2 {
                if path2.len() > 1 {
                    // `entry` is a node or frame.
                    match entry {
                        NodeEntry::Node(node) => {
                            let new_node = node.prune(remain);
                            node.lemma_prune_preserves_wf(remain);
                            node.lemma_prune_not_remove_frame_path(remain, remain2);

                            let entry2 = new_node.entries[remain2.step().0 as int];
                            assert(new_node.entries.contains(entry2));
                            assert(!(entry2 is Empty));
                            assert(!new_node.empty());
                            // `new_node` is not empty, so it is not eliminated.
                            assert(new == self.update(idx, NodeEntry::Node(new_node)));
                        },
                        NodeEntry::Frame(_) => {
                            assert(new == self);
                        },
                        _ => assert(false),
                    }
                } else {
                    // `path2` is a frame path, so `entry` must be a frame.
                    assert(entry is Frame);
                }
            } else {
                // Entry at `idx2` is not updated.
                assert(new.entries[idx2 as int] == self.entries[idx2 as int]);
            }
        }
    }

    /// Lemma. `prune` does not affect path mappings.
    pub proof fn lemma_prune_not_affect_path_mappings(self, path: PTTreePath)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
        ensures
            self.path_mappings() == self.prune(path).path_mappings(),
    {
        let new = self.prune(path);
        assert forall|path2, frame2|
            self.path_mappings().contains_pair(
                path2,
                frame2,
            ) implies new.path_mappings().contains_pair(path2, frame2) by {
            self.lemma_prune_not_remove_frame_path(path, path2);
        }
        assert forall|path2, frame2|
            new.path_mappings().contains_pair(
                path2,
                frame2,
            ) implies self.path_mappings().contains_pair(path2, frame2) by {
            self.lemma_prune_not_add_frame_path(path, path2);
        }
        lemma_map_eq_pair(self.path_mappings(), new.path_mappings());
    }

    /// Lemma. `prune` after `remove` will eliminate empty nodes
    pub proof fn lemma_prune_after_remove_preserves_fully_populated(self, path: PTTreePath)
        requires
            self.wf(),
            path.valid(self.constants.arch, self.level),
            self.remove(path).1 is Ok,
            self.fully_populated(),
        ensures
            ({
                let new = self.remove(path).0.prune(path);
                new.fully_populated() || new.empty()
            }),
        decreases path.len(),
    {
        let new = self.remove(path).0.prune(path);

        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        assert(self.entries.contains(entry));
        if path.len() <= 1 {
            match entry {
                NodeEntry::Frame(_) => {
                    if !new.empty() {
                        // Another entry exists in the node
                        let idx2 = choose|idx2|
                            0 <= idx2 < self.entries.len() && idx2 != idx && (
                            self.entries[idx2] is Node || self.entries[idx2] is Frame);
                        assert(self.entries.contains(self.entries[idx2]));
                        assert(self.entries[idx2] == new.entries[idx2]);
                        assert(new.entries.contains(self.entries[idx2]));
                        assert forall|entry|
                            #![auto]
                            new.entries.contains(entry)
                                && entry is Node implies entry->Node_0.fully_populated() by {
                            assert(self.entries.contains(entry));
                        }
                        assert(new.fully_populated());
                    }
                },
                _ => (),
            }
        } else {
            match entry {
                NodeEntry::Node(node) => {
                    let new_node = node.remove(remain).0.prune(remain);
                    // Recursively prove that the new node is fully populated or an empty node
                    node.lemma_prune_after_remove_preserves_fully_populated(remain);
                    if new_node.empty() {
                        // Empty subnode is eliminated by `prune`
                        if !new.empty() {
                            assert forall|entry|
                                #![auto]
                                new.entries.contains(entry)
                                    && entry is Node implies entry->Node_0.fully_populated() by {
                                assert(self.entries.contains(entry));
                            }
                            assert(new.fully_populated());
                        }
                    } else {
                        assert(new_node.fully_populated());
                        assert(new.entries.contains(new.entries[idx as int]));
                        assert forall|entry|
                            #![auto]
                            new.entries.contains(entry)
                                && entry is Node implies entry->Node_0.fully_populated() by {
                            if entry != new.entries[idx as int] {
                                assert(self.entries.contains(entry));
                            }
                        }
                        assert(new.fully_populated());
                    }
                },
                NodeEntry::Frame(_) => {
                    if !new.empty() {
                        assert forall|entry|
                            #![auto]
                            new.entries.contains(entry)
                                && entry is Node implies entry->Node_0.fully_populated() by {
                            assert(self.entries.contains(entry));
                        }
                        assert(new.fully_populated());
                    }
                },
                _ => (),
            }
        }
    }
}

/// Page table tree model.
pub struct PTTreeModel {
    /// The root node.
    pub root: PTTreeNode,
}

impl PTTreeModel {
    /// Wrap a root node into a tree model.
    pub open spec fn new(root: PTTreeNode) -> Self {
        Self { root }
    }

    /// Create an empty page table tree.
    pub open spec fn empty(config: SpecPTConstants) -> Self {
        Self::new(PTTreeNode::new(config, 0))
    }

    /// wf. The tree structure and node configurations are valid.
    /// The tree is fully populated or empty.
    pub open spec fn wf(self) -> bool {
        &&& self.root.level == 0
        &&& self.root.wf()
        &&& self.root.fully_populated() || self.root.empty()
    }

    /// Get page table architecture.
    pub open spec fn arch(self) -> SpecPTArch {
        self.root.constants.arch
    }

    /// Get physical memory lower bound.
    pub open spec fn pmem_lb(self) -> SpecPAddr {
        self.root.constants.pmem_lb
    }

    /// Get physical memory upper bound.
    pub open spec fn pmem_ub(self) -> SpecPAddr {
        self.root.constants.pmem_ub
    }

    /// Interpret the tree as `(vbase, frame)` mappings.
    pub open spec fn mappings(self) -> Map<SpecVAddr, SpecFrame> {
        Map::new(
            |vbase: SpecVAddr|
                exists|path| #[trigger]
                    self.root.path_mappings().contains_key(path) && path.to_vaddr(self.arch())
                        == vbase,
            |vbase: SpecVAddr|
                {
                    let path = choose|path| #[trigger]
                        self.root.path_mappings().contains_key(path) && path.to_vaddr(self.arch())
                            == vbase;
                    self.root.path_mappings().index(path)
                },
        )
    }

    /// If there exists a mapping for `vaddr`.
    pub open spec fn has_mapping_for(self, vaddr: SpecVAddr) -> bool {
        exists|vbase: SpecVAddr, frame: SpecFrame|
            {
                &&& #[trigger] self.mappings().contains_pair(vbase, frame)
                &&& vaddr.within(vbase, frame.size.as_nat())
            }
    }

    /// Get the mapping for `vaddr`.
    pub open spec fn mapping_for(self, vaddr: SpecVAddr) -> (SpecVAddr, SpecFrame)
        recommends
            self.has_mapping_for(vaddr),
    {
        choose|vbase: SpecVAddr, frame: SpecFrame|
            {
                &&& #[trigger] self.mappings().contains_pair(vbase, frame)
                &&& vaddr.within(vbase, frame.size.as_nat())
            }
    }

    /// If mapping `(vaddr, frame)` overlaps with existing virtual memory.
    pub open spec fn overlaps_vmem(self, vbase: SpecVAddr, frame: SpecFrame) -> bool {
        exists|vbase2: SpecVAddr|
            {
                &&& #[trigger] self.mappings().contains_key(vbase2)
                &&& SpecVAddr::overlap(
                    vbase2,
                    self.mappings()[vbase2].size.as_nat(),
                    vbase,
                    frame.size.as_nat(),
                )
            }
    }

    /// View the tree as `PageTableState`.
    pub open spec fn view(self) -> PageTableState {
        PageTableState {
            mappings: self.mappings(),
            constants: SpecPTConstants {
                arch: self.arch(),
                pmem_lb: self.pmem_lb(),
                pmem_ub: self.pmem_ub(),
            },
        }
    }

    /// Map a virtual address to a physical frame.
    ///
    /// If mapping succeeds, return `Ok` and the updated tree.
    pub open spec fn map(self, vbase: SpecVAddr, frame: SpecFrame) -> (Self, PagingResult)
        recommends
            self.wf(),
            self.arch().is_valid_frame_size(frame.size),
            vbase.aligned(frame.size.as_nat()),
            frame.base.aligned(frame.size.as_nat()),
            frame.base.0 >= self.pmem_lb().0,
            frame.base.0 + frame.size.as_nat() <= self.pmem_ub().0,
    {
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );
        let (node, res) = self.root.insert(path, frame);
        if res is Ok {
            (Self::new(node), Ok(()))
        } else {
            (self, Err(()))
        }
    }

    /// Unmap a virtual address.
    ///
    /// If unmapping succeeds, return `Ok` and the updated tree.
    pub open spec fn unmap(self, vbase: SpecVAddr) -> (Self, PagingResult)
        recommends
            self.wf(),
    {
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        let (node, res) = self.root.remove(path);
        if res is Ok {
            (Self::new(node.prune(path)), Ok(()))
        } else {
            (self, Err(()))
        }
    }

    /// Query a virtual address, return the mapped physical frame.
    ///
    /// If there is no mapping for the virtual address, return `Err(())`.
    pub open spec fn query(self, vaddr: SpecVAddr) -> PagingResult<(SpecVAddr, SpecFrame)>
        recommends
            self.wf(),
    {
        let path = PTTreePath::from_vaddr_root(
            vaddr,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        let visited = self.root.visit(path);
        match visited.last() {
            NodeEntry::Frame(frame) => Ok(
                (self.arch().vbase(vaddr, (visited.len() - 1) as nat), frame),
            ),
            _ => Err(()),
        }
    }

    /// Lemma. `mappings` is consistent with `root.path_mappings`.
    pub proof fn lemma_mappings_consistent_with_path_mappings(self)
        requires
            self.wf(),
        ensures
            forall|path: PTTreePath, frame: SpecFrame| #[trigger]
                self.root.path_mappings().contains_pair(path, frame)
                    ==> self.mappings().contains_pair(path.to_vaddr(self.arch()), frame),
    {
        assert forall|path: PTTreePath, frame: SpecFrame| #[trigger]
            self.root.path_mappings().contains_pair(
                path,
                frame,
            ) implies self.mappings().contains_pair(path.to_vaddr(self.arch()), frame) by {
            let vbase = path.to_vaddr(self.arch());
            assert(self.mappings().contains_key(vbase));
            self.root.lemma_path_mappings_has_at_most_one_path_for_vbase(vbase);
            assert(path == choose|path| #[trigger]
                self.root.path_mappings().contains_key(path) && path.to_vaddr(self.arch())
                    == vbase);
            assert(self.root.path_mappings().contains_pair(path, frame));
        }
    }

    /// Lemma. All `(vbase, frame)` mappings have valid size and alignment.
    pub proof fn lemma_mappings_valid(self)
        requires
            self.wf(),
        ensures
            forall|vbase, frame| #[trigger]
                self.mappings().contains_pair(vbase, frame) ==> {
                    &&& self.arch().is_valid_frame_size(frame.size)
                    &&& vbase.aligned(frame.size.as_nat())
                    &&& frame.base.aligned(frame.size.as_nat())
                    &&& frame.base.0 >= self.pmem_lb().0
                    &&& frame.base.0 + frame.size.as_nat() <= self.pmem_ub().0
                },
    {
        assert forall|vbase, frame| #[trigger] self.mappings().contains_pair(vbase, frame) implies {
            &&& self.arch().is_valid_frame_size(frame.size)
            &&& vbase.aligned(frame.size.as_nat())
            &&& frame.base.aligned(frame.size.as_nat())
            &&& frame.base.0 >= self.pmem_lb().0
            &&& frame.base.0 + frame.size.as_nat() <= self.pmem_ub().0
        } by {
            let path = choose|path: PTTreePath|
                #![auto]
                {
                    &&& path.valid(self.arch(), 0)
                    &&& self.root.visit(path).len() == path.len()
                    &&& self.root.visit(path).last() == NodeEntry::Frame(frame)
                    &&& path.to_vaddr(self.arch()) == vbase
                };
            assert(self.root.path_mappings().contains_pair(path, frame));
            self.root.lemma_path_mappings_valid();
        }
    }

    /// Lemma. All `(vbase, frame)` mappings do not overlap in virtual memory.
    pub proof fn lemma_mappings_nonoverlap_in_vmem(self)
        requires
            self.wf(),
        ensures
            forall|vbase1, frame1, vbase2, frame2|
                self.mappings().contains_pair(vbase1, frame1) && self.mappings().contains_pair(
                    vbase2,
                    frame2,
                ) ==> vbase1 == vbase2 || !SpecVAddr::overlap(
                    vbase1,
                    frame1.size.as_nat(),
                    vbase2,
                    frame2.size.as_nat(),
                ),
    {
        assert forall|vbase1, frame1, vbase2, frame2|
            self.mappings().contains_pair(vbase1, frame1) && self.mappings().contains_pair(
                vbase2,
                frame2,
            ) implies vbase1 == vbase2 || !SpecVAddr::overlap(
            vbase1,
            frame1.size.as_nat(),
            vbase2,
            frame2.size.as_nat(),
        ) by {
            let (path1, path2) = choose|path1: PTTreePath, path2: PTTreePath|
                #![auto]
                {
                    &&& path1.valid(self.arch(), 0)
                    &&& path2.valid(self.arch(), 0)
                    &&& self.root.visit(path1).len() == path1.len()
                    &&& self.root.visit(path2).len() == path2.len()
                    &&& self.root.visit(path1).last() == NodeEntry::Frame(frame1)
                    &&& self.root.visit(path2).last() == NodeEntry::Frame(frame2)
                    &&& path1.to_vaddr(self.arch()) == vbase1
                    &&& path2.to_vaddr(self.arch()) == vbase2
                };
            assert(self.root.path_mappings().contains_pair(path1, frame1));
            assert(self.root.path_mappings().contains_pair(path2, frame2));
            self.root.lemma_path_mappings_nonoverlap_in_vmem();
        }
    }

    /// Theorem. `map` preserves wf.
    pub proof fn map_preserves_wf(self, vbase: SpecVAddr, frame: SpecFrame)
        requires
            self.wf(),
            self.arch().is_valid_frame_size(frame.size),
            vbase.aligned(frame.size.as_nat()),
            frame.base.aligned(frame.size.as_nat()),
            frame.base.0 >= self.pmem_lb().0,
            frame.base.0 + frame.size.as_nat() <= self.pmem_ub().0,
        ensures
            self.map(vbase, frame).0.wf(),
    {
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );
        self.root.lemma_insert_preserves_wf(path, frame);
        if self.map(vbase, frame).1 is Ok {
            self.root.lemma_insert_preserves_fully_populated(path, frame);
        }
    }

    /// Lemma. `map` succeeds if the address does not overlap with any existing mapped region.
    pub proof fn lemma_nonoverlap_implies_map_ok(self, vbase: SpecVAddr, frame: SpecFrame)
        requires
            self.wf(),
            self.arch().is_valid_frame_size(frame.size),
            vbase.aligned(frame.size.as_nat()),
            frame.base.aligned(frame.size.as_nat()),
            frame.base.0 >= self.pmem_lb().0,
            frame.base.0 + frame.size.as_nat() <= self.pmem_ub().0,
            !self.overlaps_vmem(vbase, frame),
        ensures
            self.map(vbase, frame).1 is Ok,
    {
        let (new, res) = self.map(vbase, frame);
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );

        if self.root.empty() {
            // Tree is empty, insertion succeeds trivially
            self.root.lemma_empty_implies_insert_ok(path, frame);
        } else {
            // Tree is fully populated
            assert(self.root.fully_populated());
            if res is Err {
                // Prove by contradiction
                self.root.lemma_insert_fails_implies_prefix(path, frame);
                let path2 = choose|path2: PTTreePath| #[trigger]
                    self.root.path_mappings().contains_key(path2) && (path2.has_prefix(path)
                        || path.has_prefix(path2));
                let frame2 = self.root.path_mappings()[path2];
                self.root.lemma_path_mappings_valid();

                assert(self.root.path_mappings().contains_pair(path2, frame2));
                self.lemma_mappings_consistent_with_path_mappings();
                assert(self.mappings().contains_pair(path2.to_vaddr(self.arch()), frame2));

                // The prefix relation implies that the two frames overlap
                if path.has_prefix(path2) {
                    PTTreePath::lemma_to_vaddr_lower_bound(self.arch(), path, path2);
                    PTTreePath::lemma_to_vaddr_upper_bound(self.arch(), path, path2);
                    assert(SpecVAddr::overlap(
                        path.to_vaddr(self.arch()),
                        frame.size.as_nat(),
                        path2.to_vaddr(self.arch()),
                        frame2.size.as_nat(),
                    ));
                } else {
                    PTTreePath::lemma_to_vaddr_lower_bound(self.arch(), path2, path);
                    PTTreePath::lemma_to_vaddr_upper_bound(self.arch(), path2, path);
                    assert(SpecVAddr::overlap(
                        path2.to_vaddr(self.arch()),
                        frame2.size.as_nat(),
                        path.to_vaddr(self.arch()),
                        frame.size.as_nat(),
                    ));
                }
            }
        }
    }

    /// Lemma. The address does not overlap with any existing mapped region if `map` succeeds.
    pub proof fn lemma_map_ok_implies_nonoverlap(self, vbase: SpecVAddr, frame: SpecFrame)
        requires
            self.wf(),
            self.arch().is_valid_frame_size(frame.size),
            vbase.aligned(frame.size.as_nat()),
            frame.base.aligned(frame.size.as_nat()),
            frame.base.0 >= self.pmem_lb().0,
            frame.base.0 + frame.size.as_nat() <= self.pmem_ub().0,
            self.map(vbase, frame).1 is Ok,
        ensures
            !self.overlaps_vmem(vbase, frame),
    {
        let (new, res) = self.map(vbase, frame);
        self.map_preserves_wf(vbase, frame);

        self.lemma_map_adds_mapping(vbase, frame);
        assert(new.mappings() == self.mappings().insert(vbase, frame));

        // The newly added mapping is not in the original mappings
        self.lemma_map_ok_implies_vbase_nonexist(vbase, frame);
        assert(!self.mappings().contains_key(vbase));

        // `self` and `new` both have non-overlapping mappings
        new.lemma_mappings_nonoverlap_in_vmem();
        self.lemma_mappings_nonoverlap_in_vmem();
        // So the newly added mapping cannot overlap with any existing mapping
        assert(forall|vbase2, frame2| #[trigger]
            self.mappings().contains_pair(vbase2, frame2) ==> !SpecVAddr::overlap(
                vbase2,
                frame2.size.as_nat(),
                vbase,
                frame.size.as_nat(),
            ));
        assert(!self.overlaps_vmem(vbase, frame));
    }

    /// Lemma. A successful `map` operation adds the `(vbase, frame)` pair to mappings.
    pub proof fn lemma_map_adds_mapping(self, vbase: SpecVAddr, frame: SpecFrame)
        requires
            self.wf(),
            self.arch().is_valid_frame_size(frame.size),
            vbase.aligned(frame.size.as_nat()),
            frame.base.aligned(frame.size.as_nat()),
            frame.base.0 >= self.pmem_lb().0,
            frame.base.0 + frame.size.as_nat() <= self.pmem_ub().0,
            self.map(vbase, frame).1 is Ok,
        ensures
            self.map(vbase, frame).0.mappings() === self.mappings().insert(vbase, frame),
    {
        let new = self.map(vbase, frame).0;
        self.map_preserves_wf(vbase, frame);

        // `path` is the path to the entry containing the mapping.
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );
        assert(path.to_vaddr(self.arch()) == vbase);

        // `path_mappings` is updated according to lemma.
        self.root.lemma_insert_adds_path_mapping(path, frame);

        // `new.mappings()` is a subset of `self.mappings().insert(vbase, frame)`.
        assert forall|vbase2, frame2| #[trigger]
            new.mappings().contains_pair(vbase2, frame2) implies self.mappings().insert(
            vbase,
            frame,
        ).contains_pair(vbase2, frame2) by {
            if vbase2 != vbase {
                let path2 = choose|path2: PTTreePath| #[trigger]
                    new.root.path_mappings().contains_key(path2) && vbase2 == path2.to_vaddr(
                        self.arch(),
                    ) && new.root.path_mappings().index(path2) == frame2;
                assert(new.root.path_mappings().contains_pair(path2, frame2));
                // `lemma_insert_adds_path_mapping` ensures this.
                assert(self.root.path_mappings().insert(path, frame).contains_pair(path2, frame2));
                assert(path2 != path);
                assert(self.root.path_mappings().contains_pair(path2, frame2));
                // `self.mappings()` contains the mapping consistently.
                self.lemma_mappings_consistent_with_path_mappings();
                assert(self.mappings().contains_pair(vbase2, frame2));
                assert(self.mappings().insert(vbase, frame).contains_pair(vbase2, frame2));
            } else {
                new.root.lemma_path_mappings_has_at_most_one_path_for_vbase(vbase);
                // Only exists one path for `vbase` in path mappings, so `frame2 == frame`
                assert(frame2 == frame);
            }
        }
        // `self.mappings().insert(vbase, frame)` is a subset of `new.mappings()`.
        assert forall|vbase2, frame2| #[trigger]
            self.mappings().insert(vbase, frame).contains_pair(
                vbase2,
                frame2,
            ) implies new.mappings().contains_pair(vbase2, frame2) by {
            if vbase2 != vbase {
                assert(self.mappings().contains_pair(vbase2, frame2));
                let path2 = choose|path2: PTTreePath| #[trigger]
                    self.root.path_mappings().contains_key(path2) && vbase2 == path2.to_vaddr(
                        self.arch(),
                    ) && self.root.path_mappings().index(path2) == frame2;
                assert(self.root.path_mappings().contains_pair(path2, frame2));
                // `new.root.path_mappings()` is a superset of `self.root.path_mappings()`.
                assert(new.root.path_mappings().contains_pair(path2, frame2));
                // `new.mappings()` contains the mapping consistently.
                new.lemma_mappings_consistent_with_path_mappings();
                assert(new.mappings().contains_pair(vbase2, frame2));
            } else {
                assert(frame2 == frame);
                // `lemma_insert_adds_path_mapping` ensures this.
                assert(new.root.path_mappings().contains_pair(path, frame));
                // `new.mappings()` contains the mapping consistently.
                new.lemma_mappings_consistent_with_path_mappings();
                assert(new.mappings().contains_pair(vbase2, frame2));
            }
        }
        lemma_map_eq_pair(new.mappings(), self.mappings().insert(vbase, frame));
    }

    /// Lemma. `map` succeeds implies `vbase` not in `mappings()`.
    pub proof fn lemma_map_ok_implies_vbase_nonexist(self, vbase: SpecVAddr, frame: SpecFrame)
        requires
            self.wf(),
            self.arch().is_valid_frame_size(frame.size),
            vbase.aligned(frame.size.as_nat()),
            frame.base.aligned(frame.size.as_nat()),
            frame.base.0 >= self.pmem_lb().0,
            frame.base.0 + frame.size.as_nat() <= self.pmem_ub().0,
            self.map(vbase, frame).1 is Ok,
        ensures
            !self.mappings().contains_key(vbase),
    {
        let new = self.map(vbase, frame).0;
        self.map_preserves_wf(vbase, frame);

        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );
        self.root.lemma_insert_ok_implies_visit_reaches_empty(path, frame);

        if self.mappings().contains_key(vbase) {
            let path2 = choose|path: PTTreePath| #[trigger]
                self.root.path_mappings().contains_key(path) && path.to_vaddr(self.arch()) == vbase;
            PTTreePath::lemma_vaddr_eq_implies_real_prefix(self.arch(), path, path2);
            assert(self.root.visit(path2).last() is Frame);

            // The prefix relation leads to a contradiction of the lasted visited entry.
            if path.has_prefix(path2) {
                self.root.lemma_visited_entry_is_node_except_final(path);
                self.root.lemma_visit_preserves_prefix(path, path2);
                assert(false);
            } else {
                self.root.lemma_visited_entry_is_node_except_final(path2);
                self.root.lemma_visit_preserves_prefix(path2, path);
                assert(false);
            }
        }
    }

    /// Theorem. `unmap` preserves wf.
    pub proof fn unmap_preserves_wf(self, vbase: SpecVAddr)
        requires
            self.wf(),
            self.unmap(vbase).1 is Ok,
        ensures
            self.unmap(vbase).0.wf(),
    {
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        self.root.lemma_remove_preserves_wf(path);
        self.root.remove(path).0.lemma_prune_preserves_wf(path);

        if self.root.empty() {
            self.root.lemma_empty_implies_remove_fail(path);
        }
        assert(self.root.fully_populated());
        self.root.lemma_prune_after_remove_preserves_fully_populated(path);
    }

    /// Lemma. `unmap` succeeds implies `vbase` in `mappings()`.
    pub proof fn lemma_unmap_ok_implies_vbase_exist(self, vbase: SpecVAddr)
        requires
            self.wf(),
            self@.unmap_pre(vbase),
            self.unmap(vbase).1 is Ok,
        ensures
            self.mappings().contains_key(vbase),
    {
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        let real_path = self.root.real_path(path);

        // Prove `real_path` is a real prefix of `path`.
        self.root.lemma_remove_ok_implies_visit_reaches_frame(path);
        self.root.lemma_visit_length_bounds(path);
        self.root.lemma_real_path_valid(path);
        self.root.lemma_real_path_visits_same_entry(path);
        assert(self.root.path_mappings().contains_key(real_path));
        assert(path.has_real_prefix(real_path));

        PTTreePath::lemma_real_prefix_implies_vaddr_eq(self.arch(), path, real_path);
        assert(real_path.to_vaddr(self.arch()) == vbase);
        assert(self.mappings().contains_key(vbase));
    }

    /// Lemma. `vbase` in `mappings()` implies `unmap` succeeds.
    pub proof fn lemma_vbase_exist_implies_unmap_ok(self, vbase: SpecVAddr)
        requires
            self.wf(),
            self@.unmap_pre(vbase),
            self.mappings().contains_key(vbase),
        ensures
            self.unmap(vbase).1 is Ok,
    {
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        let path2 = choose|path: PTTreePath| #[trigger]
            self.root.path_mappings().contains_key(path) && path.to_vaddr(self.arch()) == vbase;

        PTTreePath::lemma_to_vaddr_inverts_from_vaddr(self.arch(), vbase, path);
        PTTreePath::lemma_vaddr_eq_implies_real_prefix(self.arch(), path, path2);
        assert(path.has_real_prefix(path2));
        self.root.lemma_remove_real_prefix_ok(path, path2);
    }

    /// Lemma. A successful `unmap` operation removes the `(vbase, frame)` pair from mappings.
    pub proof fn lemma_unmap_removes_mapping(self, vbase: SpecVAddr)
        requires
            self.wf(),
            self@.unmap_pre(vbase),
            self.unmap(vbase).1 is Ok,
        ensures
            self.unmap(vbase).0.mappings() === self.mappings().remove(vbase),
    {
        let new = self.unmap(vbase).0;
        self.unmap_preserves_wf(vbase);

        // `path` is the path to the entry containing the mapping.
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        let real_path = self.root.real_path(path);

        self.root.lemma_remove_ok_implies_visit_reaches_frame(path);
        self.root.lemma_visit_length_bounds(path);
        self.root.lemma_real_path_valid(path);
        self.root.lemma_real_path_visits_same_entry(path);
        assert(self.root.path_mappings().contains_key(real_path));
        assert(path.has_real_prefix(real_path));

        // `path_mappings` is updated according to lemma.
        self.root.lemma_remove_removes_path_mapping(path);
        self.root.lemma_remove_preserves_wf(path);
        self.root.remove(path).0.lemma_prune_not_affect_path_mappings(path);

        // `new.mappings()` is a subset of `self.mappings().remove(vbase)`.
        assert forall|vbase2, frame2| #[trigger]
            new.mappings().contains_pair(vbase2, frame2) implies self.mappings().remove(
            vbase,
        ).contains_pair(vbase2, frame2) by {
            let path2 = choose|path2: PTTreePath| #[trigger]
                new.root.path_mappings().contains_key(path2) && vbase2 == path2.to_vaddr(
                    self.arch(),
                ) && new.root.path_mappings().index(path2) == frame2;
            assert(new.root.path_mappings().contains_pair(path2, frame2));
            // `lemma_remove_removes_path_mapping` ensures this.
            assert(self.root.path_mappings().remove(real_path).contains_pair(path2, frame2));
            assert(self.root.path_mappings().contains_pair(path2, frame2));

            // `self.mappings()` contains the mapping consistently.
            self.lemma_mappings_consistent_with_path_mappings();
            assert(self.mappings().contains_pair(vbase2, frame2));

            // Use prefix lemmas to show `vbase != vbase2`
            self.root.lemma_path_mappings_nonprefix();
            PTTreePath::lemma_nonprefix_implies_vaddr_inequality(self.arch(), path2, real_path);
            assert(path.to_vaddr(self.arch()) != vbase2);
            assert(self.mappings().remove(vbase).contains_pair(vbase2, frame2));
        }
        // `self.mappings().remove(vbase)` is a subset of `new.mappings()`.
        assert forall|vbase2, frame2| #[trigger]
            self.mappings().remove(vbase).contains_pair(
                vbase2,
                frame2,
            ) implies new.mappings().contains_pair(vbase2, frame2) by {
            assert(vbase2 != vbase);
            assert(self.mappings().contains_pair(vbase2, frame2));
            let path2 = choose|path2: PTTreePath| #[trigger]
                self.root.path_mappings().contains_key(path2) && vbase2 == path2.to_vaddr(
                    self.arch(),
                ) && self.root.path_mappings().index(path2) == frame2;
            assert(self.root.path_mappings().contains_pair(path2, frame2));
            // `new.root.path_mappings()` is a subset of `self.root.path_mappings()`.
            assert(new.root.path_mappings().contains_pair(path2, frame2));
            // `new.mappings()` contains the mapping consistently.
            new.lemma_mappings_consistent_with_path_mappings();
            assert(new.mappings().contains_pair(vbase2, frame2));
        }
        lemma_map_eq_pair(new.mappings(), self.mappings().remove(vbase));
    }

    /// Lemma. `query` succeeds if the address is within a mapped region.
    pub proof fn lemma_mapping_exist_implies_query_ok(self, vaddr: SpecVAddr)
        requires
            self.wf(),
            self.has_mapping_for(vaddr),
        ensures
            self.query(vaddr) is Ok,
            self.query(vaddr).unwrap() == self.mapping_for(vaddr),
    {
        let (vbase, frame) = self.mapping_for(vaddr);
        let path = choose|path: PTTreePath| #[trigger]
            self.root.path_mappings().contains_key(path) && path.to_vaddr(self.arch()) == vbase;
        assert(self.root.path_mappings().contains_pair(path, frame));

        // `path2` is the path used to find the mapping.
        let path2 = PTTreePath::from_vaddr_root(
            vaddr,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        self.root.lemma_path_mappings_valid();
        assert(vbase.0 <= vaddr.0 < vbase.0 + frame.size.as_nat());
        // Substitute address with path
        assert(path2.to_vaddr(self.arch()).0 <= vaddr.0 < path2.to_vaddr(self.arch()).0
            + self.arch().leaf_frame_size().as_nat());

        if !path2.has_prefix(path) {
            // Leads to a contradiction
            let diff_idx = PTTreePath::first_diff_idx(path, path2);
            if path.0[diff_idx] < path2.0[diff_idx] {
                PTTreePath::lemma_path_order_implies_vaddr_order(self.arch(), path, path2);
                assert(path.to_vaddr(self.arch()).0 + frame.size.as_nat() <= path2.to_vaddr(
                    self.arch(),
                ).0);
            } else {
                PTTreePath::lemma_path_order_implies_vaddr_order(self.arch(), path2, path);
                assert(path2.to_vaddr(self.arch()).0 + self.arch().leaf_frame_size().as_nat()
                    <= path.to_vaddr(self.arch()).0);
            }
            assert(false);
        }
        assert(path2.has_prefix(path));

        // Show that `path` is the real path of `path2`.
        self.root.lemma_visit_preserves_prefix(path2, path);
        self.root.lemma_visited_entry_is_node_except_final(path);
        self.root.lemma_visited_entry_is_node_except_final(path2);
        assert(self.root.visit(path) == self.root.visit(path2));
        path2.lemma_trim_prefix(path);
        assert(path2.trim(path.len()) == path);
        assert(self.root.real_path(path2) == path);

        let visited = self.root.visit(path2);
        let level = (visited.len() - 1) as nat;
        assert(level == path.len() - 1);
        assert(visited.last() == NodeEntry::Frame(frame));

        // TODO: add lemma to `PTTreePath`
        PTTreePath::lemma_vaddr_range_from_path(self.arch(), vaddr, path2);
        assert(path2.to_vaddr(self.arch()).0 <= vaddr.0 < path2.to_vaddr(self.arch()).0
            + self.arch().frame_size((path2.len() - 1) as nat).as_nat());
        PTTreePath::lemma_to_vaddr_lower_bound(self.arch(), path2, path);
        PTTreePath::lemma_to_vaddr_upper_bound(self.arch(), path2, path);
        assert(path.to_vaddr(self.arch()).0 <= vaddr.0 < path.to_vaddr(self.arch()).0
            + self.arch().frame_size((path.len() - 1) as nat).as_nat());
        let fsize = self.arch().frame_size(level).as_nat();
        assert(vbase.0 <= vaddr.0 < vbase.0 + fsize);

        let vbase2 = self.arch().vbase(vaddr, level);
        self.arch().lemma_vbase_range_and_alignment(vaddr, level);
        assert(vbase2.0 <= vaddr.0 < vbase2.0 + fsize);

        assert(vbase.aligned(fsize));
        assert(vbase2.aligned(fsize));
        lemma_aligned_range_eq(vbase.0, vbase2.0, vaddr.0, fsize);
        assert(vbase2 == vbase);
    }

    /// Lemma. The address is within a mapped region if `query` succeeds.
    pub proof fn lemma_query_ok_implies_mapping_exist(self, vaddr: SpecVAddr)
        requires
            self.wf(),
            self.query(vaddr) is Ok,
        ensures
            self.has_mapping_for(vaddr),
    {
        let path = PTTreePath::from_vaddr_root(
            vaddr,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        let visited = self.root.visit(path);
        // `query` succeeds implies `visited.last()` is a frame
        assert(visited.last() is Frame);
        let frame = visited.last()->Frame_0;

        // Path mapping for `vaddr`
        let real_path = self.root.real_path(path);
        self.root.lemma_visit_length_bounds(path);
        self.root.lemma_real_path_visits_same_entry(path);
        assert(self.root.path_mappings().contains_pair(real_path, frame));

        // Mapping for `vaddr`
        let vbase = real_path.to_vaddr(self.arch());
        self.lemma_mappings_consistent_with_path_mappings();
        assert(self.mappings().contains_pair(vbase, frame));

        // TODO: add lemma to `PTTreePath`
        assume(vaddr.within(vbase, frame.size.as_nat()));

        // Prove there is only one mapped region that contains `vaddr`
        assert forall|vbase2, frame2| #[trigger]
            self.mappings().contains_pair(vbase2, frame2) && vaddr.within(
                vbase2,
                frame2.size.as_nat(),
            ) implies vbase2 == vbase by {
            // Prove by contradiction
            assert(SpecVAddr::overlap(vbase, frame.size.as_nat(), vbase2, frame2.size.as_nat()));
            self.lemma_mappings_nonoverlap_in_vmem();
        }
    }

    /// Theorem. `map` refines `PageTableState::map`.
    pub proof fn map_refinement(self, vbase: SpecVAddr, frame: SpecFrame)
        requires
            self.wf(),
            self@.map_pre(vbase, frame),
        ensures
            ({
                let (new, res) = self.map(vbase, frame);
                PageTableState::map(self@, new@, vbase, frame, res)
            }),
    {
        let (new, res) = self.map(vbase, frame);
        if !self.overlaps_vmem(vbase, frame) {
            self.lemma_nonoverlap_implies_map_ok(vbase, frame);
            self.lemma_map_adds_mapping(vbase, frame);
        } else {
            if res is Ok {
                // Prove by contradiction
                self.lemma_map_ok_implies_nonoverlap(vbase, frame);
            }
        }
    }

    /// Theorem. `unmap` refines `PageTableState::unmap`.
    pub proof fn unmap_refinement(self, vbase: SpecVAddr)
        requires
            self.wf(),
            self@.unmap_pre(vbase),
        ensures
            ({
                let (new, res) = self.unmap(vbase);
                PageTableState::unmap(self@, new@, vbase, res)
            }),
    {
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        if self.mappings().contains_key(vbase) {
            self.lemma_vbase_exist_implies_unmap_ok(vbase);
            self.lemma_unmap_removes_mapping(vbase);
        } else {
            if self.unmap(vbase).1 is Ok {
                // Prove by contradiction
                self.lemma_unmap_ok_implies_vbase_exist(vbase);
            }
        }
    }

    /// Theorem. `query` refines `PageTableState::query`.
    pub proof fn query_refinement(self, vaddr: SpecVAddr)
        requires
            self.wf(),
            self@.query_pre(vaddr),
        ensures
            self@.query(vaddr, self.query(vaddr)),
    {
        assert(self.mappings() == self@.mappings);  // I don't know why this is necessary

        let res = self.query(vaddr);
        if self.has_mapping_for(vaddr) {
            self.lemma_mapping_exist_implies_query_ok(vaddr);
        } else {
            if res is Ok {
                // Prove by contradiction
                self.lemma_query_ok_implies_mapping_exist(vaddr);
            }
        }
    }
}

/// Lemma. The equality of two maps. Two maps are equal if
/// - they have the same keys
/// - they have the same values for the same keys
pub proof fn lemma_map_eq_key_value<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    requires
        forall|k| m1.contains_key(k) ==> m2.contains_key(k),
        forall|k| m2.contains_key(k) ==> m1.contains_key(k),
        forall|k| #[trigger] m1.contains_key(k) ==> m1[k] === m2[k],
    ensures
        m1 === m2,
{
    assert(m1 === m2)
}

/// Lemma. The equality of two maps. Two maps are equal if they have the same (key, value) pairs.
pub proof fn lemma_map_eq_pair<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    requires
        forall|k, v| m1.contains_pair(k, v) ==> m2.contains_pair(k, v),
        forall|k, v| m2.contains_pair(k, v) ==> m1.contains_pair(k, v),
    ensures
        m1 === m2,
{
    assert forall|k| m1.contains_key(k) implies m2.contains_key(k) by {
        assert(m2.contains_pair(k, m1[k]));
    };
    assert forall|k| m2.contains_key(k) implies m1.contains_key(k) by {
        assert(m1.contains_pair(k, m2[k]));
    };
    assert forall|k| #[trigger] m1.contains_key(k) implies m1[k] === m2[k] by {
        let v = m1.index(k);
        assert(m1.contains_pair(k, v));
        assert(m2.contains_pair(k, v));
    }
    assert(m1 === m2) by {
        lemma_map_eq_key_value(m1, m2);
    }
}

/// Lemma. If two ranges are aligned, then their start and end are equal.
pub proof fn lemma_aligned_range_eq(a: nat, b: nat, m: nat, align: nat)
    by (nonlinear_arith)
    requires
        a <= m < a + align,
        b <= m < b + align,
        align > 0,
        a % align == b % align,
    ensures
        a == b,
{
    let x = a / align;
    let y = b / align;
    let z = a % align;
    assert(z < align);
    assert(a == x * align + z);
    assert(b == y * align + z);
    assert(x * align + z <= m < (x + 1) * align + z);
    assert(y * align + z <= m < (y + 1) * align + z);
    assert(x == y);
}

} // verus!
