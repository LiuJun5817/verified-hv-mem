//! Page table architecture specifications.
//!
//! Page table architecture specifies the hierarchical structure of a page table, including the
//! number of query levels, the number of entries at each level, and the frame size associated
//! with a block/page descriptor.
use vstd::prelude::*;

extern crate alloc;

use crate::address::{
    addr::{SpecVAddr, VAddr},
    frame::FrameSize,
};
use alloc::{vec, vec::Vec};

verus! {

/// Page table entry size.
pub spec const PTE_SIZE: nat = 8;

/// Represents a single level in a hierarchical page table structure.
pub struct SpecPTArchLevel {
    /// The number of entries at this level.
    pub entry_count: nat,
    /// Frame size indicated by a block/page descriptor at this level.
    pub frame_size: FrameSize,
}

/// Complete description of a page table architecture, consisting of multiple
/// hierarchical levels from root (lowest level) to leaf (highest level).
pub struct SpecPTArch(pub Seq<SpecPTArchLevel>);

impl SpecPTArch {
    /// The number of hierarchical levels in the page table.
    pub open spec fn level_count(self) -> nat {
        self.0.len()
    }

    /// The number of entries at a specified level.
    pub open spec fn entry_count(self, level: nat) -> nat
        recommends
            level < self.level_count(),
    {
        self.0[level as int].entry_count
    }

    /// The frame size associated with a block/page descriptor at a given level.
    pub open spec fn frame_size(self, level: nat) -> FrameSize
        recommends
            level < self.level_count(),
    {
        self.0[level as int].frame_size
    }

    /// The size of a leaf frame.
    pub open spec fn leaf_frame_size(self) -> FrameSize {
        self.frame_size((self.level_count() - 1) as nat)
    }

    /// The size of a table at a given level.
    pub open spec fn table_size(self, level: nat) -> nat
        recommends
            level < self.level_count(),
    {
        self.entry_count(level) * PTE_SIZE
    }

    /// Check if `size` is a valid frame size.
    pub open spec fn is_valid_frame_size(self, size: FrameSize) -> bool {
        exists|level: nat| level < self.level_count() && self.frame_size(level) == size
    }

    /// Get the corresponding level of a frame size.
    pub open spec fn level_of_frame_size(self, size: FrameSize) -> nat
        recommends
            self.is_valid_frame_size(size),
    {
        choose|level: nat| level < self.level_count() && self.frame_size(level) == size
    }

    /// Calculates the page table entry index for a virtual address at the specified level.
    pub open spec fn pte_index(self, vaddr: SpecVAddr, level: nat) -> nat
        recommends
            self.valid(),
            level < self.level_count(),
    {
        vaddr.0 / self.frame_size(level).as_nat() % self.entry_count(level)
    }

    /// Aligns the virtual address `vaddr` to the base of its page at `level`.
    pub open spec fn vbase(self, vaddr: SpecVAddr, level: nat) -> SpecVAddr
        recommends
            self.valid(),
            level < self.level_count(),
    {
        SpecVAddr(vaddr.0 / self.frame_size(level).as_nat() * self.frame_size(level).as_nat())
    }

    /// Check if the page table architecture is valid.
    pub open spec fn valid(self) -> bool {
        // At least one level.
        &&& self.level_count() > 0
        // Entry count > 1.
        &&& forall|level: nat|
            level < self.level_count() ==> self.entry_count(level)
                > 1
            // frame_size(N) = frame_size(N+1) * entry_count(N+1)
        &&& forall|level: nat|
            1 <= level < self.level_count() ==> self.frame_size((level - 1) as nat).as_nat()
                == self.frame_size(level).as_nat() * self.entry_count(level)
    }

    /// Lemma (helper). a > 0, b > 1 implies a * b > a.
    proof fn lemma_mul_gt_one(a: nat, b: nat)
        by (nonlinear_arith)
        requires
            a > 0,
            b > 1,
        ensures
            a * b > a,
    {
    }

    /// Lemma. Frame size decreases as level increases.
    pub proof fn lemma_frame_size_monotonic(self, l1: nat, l2: nat)
        requires
            self.valid(),
            l1 < l2 < self.level_count(),
        ensures
            self.frame_size(l1).as_nat() > self.frame_size(l2).as_nat(),
        decreases l2 - l1,
    {
        if l2 - l1 == 1 {
            assert(self.frame_size(l2).as_nat() > 0);
            assert(self.entry_count(l2) > 1);
            Self::lemma_mul_gt_one(self.frame_size(l2).as_nat(), self.entry_count(l2));
            assert(self.frame_size(l1).as_nat() > self.frame_size(l2).as_nat());
        } else {
            assert(self.frame_size(l1 + 1).as_nat() > 0);
            assert(self.entry_count(l1 + 1) > 1);
            Self::lemma_mul_gt_one(self.frame_size(l1 + 1).as_nat(), self.entry_count(l1 + 1));
            assert(self.frame_size(l1).as_nat() > self.frame_size(l1 + 1).as_nat());
            // Prove monotonicity for (l1, l1 + 1) and (l1 + 1, l2).
            self.lemma_frame_size_monotonic(l1 + 1, l2);
        }
    }

    /// Lemma. level_of_frame_size(frame_size(level)) == level.
    pub proof fn lemma_frame_size_inversion(self, level: nat)
        requires
            self.valid(),
            level < self.level_count(),
        ensures
            self.level_of_frame_size(self.frame_size(level)) == level,
    {
        let level2 = self.level_of_frame_size(self.frame_size(level));
        if level2 < level {
            self.lemma_frame_size_monotonic(level2, level);
        } else if level2 > level {
            self.lemma_frame_size_monotonic(level, level2);
        }
    }

    /// Lemma. For all `level2 < level`, frame_size(level2) divides frame_size(level).
    pub proof fn lemma_frame_size_aligned(self, level: nat, level2: nat)
        requires
            self.valid(),
            level2 <= level < self.level_count(),
        ensures
            self.frame_size(level2).as_nat() % self.frame_size(level).as_nat() == 0,
        decreases level - level2,
    {
        if level2 < level {
            let size = self.frame_size(level).as_nat();
            let size2 = self.frame_size(level2).as_nat();
            let size3 = self.frame_size(level2 + 1).as_nat();
            assert(size2 == size3 * self.entry_count(level2 + 1));

            self.lemma_frame_size_aligned(level, level2 + 1);
            vstd::arithmetic::div_mod::lemma_mul_mod_noop(
                size3 as int,
                self.entry_count(level2 + 1) as int,
                size as int,
            );
            assert(size2 % size == 0);
        } else {
            assert(self.frame_size(level2).as_nat() == self.frame_size(level).as_nat());
        }
    }

    /// Lemma. `vbase` has fixed range and alignment.
    pub proof fn lemma_vbase_range_and_alignment(self, vaddr: SpecVAddr, level: nat)
        by (nonlinear_arith)
        requires
            self.valid(),
            level < self.level_count(),
        ensures
            self.vbase(vaddr, level).0 <= vaddr.0 < self.vbase(vaddr, level).0 + self.frame_size(
                level,
            ).as_nat(),
            self.vbase(vaddr, level).aligned(self.frame_size(level).as_nat()),
    {
    }
}

/// **EXEC MODE** Represents a single level in a hierarchical page table structure.
pub struct PTArchLevel {
    /// The number of entries at this level.
    pub entry_count: usize,
    /// Frame size indicated by a block/page descriptor at this level.
    pub frame_size: FrameSize,
}

impl PTArchLevel {
    /// View as `PTArchLevel`.
    pub open spec fn view(self) -> SpecPTArchLevel {
        SpecPTArchLevel { entry_count: self.entry_count as nat, frame_size: self.frame_size }
    }
}

impl Clone for PTArchLevel {
    fn clone(&self) -> Self {
        PTArchLevel { entry_count: self.entry_count, frame_size: self.frame_size }
    }
}

/// **EXEC MODE** Complete description of a page table architecture, consisting of
/// multiple hierarchical levels from root (lowest level) to leaf (highest level).
///
/// Provides utilities to compute the page table entry index and the virtual address.
pub struct PTArch(pub Vec<PTArchLevel>);

impl Clone for PTArch {
    fn clone(&self) -> (res: Self)
        ensures
            self@ == res@,
    {
        let res = PTArch(self.0.clone());
        // Assume equivalence of the clone.
        assume(self@ == res@);
        res
    }
}

impl PTArch {
    /// View as `PTArch`.
    pub open spec fn view(self) -> SpecPTArch {
        SpecPTArch(Seq::new(self.0.len() as nat, |i| self.0[i].view()))
    }

    /// The number of hierarchical levels in the page table.
    pub fn level_count(&self) -> (res: usize)
        ensures
            res == self@.level_count(),
    {
        self.0.len()
    }

    /// The frame (page or block) size at the given level.
    pub fn frame_size(&self, level: usize) -> (res: FrameSize)
        requires
            level < self@.level_count(),
        ensures
            res == self@.frame_size(level as nat),
    {
        self.0[level].frame_size
    }

    /// The number of entries at the given level.
    pub fn entry_count(&self, level: usize) -> (res: usize)
        requires
            level < self@.level_count(),
        ensures
            res == self@.entry_count(level as nat),
    {
        self.0[level].entry_count
    }

    /// Computes the page table entry index for `vaddr` at the specified level.
    pub fn pte_index(&self, vaddr: VAddr, level: usize) -> (res: usize)
        requires
            self@.valid(),
            level < self@.level_count(),
        ensures
            res == self@.pte_index(vaddr@, level as nat),
            res < self@.entry_count(level as nat),
    {
        vaddr.0 / self.frame_size(level).as_usize() % self.entry_count(level)
    }

    /// Aligns the virtual address `vaddr` to the base of its page at `level`.
    ///
    /// The default implementation rounds `vaddr` down to the nearest multiple
    /// of the frame size at `level`.
    pub fn vbase(&self, vaddr: VAddr, level: usize) -> (res: VAddr)
        requires
            self@.valid(),
            level < self@.level_count(),
        ensures
            res.0 == self@.vbase(vaddr@, level as nat).0,
    {
        let fsize = self.frame_size(level).as_usize();
        assert(fsize > 0);
        assert(vaddr.0 / fsize * fsize <= vaddr.0) by (nonlinear_arith);
        VAddr(vaddr.0 / fsize * fsize)
    }

    /// Get the corresponding level of a frame size.
    #[verifier::external_body]
    pub fn level_of_frame_size(&self, size: FrameSize) -> (res: usize)
        requires
            self@.is_valid_frame_size(size),
        ensures
            res == self@.level_of_frame_size(size),
    {
        self.0.as_slice().iter().position(|l| l.frame_size.as_usize() == size.as_usize()).unwrap()
    }
}

} // verus!
