//! Visit path of the page table tree model.
use vstd::prelude::*;

use crate::address::addr::VAddr;
use crate::page_table::pt_arch::SpecPTArch;

verus! {

/// Represents a path from a node to an entry in the page table tree.
///
/// The path is represented as a sequence of indices, where each index corresponds to
/// an entry in the page table node at a particular level of the hierarchy.
pub struct PTTreePath(pub Seq<nat>);

impl PTTreePath {
    /// Path length.
    pub open spec fn len(self) -> nat {
        self.0.len()
    }

    /// Pop head and return the remaining path.
    pub open spec fn step(self) -> (nat, Self)
        recommends
            self.len() > 0,
    {
        (self.0[0], Self(self.0.skip(1)))
    }

    /// Trim the path to the given length.
    pub open spec fn trim(self, len: nat) -> Self
        recommends
            len <= self.len(),
    {
        Self(self.0.take(len as int))
    }

    /// Check if path is valid.
    pub open spec fn valid(self, arch: SpecPTArch, start: nat) -> bool
        recommends
            arch.valid(),
    {
        &&& self.len() > 0
        &&& self.len() + start <= arch.level_count()
        &&& forall|i: int| 0 <= i < self.len() ==> self.0[i] < arch.entry_count(i as nat + start)
    }

    /// If `self` has a non-empty prefix `p`.
    pub open spec fn has_prefix(self, p: Self) -> bool {
        &&& 0 < p.len() <= self.len()
        &&& forall|i: int| 0 <= i < p.len() ==> self.0[i] == p.0[i]
    }

    /// If `self` has a zero tail.
    pub open spec fn has_zero_tail(self, idx: nat) -> bool {
        forall|i: int| idx <= i < self.len() ==> self.0[i] == 0
    }

    /// If `self` has a non-empty prefix `p` and the remaining tail is zero.
    pub open spec fn has_real_prefix(self, p: Self) -> bool {
        &&& self.has_prefix(p)
        &&& self.has_zero_tail(p.len())
    }

    /// If `self` is a zero sequence
    pub open spec fn is_zero(self) -> bool {
        forall|i: int| 0 <= i < self.len() ==> self.0[i] == 0
    }

    /// Get the first position at which two paths differ.
    pub open spec fn first_diff_idx(a: Self, b: Self) -> int
        recommends
            a.len() > 0,
            b.len() > 0,
            !a.has_prefix(b),
            !b.has_prefix(a),
    {
        choose|i: int|
            0 <= i < a.len() && i < b.len() && a.0[i] != b.0[i] && forall|j: int|
                0 <= j < i ==> a.0[j] == b.0[j]
    }

    /// Get a `PTTreePath` from a virtual address, used to query the page table from
    /// a given start level.
    pub open spec fn from_vaddr(vaddr: VAddr, arch: SpecPTArch, start: nat, end: nat) -> Self
        recommends
            arch.valid(),
            start <= end < arch.level_count(),
    {
        Self(Seq::new((end - start) as nat + 1, |i: int| arch.pte_index(vaddr, i as nat + start)))
    }

    /// Get a `PTTreePath` from a virtual address, used to query the page table from root.
    pub open spec fn from_vaddr_root(vaddr: VAddr, arch: SpecPTArch, end: nat) -> Self
        recommends
            arch.valid(),
            end < arch.level_count(),
    {
        Self::from_vaddr(vaddr, arch, 0, end)
    }

    /// Calculate the virtual address corresponding to the path from root.
    pub open spec fn to_vaddr(self, arch: SpecPTArch) -> VAddr
        recommends
            arch.valid(),
            self.valid(arch, 0),
    {
        let parts: Seq<nat> = Seq::new(
            self.len(),
            |i: int| self.0[i] * arch.frame_size(i as nat).as_nat(),
        );
        VAddr(parts.fold_left(0, |sum: nat, part| sum + part))
    }

    /// Lemma. Two paths are equal if they have the same first element and the same tail.
    pub broadcast proof fn lemma_eq_step(self, other: Self)
        requires
            self.len() > 0,
            other.len() > 0,
            #[trigger] self.step() == #[trigger] other.step(),
        ensures
            self == other,
    {
        let (idx1, remain1) = self.step();
        let (idx2, remain2) = other.step();
        assert(remain1.len() == self.len() - 1);
        assert forall|i| 0 <= i < self.len() implies self.0[i] == other.0[i] by {
            if i == 0 {
                assert(idx1 == idx2);
            } else {
                assert(remain1.0[i - 1] == remain2.0[i - 1]);
            }
        }
        assert(self.0 == other.0);
    }

    /// Lemma. If a prefix has the same length as the full path, then the two paths are equal.
    pub broadcast proof fn lemma_prefix_eq_full(self, pref: Self)
        requires
            #[trigger] self.has_prefix(pref),
            pref.len() == self.len(),
        ensures
            self == pref,
    {
        assert(self.0 == pref.0);
    }

    /// Lemma. `other` is a prefix of `self` if the first element of `other` is the same as the first
    /// element of `self`, and the tail of `other` is a prefix of the tail of `self`.
    pub broadcast proof fn lemma_prefix_step(self, other: Self)
        requires
            self.len() > 0,
            other.len() > 0,
            self.step().0 == other.step().0,
            #[trigger] self.step().1.has_prefix(other.step().1),
        ensures
            self.has_prefix(other),
    {
        let (idx1, remain1) = self.step();
        let (idx2, remain2) = other.step();
        assert forall|i| 0 <= i < other.len() implies self.0[i] == other.0[i] by {
            if i == 0 {
                assert(idx1 == idx2);
            } else {
                assert(remain1.0[i - 1] == remain2.0[i - 1]);
            }
        }
    }

    /// Lemma. If `pref` is a prefix of `self`, then `self.trim(pref.len())` is equal to `pref`.
    pub broadcast proof fn lemma_trim_prefix(self, pref: Self)
        requires
            #[trigger] self.has_prefix(pref),
        ensures
            self.trim(pref.len()) == pref,
    {
        let trimmed = self.trim(pref.len());
        // assert(trimmed.len() == pref.len());
        assert forall|i| 0 <= i < trimmed.len() implies trimmed.0[i] == pref.0[i] by {
            assert(self.0[i] == pref.0[i]);
        }
        assert(trimmed.0 == pref.0);
    }

    /// Lemma. Existence of the first differing index between two distinct paths.
    pub broadcast proof fn lemma_first_diff_idx_exists(a: Self, b: Self)
        requires
            a.len() > 0,
            b.len() > 0,
            !#[trigger] a.has_prefix(b),
            !b.has_prefix(a),
        ensures
            exists|i: int|
                0 <= i < a.len() && i < b.len() && a.0[i] != b.0[i] && forall|j: int|
                    0 <= j < i ==> a.0[j] == b.0[j],
    {
        assert(exists|i: int| 0 <= i < a.len() && i < b.len() && a.0[i] != b.0[i]);
        let i = choose|i: int| 0 <= i < a.len() && i < b.len() && a.0[i] != b.0[i];
        Self::lemma_first_diff_idx_exists_recursive(a, b, i);
    }

    /// Helper lemma to prove `lemma_first_diff_idx_exists` by induction.
    proof fn lemma_first_diff_idx_exists_recursive(a: Self, b: Self, i: int)
        requires
            a.len() > 0,
            b.len() > 0,
            !a.has_prefix(b),
            !b.has_prefix(a),
            0 <= i < a.len() && i < b.len() && a.0[i] != b.0[i],
        ensures
            exists|j: int|
                0 <= j <= i && a.0[j] != b.0[j] && forall|k: int| 0 <= k < j ==> a.0[k] == b.0[k],
        decreases i,
    {
        if exists|j: int| 0 <= j < i && a.0[j] != b.0[j] {
            let j = choose|j: int| 0 <= j < i && a.0[j] != b.0[j];
            Self::lemma_first_diff_idx_exists_recursive(a, b, j);
        } else {
            assert(forall|k: int| 0 <= k < i ==> a.0[k] == b.0[k]);
        }
    }

    /// Lemma. `from_vaddr` produces a valid path.
    pub broadcast proof fn lemma_from_vaddr_yields_valid_path(
        vaddr: VAddr,
        arch: SpecPTArch,
        start: nat,
        end: nat,
    )
        by (nonlinear_arith)
        requires
            start <= end < arch.level_count(),
            arch.valid(),
        ensures
            #[trigger] Self::from_vaddr(vaddr, arch, start, end).valid(arch, start),
    {
        let path = Self::from_vaddr(vaddr, arch, start, end);
        assert forall|i: int| 0 <= i < path.len() implies path.0[i] < arch.entry_count(
            i as nat + start,
        ) by { assert(arch.pte_index(vaddr, i as nat + start) < arch.entry_count(i as nat + start))
        }
    }

    /// Lemma. `from_vaddr_root` produces a valid path.
    pub broadcast proof fn lemma_from_vaddr_root_yields_valid_path(
        vaddr: VAddr,
        arch: SpecPTArch,
        end: nat,
    )
        requires
            end < arch.level_count(),
            arch.valid(),
        ensures
            #[trigger] Self::from_vaddr_root(vaddr, arch, end).valid(arch, 0),
    {
        Self::lemma_from_vaddr_yields_valid_path(vaddr, arch, 0, end);
    }

    /// Lemma. from_vaddr(vaddr, arch, start, end).step().1 == from_vaddr(vaddr, arch, start + 1, end)
    pub broadcast proof fn lemma_from_vaddr_step(
        vaddr: VAddr,
        arch: SpecPTArch,
        start: nat,
        end: nat,
    )
        requires
            start < end < arch.level_count(),
            arch.valid(),
        ensures
            #[trigger] Self::from_vaddr(vaddr, arch, start, end).step().1 == Self::from_vaddr(
                vaddr,
                arch,
                start + 1,
                end,
            ),
    {
        let path = Self::from_vaddr(vaddr, arch, start, end);
        let (idx, remain) = path.step();
        let path2 = Self::from_vaddr(vaddr, arch, start + 1, end);
        assert(remain.0 == path2.0);
    }

    /// Lemma. The address computed by `to_vaddr` is aligned to the frame size of the last level.
    pub broadcast proof fn lemma_to_vaddr_frame_alignment(self, arch: SpecPTArch)
        by (nonlinear_arith)
        requires
            arch.valid(),
            #[trigger] self.valid(arch, 0),
        ensures
            self.to_vaddr(arch).aligned(arch.frame_size((self.len() - 1) as nat).as_nat()),
    {
        let parts: Seq<nat> = Seq::new(
            self.len(),
            |i: int| self.0[i] * arch.frame_size(i as nat).as_nat(),
        );
        let fsize = arch.frame_size((self.len() - 1) as nat).as_nat();
        assert forall|i| 0 <= i < self.len() implies #[trigger] arch.frame_size(i).as_nat() % fsize
            == 0 by {
            arch.lemma_frame_size_aligned((self.len() - 1) as nat, i);
        }
        assert(forall|i| 0 <= i < self.len() ==> parts[i] % fsize == 0);
        // All parts align to the frame size of the last level, prove that sum does too.
        lemma_parts_align_implies_sum_align(parts, fsize);
    }

    /// Lemma. If `path` has a prefix `pref`, then `path.to_vaddr()` has a lower bound.
    pub broadcast proof fn lemma_to_vaddr_lower_bound(arch: SpecPTArch, path: Self, pref: Self)
        requires
            arch.valid(),
            #[trigger] path.valid(arch, 0),
            #[trigger] path.has_prefix(pref),
        ensures
            pref.to_vaddr(arch).0 <= path.to_vaddr(arch).0,
        decreases path.len(),
    {
        if path.len() <= pref.len() {
            // `pref` equals `path`
            path.lemma_prefix_eq_full(pref);
            assert(path.to_vaddr(arch).0 == pref.to_vaddr(arch).0);
        } else {
            // `pref2` is the longest prefix of `path` and not equal to `path`
            let pref2 = path.trim((path.len() - 1) as nat);
            let parts = Seq::new(
                path.len(),
                |i: int| path.0[i] * arch.frame_size(i as nat).as_nat(),
            );
            let pref2_parts = Seq::new(
                pref2.len(),
                |i: int| pref2.0[i] * arch.frame_size(i as nat).as_nat(),
            );
            assert(parts.take(pref2.len() as int) == pref2_parts);

            // Decompose the sum as "pref2 parts" + "remaining part"
            assert(parts.fold_left(0, |sum: nat, part| sum + part) == pref2_parts.fold_left(
                0,
                |sum: nat, part| sum + part,
            ) + path.0[path.len() - 1] * arch.frame_size((path.len() - 1) as nat).as_nat());
            assert(path.to_vaddr(arch).0 >= pref2.to_vaddr(arch).0);

            // Recursive proof for `pref2` and its prefix `pref`
            assert(pref2.has_prefix(pref));
            Self::lemma_to_vaddr_lower_bound(arch, pref2, pref);
        }
    }

    /// Lemma. If `path` has a prefix `pref`, then `path.to_vaddr()` has an upper bound.
    pub broadcast proof fn lemma_to_vaddr_upper_bound(arch: SpecPTArch, path: Self, pref: Self)
        by (nonlinear_arith)
        requires
            arch.valid(),
            #[trigger] path.valid(arch, 0),
            #[trigger] path.has_prefix(pref),
        ensures
            path.to_vaddr(arch).0 <= pref.to_vaddr(arch).0 + arch.frame_size(
                (pref.len() - 1) as nat,
            ).as_nat() - arch.frame_size((path.len() - 1) as nat).as_nat(),
        decreases path.len(),
    {
        if path.len() <= pref.len() {
            // `pref` equals `path`
            path.lemma_prefix_eq_full(pref);
            assert(path.to_vaddr(arch).0 == pref.to_vaddr(arch).0);
        } else {
            // `pref2` is the longest prefix of `path` and not equal to `path`
            let pref2 = path.trim((path.len() - 1) as nat);
            let parts = Seq::new(
                path.len(),
                |i: int| path.0[i] * arch.frame_size(i as nat).as_nat(),
            );
            let pref2_parts = Seq::new(
                pref2.len(),
                |i: int| pref2.0[i] * arch.frame_size(i as nat).as_nat(),
            );
            assert(parts.take(pref2.len() as int) == pref2_parts);

            // Decompose "pref2_parts" as "pref parts" + "remaining part"
            let remain = path.0[path.len() - 1] * arch.frame_size((path.len() - 1) as nat).as_nat();
            assert(parts.fold_left(0, |sum: nat, part| sum + part) == pref2_parts.fold_left(
                0,
                |sum: nat, part| sum + part,
            ) + remain);

            // The remaining part has an upper bound
            assert(path.0[path.len() - 1] <= arch.entry_count((path.len() - 1) as nat) - 1);
            assert(remain <= arch.frame_size((path.len() - 1) as nat).as_nat() * arch.entry_count(
                (path.len() - 1) as nat,
            ) - arch.frame_size((path.len() - 1) as nat).as_nat());
            assert(remain <= arch.frame_size((pref2.len() - 1) as nat).as_nat() - arch.frame_size(
                (path.len() - 1) as nat,
            ).as_nat());

            assert(path.to_vaddr(arch).0 <= pref2.to_vaddr(arch).0 + arch.frame_size(
                (pref2.len() - 1) as nat,
            ).as_nat() - arch.frame_size((path.len() - 1) as nat).as_nat());

            // Recursive proof for `pref2` and its prefix `pref`
            assert(pref2.has_prefix(pref));
            Self::lemma_to_vaddr_upper_bound(arch, pref2, pref);
        }
    }

    /// Lemma. If `a` and `b` are not a prefix of each other, then the order of their virtual
    /// addresses is the same as the order of their path indices.
    pub broadcast proof fn lemma_path_order_implies_vaddr_order(arch: SpecPTArch, a: Self, b: Self)
        by (nonlinear_arith)
        requires
            arch.valid(),
            #[trigger] a.valid(arch, 0),
            b.valid(arch, 0),
            !#[trigger] a.has_prefix(b),
            !b.has_prefix(a),
            a.0[Self::first_diff_idx(a, b)] < b.0[Self::first_diff_idx(a, b)],
        ensures
            a.to_vaddr(arch).0 + arch.frame_size((a.len() - 1) as nat).as_nat() <= b.to_vaddr(
                arch,
            ).0,
    {
        // Trim the paths at the first differing index
        Self::lemma_first_diff_idx_exists(a, b);
        let diff_idx = Self::first_diff_idx(a, b);
        let pref_a = a.trim((diff_idx + 1) as nat);
        let pref_b = b.trim((diff_idx + 1) as nat);

        // Bound the full paths by their prefixes
        Self::lemma_to_vaddr_upper_bound(arch, a, pref_a);
        Self::lemma_to_vaddr_lower_bound(arch, b, pref_b);
        assert(a.to_vaddr(arch).0 + arch.frame_size((a.len() - 1) as nat).as_nat()
            <= pref_a.to_vaddr(arch).0 + arch.frame_size((pref_a.len() - 1) as nat).as_nat());
        assert(pref_b.to_vaddr(arch).0 <= b.to_vaddr(arch).0);

        // `common` is the same part shared by `pref_a` and `pref_b`
        assert(pref_a.trim(diff_idx as nat).0 == pref_b.trim(diff_idx as nat).0);
        let common = pref_a.trim(diff_idx as nat);

        // Show `common_parts` is equally added when computing vaddr
        let common_parts = Seq::new(
            common.len(),
            |i: int| common.0[i] * arch.frame_size(i as nat).as_nat(),
        );
        let pref_a_parts = Seq::new(
            pref_a.len(),
            |i: int| pref_a.0[i] * arch.frame_size(i as nat).as_nat(),
        );
        let pref_b_parts = Seq::new(
            pref_b.len(),
            |i: int| pref_b.0[i] * arch.frame_size(i as nat).as_nat(),
        );
        let fsize = arch.frame_size(diff_idx as nat).as_nat();

        assert(pref_a_parts.take(diff_idx) == common_parts);
        assert(pref_a_parts.fold_left(0, |sum: nat, part| sum + part) == common_parts.fold_left(
            0nat,
            |sum: nat, part| sum + part,
        ) + pref_a.0[diff_idx] * fsize);
        assert(pref_b_parts.take(diff_idx) == common_parts);
        assert(pref_b_parts.fold_left(0, |sum: nat, part| sum + part) == common_parts.fold_left(
            0nat,
            |sum: nat, part| sum + part,
        ) + pref_b.0[diff_idx] * fsize);

        // Decompose the sum as "common parts" + "difference part"
        assert(pref_a.to_vaddr(arch).0 == common.to_vaddr(arch).0 + pref_a.0[diff_idx] * fsize);
        assert(pref_b.to_vaddr(arch).0 == common.to_vaddr(arch).0 + pref_b.0[diff_idx] * fsize);

        // Calculate the minimum difference between `pref_a.to_vaddr()` and `pref_b.to_vaddr()`
        assert(pref_b.to_vaddr(arch).0 - pref_a.to_vaddr(arch).0 == (pref_b.0[diff_idx]
            - pref_a.0[diff_idx]) * fsize);
        assert(pref_b.0[diff_idx] - pref_a.0[diff_idx] >= 1);
        assert(pref_b.to_vaddr(arch).0 - pref_a.to_vaddr(arch).0 >= fsize);

        // Prove the bounded inequality
        assert(a.to_vaddr(arch).0 + arch.frame_size((a.len() - 1) as nat).as_nat() <= b.to_vaddr(
            arch,
        ).0);
    }

    /// Lemma. If `a` and `b` are not a prefix of each other, then `a.vaddr() != b.vaddr()`.
    pub broadcast proof fn lemma_nonprefix_implies_vaddr_inequality(
        arch: SpecPTArch,
        a: Self,
        b: Self,
    )
        requires
            arch.valid(),
            #[trigger] a.valid(arch, 0),
            b.valid(arch, 0),
            !#[trigger] a.has_prefix(b),
            !b.has_prefix(a),
        ensures
            a.to_vaddr(arch) != b.to_vaddr(arch),
    {
        Self::lemma_first_diff_idx_exists(a, b);
        let diff_idx = Self::first_diff_idx(a, b);
        if a.0[diff_idx] < b.0[diff_idx] {
            Self::lemma_path_order_implies_vaddr_order(arch, a, b);
        } else {
            Self::lemma_path_order_implies_vaddr_order(arch, b, a);
        }
    }

    /// Lemma. If `a.to_vaddr()` is equal to `b.to_vaddr()`, then `a` is a real prefix of `b` or
    /// `b` is a real prefix of `a`.
    pub broadcast proof fn lemma_vaddr_eq_implies_real_prefix(arch: SpecPTArch, a: Self, b: Self)
        requires
            #[trigger] arch.valid(),
            a.valid(arch, 0),
            b.valid(arch, 0),
            a.to_vaddr(arch) == b.to_vaddr(arch),
        ensures
            #[trigger] a.has_real_prefix(b) || b.has_real_prefix(a),
    {
        // TODO
        assume(false);
    }

    /// Lemma. If `a` is a real prefix of `b`, then `a.to_vaddr() == b.to_vaddr()`.
    pub broadcast proof fn lemma_real_prefix_implies_vaddr_eq(arch: SpecPTArch, a: Self, b: Self)
        requires
            #[trigger] arch.valid(),
            a.valid(arch, 0),
            b.valid(arch, 0),
            #[trigger] a.has_real_prefix(b),
        ensures
            a.to_vaddr(arch) == b.to_vaddr(arch),
    {
        let a_parts: Seq<nat> = Seq::new(
            a.len(),
            |i: int| a.0[i] * arch.frame_size(i as nat).as_nat(),
        );
        let b_parts: Seq<nat> = Seq::new(
            b.len(),
            |i: int| b.0[i] * arch.frame_size(i as nat).as_nat(),
        );
        assert(a_parts.take(b.len() as int) == b_parts);
        let a_sum = a_parts.fold_right(|part: nat, sum: nat| part + sum, 0nat);
        let b_sum = b_parts.fold_right(|part: nat, sum: nat| part + sum, 0nat);
        let seq2 = a_parts.skip(b.len() as int);

        a_parts.lemma_fold_right_split(|part: nat, sum: nat| part + sum, 0nat, b.len() as int);
        assert(a_sum == b_parts.fold_right(
            |part: nat, sum: nat| part + sum,
            seq2.fold_right(|part: nat, sum: nat| part + sum, 0nat),
        ));

        assert(seq2 == Seq::new((a.len() - b.len()) as nat, |_i| 0nat));
        lemma_zero_seq_sum_is_zero(seq2);
        assert(seq2.fold_right(|part: nat, sum: nat| part + sum, 0nat) == 0);
        assert(a_sum == b_sum);

        lemma_left_sum_eq_right_sum(a_parts);
        lemma_left_sum_eq_right_sum(b_parts);

        assert(a.to_vaddr(arch).0 == a_parts.fold_left(0, |sum: nat, part| sum + part));
        assert(b.to_vaddr(arch).0 == b_parts.fold_left(0, |sum: nat, part| sum + part));
        assert(a.to_vaddr(arch).0 == a_sum);
        assert(b.to_vaddr(arch).0 == b_sum);
    }

    /// Lemma. The computed base virtual address of a path and the frame size guarantee that
    /// any derived `to_vaddr` falls within the address window.
    pub broadcast proof fn lemma_vaddr_range_from_path(arch: SpecPTArch, vaddr: VAddr, path: Self)
        requires
            arch.valid(),
            path.valid(arch, 0),
            path == #[trigger] Self::from_vaddr_root(vaddr, arch, (path.len() - 1) as nat),
        ensures
            path.to_vaddr(arch).0 <= vaddr.0 < path.to_vaddr(arch).0 + arch.frame_size(
                (path.len() - 1) as nat,
            ).as_nat(),
    {
        let parts: Seq<nat> = Seq::new(
            path.len(),
            |i: int| path.0[i] * arch.frame_size(i as nat).as_nat(),
        );
        assert(forall|i|
            0 <= i < path.len() ==> parts[i] == arch.pte_index(vaddr, i as nat) * arch.frame_size(
                i as nat,
            ).as_nat());
        // TODO: consider adding a lemma to `PTArch`
        assume(false);
    }

    /// Lemma. Converting a vaddr into a path and then back exactly inverts the operation.
    pub broadcast proof fn lemma_to_vaddr_inverts_from_vaddr(
        arch: SpecPTArch,
        vaddr: VAddr,
        path: Self,
    )
        requires
            arch.valid(),
            path.valid(arch, 0),
            vaddr.aligned(arch.frame_size((path.len() - 1) as nat).as_nat()),
            path == #[trigger] Self::from_vaddr_root(vaddr, arch, (path.len() - 1) as nat),
        ensures
            path.to_vaddr(arch) == vaddr,
    {
        let fsize = arch.frame_size((path.len() - 1) as nat).as_nat();
        Self::lemma_vaddr_range_from_path(arch, vaddr, path);

        assert(vaddr.0 - fsize < path.to_vaddr(arch).0 <= vaddr.0);
        path.lemma_to_vaddr_frame_alignment(arch);

        assert(vaddr.0 % fsize == 0);
        assert((vaddr.0 - fsize) / fsize as int == vaddr.0 / fsize - 1);
        assert(vaddr.0 / fsize - 1 < path.to_vaddr(arch).0 / fsize <= vaddr.0 / fsize);

        assert(path.to_vaddr(arch).0 / fsize == vaddr.0 / fsize);
        assert(path.to_vaddr(arch).0 == vaddr.0);
    }
}

/// Lemma. If a sequence is a zero sequence, then its sum is zero.
pub proof fn lemma_zero_seq_sum_is_zero(s: Seq<nat>)
    requires
        s == seq![0nat; s.len()],
    ensures
        s.fold_right(|part: nat, sum: nat| part + sum, 0nat) == 0,
    decreases s.len(),
{
    let f = |part: nat, sum: nat| part + sum;
    let sum = s.fold_right(f, 0nat);
    if s.len() == 0 {
        assert(sum == 0);
    } else {
        let sub = s.subrange(0, s.len() - 1);
        assert(sub == Seq::new(sub.len(), |_i| 0nat));
        assert(sum == sub.fold_right(f, s.last()));
        lemma_zero_seq_sum_is_zero(sub);
    }
}

/// Lemma. Left sum is equal to right sum (fold_right_alt).
proof fn lemma_left_sum_eq_right_sum_alt(s: Seq<nat>)
    ensures
        s.fold_left(0nat, |sum: nat, part: nat| sum + part) == s.fold_right_alt(
            |part: nat, sum: nat| part + sum,
            0nat,
        ),
    decreases s.len(),
{
    let lsum = s.fold_left(0nat, |sum: nat, part: nat| sum + part);
    let rsum = s.fold_right_alt(|part: nat, sum: nat| part + sum, 0nat);
    if s.len() > 0 {
        let lsub = s.subrange(0, s.len() - 1);
        let lsub_lsum = lsub.fold_left(0nat, |sum: nat, part: nat| sum + part);
        let lsub_rsum = lsub.fold_right_alt(|part: nat, sum: nat| part + sum, 0nat);
        assert(lsum == lsub_lsum + s.last());

        let rsub = s.subrange(1, s.len() as int);
        let rsub_lsum = rsub.fold_left(0nat, |sum: nat, part: nat| sum + part);
        let rsub_rsum = rsub.fold_right_alt(|part: nat, sum: nat| part + sum, 0nat);

        assert(rsum == s[0] + rsub.fold_right_alt(|part: nat, sum: nat| part + sum, 0nat));

        lemma_left_sum_eq_right_sum_alt(lsub);
        lemma_left_sum_eq_right_sum_alt(rsub);
        assert(lsub_lsum == lsub_rsum);

        if lsub.len() > 0 {
            let lsub_rsub = lsub.subrange(1, lsub.len() as int);
            assert(lsub_rsum == lsub.first() + lsub_rsub.fold_right_alt(
                |part: nat, sum: nat| part + sum,
                0nat,
            ));
            let rsub_lsub = rsub.subrange(0, rsub.len() - 1);
            assert(rsub_lsum == rsub.last() + rsub_lsub.fold_left(
                0nat,
                |sum: nat, part: nat| sum + part,
            ));
            assert(lsub_rsub == rsub_lsub);

            lemma_left_sum_eq_right_sum_alt(lsub_rsub);
            let sub_sub_sum = lsub_rsub.fold_right_alt(|part: nat, sum: nat| part + sum, 0nat);

            assert(lsum == s.last() + s.first() + sub_sub_sum);
            assert(rsum == s.first() + s.last() + sub_sub_sum);

            assert(lsum == rsum);
        }
    }
}

/// Lemma. Left sum is equal to right sum.
pub proof fn lemma_left_sum_eq_right_sum(s: Seq<nat>)
    ensures
        s.fold_left(0nat, |sum: nat, part: nat| sum + part) == s.fold_right(
            |part: nat, sum: nat| part + sum,
            0nat,
        ),
{
    lemma_left_sum_eq_right_sum_alt(s);
    s.lemma_fold_right_alt(|part: nat, sum: nat| part + sum, 0nat);
}

/// Lemma. If all parts align to a value, then the sum of the parts aligns to the same value.
pub proof fn lemma_parts_align_implies_sum_align(s: Seq<nat>, align: nat)
    by (nonlinear_arith)
    requires
        align > 0,
        forall|i| 0 <= i < s.len() ==> s[i] % align == 0,
    ensures
        s.fold_left(0nat, |sum: nat, part: nat| sum + part) % align == 0,
    decreases s.len(),
{
    let sum = s.fold_left(0nat, |sum: nat, part: nat| sum + part);
    if s.len() > 0 {
        let sub = s.subrange(0, s.len() - 1);
        let sub_sum = sub.fold_left(0nat, |sum: nat, part: nat| sum + part);
        lemma_parts_align_implies_sum_align(sub, align);
        assert(sum == sub_sum + s.last());
        vstd::arithmetic::div_mod::lemma_add_mod_noop(
            sub_sum as int,
            s.last() as int,
            align as int,
        );
    }
}

pub broadcast group group_pt_tree_path_lemmas {
    // prefix related lemmas
    PTTreePath::lemma_eq_step,
    PTTreePath::lemma_prefix_eq_full,
    PTTreePath::lemma_prefix_step,
    PTTreePath::lemma_trim_prefix,
    PTTreePath::lemma_first_diff_idx_exists,
    // vaddr related lemmas
    PTTreePath::lemma_from_vaddr_yields_valid_path,
    PTTreePath::lemma_from_vaddr_root_yields_valid_path,
    PTTreePath::lemma_from_vaddr_step,
    PTTreePath::lemma_to_vaddr_frame_alignment,
    PTTreePath::lemma_to_vaddr_lower_bound,
    PTTreePath::lemma_to_vaddr_upper_bound,
    PTTreePath::lemma_path_order_implies_vaddr_order,
    PTTreePath::lemma_nonprefix_implies_vaddr_inequality,
    PTTreePath::lemma_vaddr_eq_implies_real_prefix,
    PTTreePath::lemma_real_prefix_implies_vaddr_eq,
    PTTreePath::lemma_vaddr_range_from_path,
    PTTreePath::lemma_to_vaddr_inverts_from_vaddr,
}

} // verus!
