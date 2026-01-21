//! Abstract page table memory and specification.
//!
//! Page Table Memory is a collection of page tables, and provides read/write, alloc/dealloc functionality.
//! The implementation should refine the specification defined in `spec::memory::PageTableMem`.
use vstd::prelude::*;

use crate::address::{
    addr::{PAddr, PAddrExec, VAddr, VAddrExec},
    frame::FrameSize,
};
use crate::page_table::pt_arch::{PTArch, SpecPTArch};

verus! {

/// Describe a page table stored in physical memory.
pub struct SpecTable {
    /// Base address of the table.
    pub base: PAddr,
    /// Size of the table.
    pub size: FrameSize,
    /// Level of the table.
    pub level: nat,
}

/// Abstract model of page table memory, a memory region that stores page tables.
///
/// Hardware reads page table memory to perform page table walk, but cannot write to it.
/// Page table memory is modified by page table functions.
pub struct SpecPageTableMem {
    /// All tables in the hierarchical page table, the first table is the root.
    pub tables: Seq<SpecTable>,
    /// Page table architecture.
    pub arch: SpecPTArch,
}

impl SpecPageTableMem {
    /// Root page table address.
    pub open spec fn root(self) -> PAddr {
        self.tables[0].base
    }

    /// If the table with the given base address exists.
    pub open spec fn contains_table(self, base: PAddr) -> bool {
        exists|table: SpecTable| #[trigger] self.tables.contains(table) && table.base == base
    }

    /// Get the table with the given base address.
    pub open spec fn table(self, base: PAddr) -> SpecTable
        recommends
            self.contains_table(base),
    {
        choose|table: SpecTable| #[trigger] self.tables.contains(table) && table.base == base
    }

    /// View a table as a sequence of entries.
    pub uninterp spec fn table_view(self, base: PAddr) -> Seq<u64>
        recommends
            self.contains_table(base),
    ;

    /// Facts about table view.
    #[verifier::external_body]
    pub broadcast proof fn table_view_facts(self, base: PAddr)
        requires
            self.wf(),
        ensures
            #[trigger] self.table_view(base).len() == self.arch.entry_count(self.table(base).level),
    {
    }

    /// If a table is empty.
    pub open spec fn is_table_empty(self, base: PAddr) -> bool
        recommends
            self.contains_table(base),
    {
        self.table_view(base) == Seq::new(self.table_view(base).len(), |_i| 0u64)
    }

    /// If accessing the given table at the given index is allowed.
    pub open spec fn accessible(self, base: PAddr, index: nat) -> bool {
        self.contains_table(base) && index < self.arch.entry_count(self.table(base).level)
    }

    /// Read the entry at the given index in the given table.
    pub open spec fn read(self, base: PAddr, index: nat) -> u64
        recommends
            self.accessible(base, index),
    {
        self.table_view(base)[index as int]
    }

    /// Well-formedness.
    pub open spec fn wf(self) -> bool {
        &&& self.arch.valid()
        // Root table is always present.
        &&& self.tables.len() > 0
        // Root table level is 0
        &&& self.tables[0].level == 0
        // Table level is valid.
        &&& forall|i|
            0 <= i < self.tables.len() ==> #[trigger] self.tables[i].level
                < self.arch.level_count()
        // Table size is valid.
        &&& forall|i|
            0 <= i < self.tables.len() ==> #[trigger] self.tables[i].size.as_nat()
                == self.arch.table_size(
                self.tables[i].level,
            )
        // All tables should not overlap.
        &&& forall|i, j|
            0 <= i < self.tables.len() && 0 <= j < self.tables.len() ==> i == j || !PAddr::overlap(
                self.tables[i].base,
                self.tables[i].size.as_nat(),
                self.tables[j].base,
                self.tables[j].size.as_nat(),
            )
    }

    /// Init State.
    pub open spec fn init(self) -> bool {
        &&& self.arch.valid()
        &&& self.tables.len() == 1
        &&& self.tables[0].level == 0
        &&& self.tables[0].size.as_nat() == self.arch.table_size(0)
        &&& self.table_view(self.root()) == Seq::new(self.arch.entry_count(0), |_i| 0u64)
    }

    /// Allocate a new table.
    pub uninterp spec fn alloc_table(self, level: nat) -> (Self, SpecTable)
        recommends
            self.alloc_table_pre(level),
    ;

    /// Precondition for `alloc_table`.
    pub open spec fn alloc_table_pre(self, level: nat) -> bool {
        level < self.arch.level_count()
    }

    /// Specification of `alloc_table`.
    pub open spec fn alloc_table_spec(s1: Self, s2: Self, level: nat, table: SpecTable) -> bool {
        &&& s1.alloc_table_pre(level)
        &&& (s2, table) == s1.alloc_table(level)
        // `arch` is unchanged
        &&& s2.arch == s1.arch
        // `self` doesn't have the table
        &&& !s1.contains_table(table.base)
        // new table has valid level
        &&& table.level == level
        // new table has valid size
        &&& table.size.as_nat() == s1.arch.table_size(
            level,
        )
        // new table is aligned
        &&& table.base.aligned(table.size.as_nat())
        // new table is empty
        &&& s2.table_view(table.base) == Seq::new(
            s2.arch.entry_count(level),
            |_i| 0u64,
        )
        // old tables are the same
        &&& forall|base: PAddr| #[trigger]
            s1.contains_table(base) ==> s2.table_view(base) == s1.table_view(
                base,
            )
        // new table doesn't overlap with existing tables
        &&& forall|i|
            #![auto]
            0 <= i < s1.tables.len() ==> !PAddr::overlap(
                s1.tables[i].base,
                s1.tables[i].size.as_nat(),
                table.base,
                table.size.as_nat(),
            )
            // `tables` is updated
        &&& s2.tables == s1.tables.push(table)
    }

    /// Restrict `alloc_table` using proof fn.
    pub broadcast proof fn alloc_table_facts(self, level: nat)
        requires
            self.alloc_table_pre(level),
        ensures
            ({
                let (s2, table) = #[trigger] self.alloc_table(level);
                Self::alloc_table_spec(self, s2, level, table)
            }),
    {
        admit();
    }

    /// Deallocate a table.
    pub uninterp spec fn dealloc_table(self, base: PAddr) -> Self
        recommends
            self.dealloc_table_pre(base),
    ;

    /// Precondition for `dealloc_table`.
    pub open spec fn dealloc_table_pre(self, base: PAddr) -> bool {
        &&& self.contains_table(base)
        &&& base != self.root()
    }

    /// Specification of `dealloc_table`.
    pub open spec fn dealloc_table_spec(s1: Self, s2: Self, base: PAddr) -> bool {
        &&& s1.dealloc_table_pre(base)
        &&& s2 == s1.dealloc_table(base)
        // `arch` is unchanged
        &&& s2.arch == s1.arch
        // Root is preserved
        &&& s2.tables[0] == s1.tables[0]
        // `base` is removed
        &&& !s2.contains_table(base)
        // Subset
        &&& forall|table|
            s2.tables.contains(table) ==> s1.tables.contains(
                table,
            )
        // Other tables are the same
        &&& forall|table| #[trigger]
            s1.tables.contains(table) && table.base != base ==> s2.tables.contains(
                table,
            )
        // Table base unique
        &&& forall|i, j|
            #![auto]
            0 <= i < s2.tables.len() && 0 <= j < s2.tables.len() ==> i == j || s2.tables[i].base
                != s2.tables[j].base
        // Table contents are the same
        &&& forall|base: PAddr| #[trigger]
            s1.contains_table(base) ==> s2.table_view(base) == s1.table_view(base)
    }

    /// Restrict `dealloc_table` using proof fn.
    pub broadcast proof fn dealloc_table_facts(self, base: PAddr)
        requires
            self.dealloc_table_pre(base),
        ensures
            Self::dealloc_table_spec(self, #[trigger] self.dealloc_table(base), base),
    {
        admit();
    }

    /// Update the entry at the given index in the given table.
    pub uninterp spec fn write(self, base: PAddr, index: nat, entry: u64) -> Self
        recommends
            self.write_pre(base, index),
    ;

    /// Precondition for `write`.
    pub open spec fn write_pre(self, base: PAddr, index: nat) -> bool {
        self.accessible(base, index)
    }

    /// Specification of `write`.
    pub open spec fn write_spec(s1: Self, s2: Self, base: PAddr, index: nat, entry: u64) -> bool {
        &&& s1.write_pre(base, index)
        &&& s2 == s1.write(base, index, entry)
        // `arch` is unchanged
        &&& s2.arch == s1.arch
        // Tables are the same
        &&& s2.tables == s1.tables
        // The entry is updated
        &&& s2.table_view(base) == s1.table_view(base).update(
            index as int,
            entry,
        )
        // Other tables contents are the same
        &&& forall|i|
            #![auto]
            0 <= i < s1.tables.len() && s1.tables[i].base != base ==> s2.table_view(
                s1.tables[i].base,
            ) == s1.table_view(s1.tables[i].base)
    }

    /// Restrict `write` using proof fn.
    pub broadcast proof fn write_facts(self, base: PAddr, index: nat, entry: u64)
        requires
            self.write_pre(base, index),
        ensures
            Self::write_spec(self, #[trigger] self.write(base, index, entry), base, index, entry),
    {
        admit();
    }

    /// Lemma. Different tables have different base addresses.
    pub broadcast proof fn lemma_table_base_unique(self)
        requires
            #[trigger] self.wf(),
        ensures
            forall|i, j|
                #![auto]
                0 <= i < self.tables.len() && 0 <= j < self.tables.len() ==> i == j
                    || self.tables[i].base != self.tables[j].base,
    {
        assert forall|i, j|
            #![auto]
            0 <= i < self.tables.len() && 0 <= j < self.tables.len() implies i == j
            || self.tables[i].base != self.tables[j].base by {
            if i != j && self.tables[i].base == self.tables[j].base {
                assert(PAddr::overlap(
                    self.tables[i].base,
                    self.tables[i].size.as_nat(),
                    self.tables[j].base,
                    self.tables[j].size.as_nat(),
                ));
            }
        }
    }

    /// Lemma. Always contains a root table.
    pub broadcast proof fn lemma_contains_root(self)
        requires
            #[trigger] self.wf(),
        ensures
            self.contains_table(self.root()),
            self.table(self.root()) == self.tables[0],
    {
        assert(self.tables.contains(self.tables[0]));
        self.lemma_table_base_unique();
    }

    /// Lemma. `init` implies well-formedness.
    pub broadcast proof fn lemma_init_implies_wf(self)
        requires
            #[trigger] self.init(),
        ensures
            self.wf(),
    {
    }

    /// Lemma. `alloc_table` preserves wf.
    pub broadcast proof fn lemma_alloc_table_preserves_wf(
        s1: Self,
        s2: Self,
        level: nat,
        table: SpecTable,
    )
        requires
            s1.wf(),
            #[trigger] Self::alloc_table_spec(s1, s2, level, table),
        ensures
            s2.wf(),
    {
        assert forall|table2: SpecTable| #[trigger] s2.tables.contains(table2) implies table2.level
            < s2.arch.level_count() by {
            if table2 != table {
                assert(s2.tables.contains(table2));
            }
        }
    }

    /// Lemma. `alloc_table` preserves accessibility.
    pub broadcast proof fn lemma_alloc_table_preserves_accessibility(
        s1: Self,
        s2: Self,
        level: nat,
        table: SpecTable,
        base: PAddr,
        index: nat,
    )
        requires
            s1.wf(),
            #[trigger] Self::alloc_table_spec(s1, s2, level, table),
            #[trigger] s1.accessible(base, index),
        ensures
            s2.accessible(base, index),
    {
        // s2 contains table with base address `base`
        assert(s1.contains_table(base));
        assert forall|table2: SpecTable| s1.tables.contains(table2) implies s2.tables.contains(
            table2,
        ) by {
            let idx = choose|i| 0 <= i < s1.tables.len() && s1.tables[i] == table2;
            assert(s2.tables[idx] == table2);
        }
        assert(s2.contains_table(base));

        // The table with base address `base` is the same as the table in `s1`
        Self::lemma_alloc_table_preserves_wf(s1, s2, level, table);
        s2.lemma_table_base_unique();
        assert(s1.table(base) == s2.table(base));
    }

    /// Lemma. pt_mem after `alloc_table` contains the new table.
    pub broadcast proof fn lemma_allocated_contains_new_table(
        s1: Self,
        s2: Self,
        level: nat,
        table: SpecTable,
    )
        requires
            s1.wf(),
            #[trigger] Self::alloc_table_spec(s1, s2, level, table),
        ensures
            s2.contains_table(table.base),
    {
        assert(s2.tables == s1.tables.push(table));
        assert(s2.tables.last() == table);
        assert(s2.tables.contains(table));
    }

    /// Lemma. pt_mem after `alloc_table` contains all pre-existing tables.
    pub broadcast proof fn lemma_allocated_contains_old_tables(
        s1: Self,
        s2: Self,
        level: nat,
        table: SpecTable,
    )
        requires
            s1.wf(),
            #[trigger] Self::alloc_table_spec(s1, s2, level, table),
        ensures
            forall|base: PAddr|
                s2.contains_table(base) && base != table.base ==> s1.contains_table(base),
    {
        assert forall|base: PAddr|
            s2.contains_table(base) && base != table.base implies s1.contains_table(base) by {
            let table = choose|table: SpecTable| #[trigger]
                s2.tables.contains(table) && table.base == base;
            assert(s1.tables.contains(table));
        }
    }

    /// Lemma. `self.tables` after `alloc_table` is a superset of before.
    pub broadcast proof fn lemma_allocated_is_superset(
        s1: Self,
        s2: Self,
        level: nat,
        table: SpecTable,
    )
        requires
            s1.wf(),
            #[trigger] Self::alloc_table_spec(s1, s2, level, table),
        ensures
            forall|base: PAddr| s1.contains_table(base) ==> s2.contains_table(base),
    {
        assert forall|base: PAddr| s1.contains_table(base) implies s2.contains_table(base) by {
            let i = choose|i| 0 <= i < s1.tables.len() && #[trigger] s1.tables[i].base == base;
            assert(s2.tables.contains(s2.tables[i]));
        }
    }

    /// Lemma. `dealloc_table` preserves wf.
    pub broadcast proof fn lemma_dealloc_table_preserves_wf(s1: Self, s2: Self, base: PAddr)
        requires
            s1.wf(),
            #[trigger] Self::dealloc_table_spec(s1, s2, base),
        ensures
            s2.wf(),
    {
        s1.lemma_contains_root();
        assert forall|i| 0 <= i < s2.tables.len() implies #[trigger] s2.tables[i].level
            < s2.arch.level_count() by {
            assert(s2.tables.contains(s2.tables[i]));
        }
        assert forall|i| 0 <= i < s2.tables.len() implies #[trigger] s2.tables[i].size.as_nat()
            == s2.arch.table_size(s2.tables[i].level) by {
            assert(s2.tables.contains(s2.tables[i]));
        }
        assert forall|i, j| 0 <= i < s2.tables.len() && 0 <= j < s2.tables.len() implies i == j
            || !PAddr::overlap(
            s2.tables[i].base,
            s2.tables[i].size.as_nat(),
            s2.tables[j].base,
            s2.tables[j].size.as_nat(),
        ) by {
            assert(s2.tables.contains(s2.tables[i]));
            assert(s2.tables.contains(s2.tables[j]));
        }
    }

    /// Lemma. `write` preserves wf.
    pub broadcast proof fn lemma_write_preserves_wf(
        s1: Self,
        s2: Self,
        base: PAddr,
        index: nat,
        entry: u64,
    )
        requires
            s1.wf(),
            #[trigger] Self::write_spec(s1, s2, base, index, entry),
        ensures
            s2.wf(),
    {
    }
}

/// Broadcast page table memory related lemmas.
pub broadcast group group_pt_mem_lemmas {
    SpecPageTableMem::table_view_facts,
    SpecPageTableMem::alloc_table_facts,
    SpecPageTableMem::dealloc_table_facts,
    SpecPageTableMem::write_facts,
    SpecPageTableMem::lemma_table_base_unique,
    SpecPageTableMem::lemma_contains_root,
    SpecPageTableMem::lemma_init_implies_wf,
    SpecPageTableMem::lemma_alloc_table_preserves_wf,
    SpecPageTableMem::lemma_allocated_contains_new_table,
    SpecPageTableMem::lemma_allocated_contains_old_tables,
    SpecPageTableMem::lemma_allocated_is_superset,
    SpecPageTableMem::lemma_alloc_table_preserves_accessibility,
    SpecPageTableMem::lemma_dealloc_table_preserves_wf,
    SpecPageTableMem::lemma_write_preserves_wf,
}

/// Specifiaction that executable page table memory should satisfy.
pub trait PageTableMem: Sized {
    /// View as an abstract page table memory.
    open spec fn view(self) -> SpecPageTableMem {
        // If the exec-mode page table memory implementation doesn't want to provide proof,
        // it could just use this default version, which will not affect functionality.
        //
        // However, this may lead to unsafety since Verus cannot reason about the page table memory structure.
        SpecPageTableMem { arch: SpecPTArch(Seq::empty()), tables: Seq::empty() }
    }

    /// Invariants that must be implied at initial state and preseved after each operation.
    spec fn invariants(self) -> bool;

    /// Physical address of the root page table.
    fn root(&self) -> (res: PAddrExec)
        requires
            self@.tables.len() > 0,
        ensures
            res@ == self@.root(),
    ;

    /// If a table is empty.
    fn is_table_empty(&self, base: PAddrExec) -> (res: bool)
        requires
            self@.contains_table(base@),
        ensures
            res == self@.is_table_empty(base@),
    ;

    /// Allocate a new table and returns the table base address and size.
    fn alloc_table(&mut self, level: usize) -> (res: (PAddrExec, FrameSize))
        requires
            old(self).invariants(),
            old(self)@.alloc_table_pre(level as nat),
        ensures
            self.invariants(),
            SpecPageTableMem::alloc_table_spec(
                old(self)@,
                self@,
                level as nat,
                SpecTable { base: res.0@, size: res.1, level: level as nat },
            ),
    ;

    /// Deallocate a table.
    fn dealloc_table(&mut self, base: PAddrExec)
        requires
            old(self).invariants(),
            old(self)@.dealloc_table_pre(base@),
        ensures
            self.invariants(),
            SpecPageTableMem::dealloc_table_spec(old(self)@, self@, base@),
    ;

    /// Get the value at the given index in the given table.
    fn read(&self, base: PAddrExec, index: usize) -> (res: u64)
        requires
            self.invariants(),
            self@.accessible(base@, index as nat),
        ensures
            self@.read(base@, index as nat) == res,
    ;

    /// Write the value to the given index in the given table.
    fn write(&mut self, base: PAddrExec, index: usize, value: u64)
        requires
            old(self).invariants(),
            old(self)@.write_pre(base@, index as nat),
        ensures
            self.invariants(),
            SpecPageTableMem::write_spec(old(self)@, self@, base@, index as nat, value),
    ;

    /// Lemma. Invariants implies well-formedness.
    broadcast proof fn lemma_invariants_implies_wf(self)
        requires
            #[trigger] self.invariants(),
        ensures
            self@.wf(),
    ;
}

} // verus!
