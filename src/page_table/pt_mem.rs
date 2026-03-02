//! Abstract page table memory and specification.
//!
//! Page Table Memory is a collection of page tables, and provides read/write, alloc/dealloc functionality.
//! The implementation should refine the specification defined in `spec::memory::PageTableMem`.
use std::marker::PhantomData;
use vstd::prelude::*;

use crate::{
    address::{
        addr::{PAddr, SpecPAddr, SpecVAddr, VAddr},
        frame::FrameSize,
    },
    frame_allocator::frame_trait::FrameAllocator,
    global_allocator::{
        frame::{Frame4K, GlobalFrameAllocator},
        GlobalAllocator, Resource,
    },
    page_table::pt_arch::{PTArch, SpecPTArch},
};

verus! {

/// Abstract model of page table memory, a memory region that stores page tables.
///
/// Hardware reads page table memory to perform page table walk, but cannot write to it.
/// Page table memory is modified by page table functions.
pub struct SpecPageTableMem {
    /// All tables in the hierarchical page table, the key is the base address of the table,
    /// and the value is the level of the table.
    pub tables: Map<SpecPAddr, nat>,
    /// Page table architecture.
    pub arch: SpecPTArch,
    /// Root table address.
    pub root: SpecPAddr,
}

impl SpecPageTableMem {
    /// Get the table with the given base address.
    pub open spec fn level(self, base: SpecPAddr) -> nat
        recommends
            self.contains_table(base),
    {
        self.tables[base]
    }

    /// If the table with the given base address exists.
    pub open spec fn contains_table(self, base: SpecPAddr) -> bool {
        self.tables.contains_key(base)
    }

    /// If the table with the given base address and level exists.
    pub open spec fn contains_table_with_level(self, base: SpecPAddr, level: nat) -> bool {
        self.tables.contains_key(base) && self.tables[base] == level
    }

    /// View a table as a sequence of entries.
    pub uninterp spec fn table_view(self, base: SpecPAddr) -> Seq<u64>
        recommends
            self.contains_table(base),
    ;

    /// Facts about table view. It should not be called directly.
    pub broadcast proof fn table_view_facts(self, base: SpecPAddr)
        requires
            self.wf(),
        ensures
            #[trigger] self.table_view(base).len() == self.arch.entry_count(self.tables[base]),
    {
        admit();
    }

    /// Well-formedness.
    pub open spec fn wf(self) -> bool {
        &&& self.arch.valid()
        // Root table is always present.
        &&& self.contains_table_with_level(
            self.root,
            0,
        )
        // Table level is valid.
        &&& forall|base: SpecPAddr| #[trigger]
            self.tables.contains_key(base) ==> self.tables[base]
                < self.arch.level_count()
        // All tables are properly aligned.
        &&& forall|base: SpecPAddr| #[trigger]
            self.tables.contains_key(base) ==> base.aligned(
                self.arch.table_size(self.tables[base]),
            )
        // All tables should not overlap.
        &&& forall|base1: SpecPAddr, base2: SpecPAddr|
            self.tables.contains_key(base1) && self.tables.contains_key(base2) && base1 != base2
                ==> !SpecPAddr::overlap(
                base1,
                self.arch.table_size(self.tables[base1]),
                base2,
                self.arch.table_size(self.tables[base2]),
            )
    }

    /// Init State.
    pub open spec fn init(self) -> bool {
        &&& self.arch.valid()
        // Contains only the root table
        &&& self.tables
            == map![self.root => 0nat]
        // Root table is aligned
        &&& self.root.aligned(
            self.arch.table_size(0),
        )
        // Root table is empty
        &&& self.table_view(self.root) == Seq::new(self.arch.entry_count(0), |_i| 0u64)
    }

    /// If a table is empty.
    pub open spec fn is_table_empty(self, base: SpecPAddr) -> bool
        recommends
            self.contains_table(base),
    {
        self.table_view(base) == Seq::new(self.table_view(base).len(), |_i| 0u64)
    }

    /// If accessing the given table at the given index is allowed.
    pub open spec fn accessible(self, base: SpecPAddr, index: nat) -> bool {
        self.contains_table(base) && index < self.arch.entry_count(self.tables[base])
    }

    /// Read the entry at the given index in the given table.
    pub open spec fn read(self, base: SpecPAddr, index: nat) -> u64
        recommends
            self.accessible(base, index),
    {
        self.table_view(base)[index as int]
    }

    /// Allocate a new table.
    pub uninterp spec fn alloc_table(self, level: nat) -> (Self, SpecPAddr)
        recommends
            self.alloc_table_pre(level),
    ;

    /// Precondition for `alloc_table`.
    pub open spec fn alloc_table_pre(self, level: nat) -> bool {
        level < self.arch.level_count()
    }

    /// Specification of `alloc_table`.
    pub open spec fn alloc_table_spec(s1: Self, s2: Self, level: nat, new_base: SpecPAddr) -> bool {
        &&& s1.alloc_table_pre(level)
        &&& (s2, new_base) == s1.alloc_table(level)
        // `arch` is unchanged
        &&& s2.arch == s1.arch
        // `root` is unchanged
        &&& s2.root == s1.root
        // `s1` doesn't have the table
        &&& !s1.contains_table(new_base)
        // new table is aligned
        &&& new_base.aligned(
            s1.arch.table_size(level),
        )
        // new table doesn't overlap with existing tables
        &&& forall|base: SpecPAddr| #[trigger]
            s1.tables.contains_key(base) ==> !SpecPAddr::overlap(
                new_base,
                s1.arch.table_size(level),
                base,
                s1.arch.table_size(s1.level(base)),
            )
            // new table is empty
        &&& s2.table_view(new_base) == Seq::new(
            s2.arch.entry_count(level),
            |_i| 0u64,
        )
        // new table is added
        &&& s2.tables == s1.tables.insert(
            new_base,
            level,
        )
        // old tables' contents are preserved
        &&& forall|base: SpecPAddr| #[trigger]
            s1.tables.contains_key(base) ==> s2.table_view(base) == s1.table_view(base)
    }

    /// Restrict `alloc_table` using proof fn. It should not be called when we want to reason about
    /// the executable implementation of the `alloc_table` function.
    pub broadcast proof fn alloc_table_facts(self, level: nat)
        requires
            self.alloc_table_pre(level),
        ensures
            ({
                let (s2, new_base) = #[trigger] self.alloc_table(level);
                Self::alloc_table_spec(self, s2, level, new_base)
            }),
    {
        admit();
    }

    /// Deallocate a table.
    pub uninterp spec fn dealloc_table(self, base: SpecPAddr) -> Self
        recommends
            self.dealloc_table_pre(base),
    ;

    /// Precondition for `dealloc_table`.
    pub open spec fn dealloc_table_pre(self, base: SpecPAddr) -> bool {
        &&& self.contains_table(base)
        &&& base != self.root
    }

    /// Specification of `dealloc_table`.
    pub open spec fn dealloc_table_spec(s1: Self, s2: Self, base: SpecPAddr) -> bool {
        &&& s1.dealloc_table_pre(base)
        &&& s2 == s1.dealloc_table(base)
        // `arch` is unchanged
        &&& s2.arch == s1.arch
        // `root` is unchanged
        &&& s2.root == s1.root
        // `base` is removed
        &&& s2.tables == s1.tables.remove(
            base,
        )
        // other tables' contents are preserved
        &&& forall|base2: SpecPAddr| #[trigger]
            s2.tables.contains_key(base2) ==> s1.table_view(base2) == s2.table_view(base2)
    }

    /// Restrict `dealloc_table` using proof fn. It should not be called when we want to reason about
    /// the executable implementation of the `dealloc_table` function.
    pub broadcast proof fn dealloc_table_facts(self, base: SpecPAddr)
        requires
            self.dealloc_table_pre(base),
        ensures
            Self::dealloc_table_spec(self, #[trigger] self.dealloc_table(base), base),
    {
        admit();
    }

    /// Update the entry at the given index in the given table.
    pub uninterp spec fn write(self, base: SpecPAddr, index: nat, entry: u64) -> Self
        recommends
            self.write_pre(base, index),
    ;

    /// Precondition for `write`.
    pub open spec fn write_pre(self, base: SpecPAddr, index: nat) -> bool {
        self.accessible(base, index)
    }

    /// Specification of `write`.
    pub open spec fn write_spec(
        s1: Self,
        s2: Self,
        base: SpecPAddr,
        index: nat,
        entry: u64,
    ) -> bool {
        &&& s1.write_pre(base, index)
        &&& s2 == s1.write(base, index, entry)
        // `arch` is unchanged
        &&& s2.arch == s1.arch
        // `root` is unchanged
        &&& s2.root == s1.root
        // Tables are the same
        &&& s2.tables == s1.tables
        // The entry is updated
        &&& s2.table_view(base) == s1.table_view(base).update(
            index as int,
            entry,
        )
        // Other tables' contents are the same
        &&& forall|base2: SpecPAddr|
            base2 != base && #[trigger] s2.tables.contains_key(base2) ==> s1.table_view(base2)
                == s2.table_view(base2)
    }

    /// Restrict `write` using proof fn. It should not be called when we want to reason about
    /// the executable implementation of the `write` function.
    pub broadcast proof fn write_facts(self, base: SpecPAddr, index: nat, entry: u64)
        requires
            self.write_pre(base, index),
        ensures
            Self::write_spec(self, #[trigger] self.write(base, index, entry), base, index, entry),
    {
        admit();
    }

    /// Lemma. `init` implies well-formedness.
    pub broadcast proof fn lemma_init_implies_wf(self)
        requires
            #[trigger] self.init(),
        ensures
            self.wf(),
    {
        assert(!self.tables.is_empty());
    }

    /// Lemma. `alloc_table` preserves wf.
    pub broadcast proof fn lemma_alloc_table_preserves_wf(
        s1: Self,
        s2: Self,
        level: nat,
        new_base: SpecPAddr,
    )
        requires
            s1.wf(),
            #[trigger] Self::alloc_table_spec(s1, s2, level, new_base),
        ensures
            s2.wf(),
    {
    }

    /// Lemma. `alloc_table` preserves accessibility.
    pub broadcast proof fn lemma_alloc_table_preserves_accessibility(
        s1: Self,
        s2: Self,
        level: nat,
        new_base: SpecPAddr,
        base: SpecPAddr,
        index: nat,
    )
        requires
            s1.wf(),
            #[trigger] Self::alloc_table_spec(s1, s2, level, new_base),
            #[trigger] s1.accessible(base, index),
        ensures
            s2.accessible(base, index),
    {
        Self::lemma_alloc_table_preserves_wf(s1, s2, level, new_base);
    }

    /// Lemma. `dealloc_table` preserves wf.
    pub broadcast proof fn lemma_dealloc_table_preserves_wf(s1: Self, s2: Self, base: SpecPAddr)
        requires
            s1.wf(),
            #[trigger] Self::dealloc_table_spec(s1, s2, base),
        ensures
            s2.wf(),
    {
    }

    /// Lemma. `write` preserves wf.
    pub broadcast proof fn lemma_write_preserves_wf(
        s1: Self,
        s2: Self,
        base: SpecPAddr,
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
    SpecPageTableMem::lemma_init_implies_wf,
    SpecPageTableMem::lemma_alloc_table_preserves_wf,
    SpecPageTableMem::lemma_alloc_table_preserves_accessibility,
    SpecPageTableMem::lemma_dealloc_table_preserves_wf,
    SpecPageTableMem::lemma_write_preserves_wf,
}

/// Concrete page table memory implementation. The type parameter `A` is the backend frame
/// allocator used to allocate/deallocate page tables.
pub struct PageTableMem<A> where A: FrameAllocator {
    /// Page table architecture
    pub arch: PTArch,
    /// Global frame allocator client id
    pub cid: usize,
    /// Root page table address, should be allocated at initialization and never change after that.
    pub root: PAddr,
    /// Phantom data
    pub _phantom: PhantomData<A>,
}

impl<A> PageTableMem<A> where A: FrameAllocator {
    /// Get the abstract view of the page table memory, based on the global frame allocator state.
    pub open spec fn view(&self, allocator: &GlobalFrameAllocator<A>) -> SpecPageTableMem {
        // TODO
        SpecPageTableMem { tables: Map::empty(), arch: self.arch.view(), root: self.root@ }
    }

    /// Invariants that must be implied at initial state and preseved after each operation.
    pub open spec fn invariants(&self, allocator: &GlobalFrameAllocator<A>) -> bool {
        // Invariants of the page table memory.
        &&& self.arch.view().valid()
        // Invariants of the global allocator.
        &&& allocator.invariants()
        // The client is valid.
        &&& allocator.view().clients.contains_key(
            self.cid as nat,
        )
        // The root table is allocated to the client.
        &&& allocator.view().clients[self.cid as nat].contains(Frame4K(self.root).to_nat())
    }

    /// Create a new page table memory.
    pub fn new(allocator: &mut GlobalFrameAllocator<A>, cid: usize, arch: PTArch) -> (res: Self)
        requires
            old(allocator).has_client(cid),
            old(allocator).invariants(),
            old(allocator).view().clients[cid as nat].is_empty(),
            !old(allocator).view().free.is_empty(),
        ensures
            res.view(allocator).init(),
    {
        let root_frame = allocator.alloc(cid);
        // TODO
        assume(false);
        Self { arch, cid, root: root_frame.0, _phantom: PhantomData }
    }

    /// Check if a table is empty.
    pub fn is_table_empty(&self, allocator: &GlobalFrameAllocator<A>, base: PAddr) -> (res: bool)
        requires
            self.invariants(allocator),
            allocator.view().clients.contains_key(self.cid as nat),
            allocator.invariants(),
            allocator.view().clients[self.cid as nat].contains(Frame4K(base).to_nat()),
        ensures
            res == self.view(allocator).is_table_empty(base@),
    {
        // TODO
        assume(false);
        false
    }

    /// Allocate a new table and returns the table base address and size.
    pub fn alloc_table(&self, allocator: &mut GlobalFrameAllocator<A>, level: usize) -> (res: PAddr)
        requires
            self.invariants(old(allocator)),
            old(allocator).view().clients.contains_key(self.cid as nat),
            old(allocator).invariants(),
            !old(allocator).view().free.is_empty(),
        ensures
            SpecPageTableMem::alloc_table_spec(
                self.view(old(allocator)),
                self.view(allocator),
                level as nat,
                res@,
            ),
    {
        let frame = allocator.alloc(self.cid);
        // The client should get a new frame.
        proof {
            assert(allocator.view().clients[self.cid as nat].contains(frame.to_nat()));
            // TODO
            assume(false);
        }
        frame.0
    }

    /// Deallocate a table.
    pub fn dealloc_table(&self, allocator: &mut GlobalFrameAllocator<A>, base: PAddr)
        requires
            self.invariants(old(allocator)),
            old(allocator).view().clients.contains_key(self.cid as nat),
            old(allocator).invariants(),
            old(allocator).view().clients[self.cid as nat].contains(Frame4K(base).to_nat()),
            base != self.root,
        ensures
            SpecPageTableMem::dealloc_table_spec(
                self.view(old(allocator)),
                self.view(allocator),
                base@,
            ),
    {
        // TODO
        assume(false);
        // For simplicity we assume the deallocated table is always empty, so we don't need to zero it.
        allocator.dealloc(self.cid, Frame4K(base));
    }

    /// Get the value at the given index in the given table.
    #[verifier::external_body]
    pub fn read(&self, allocator: &GlobalFrameAllocator<A>, base: PAddr, index: usize) -> (res: u64)
        requires
            self.invariants(allocator),
            self.view(allocator).accessible(base@, index as nat),
        ensures
            #[trigger] self.view(allocator).read(base@, index as nat) == res,
    {
        unsafe { (base.0 as *const u64).offset(index as isize).read_volatile() }
    }

    /// Write the value to the given index in the given table.
    #[verifier::external_body]
    pub fn write(&self, allocator: &GlobalFrameAllocator<A>, base: PAddr, index: usize, value: u64)
        requires
            self.invariants(allocator),
            self.view(allocator).accessible(base@, index as nat),
        ensures
            SpecPageTableMem::write_spec(
                self.view(allocator),
                self.view(allocator),
                base@,
                index as nat,
                value,
            ),
    {
        unsafe { (base.0 as *mut u64).offset(index as isize).write_volatile(value) }
    }

    /// Lemma. Invariants implies well-formedness.
    broadcast proof fn lemma_invariants_implies_wf(&self, allocator: &GlobalFrameAllocator<A>)
        requires
            #[trigger] self.invariants(allocator),
        ensures
            self.view(allocator).wf(),
    {
        // TODO
        assume(false);
    }
}

} // verus!
