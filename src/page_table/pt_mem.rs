//! Abstract page table memory and specification.
//!
//! Page Table Memory is a collection of page tables, and provides read/write, alloc/dealloc functionality.
//! The implementation should refine the specification defined in `spec::memory::PageTableMem`.
use std::{borrow::Borrow, marker::PhantomData};
use vstd::{
    prelude::*,
    simple_pptr::{PPtr, PointsTo},
};

use crate::{
    address::{
        addr::{PAddr, SpecPAddr, SpecVAddr, VAddr},
        frame::FrameSize,
    },
    bitmap_allocator::bitmap_trait::BitmapAllocator,
    global_allocator::{self, ClientID, Frame4KPerm, GlobalAllocator, GlobalAllocatorModel},
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
    /// Table Contents
    pub contents: Map<SpecPAddr, Seq<u64>>,
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
        // Table dom is consistent with contents dom.
        &&& self.contents.dom()
            == self.tables.dom()
        // Table contents have the right length.
        &&& forall|base: SpecPAddr| #[trigger]
            self.tables.contains_key(base) ==> self.contents[base].len() == self.arch.entry_count(
                self.tables[base],
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
        &&& self.tables == Map::empty().insert(self.root, 0nat)
        &&& self.contents == Map::empty().insert(
            self.root,
            Seq::new(self.arch.entry_count(0), |_i| 0u64),
        )
        // Root table is aligned
        &&& self.root.aligned(
            self.arch.table_size(0),
        )
        // Root table is empty
        &&& self.contents[self.root] == Seq::new(self.arch.entry_count(0), |_i| 0u64)
    }

    /// If a table is empty.
    pub open spec fn is_table_empty(self, base: SpecPAddr) -> bool
        recommends
            self.contains_table(base),
    {
        self.contents[base] == Seq::new(self.contents[base].len(), |_i| 0u64)
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
        self.contents[base][index as int]
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
        // TODO: assume smallest page size is 4096
        &&& new_base.aligned(4096)
        &&& new_base.0
            < usize::MAX
        // new table doesn't overlap with existing tables
        &&& forall|base: SpecPAddr| #[trigger]
            s1.tables.contains_key(base) ==> !SpecPAddr::overlap(
                new_base,
                s1.arch.table_size(level),
                base,
                s1.arch.table_size(s1.level(base)),
            )
            // new table is empty
        &&& s2.contents == s1.contents.insert(
            new_base,
            Seq::new(s2.arch.entry_count(level), |_i| 0u64),
        )
        // new table is added
        &&& s2.tables == s1.tables.insert(new_base, level)
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

    /// Restrict `alloc_table` in the reverse direction.
    pub broadcast proof fn alloc_table_facts_rev(
        s1: Self,
        s2: Self,
        level: nat,
        new_base: SpecPAddr,
    )
        requires
            s1.alloc_table_pre(level),
            #[trigger] Self::alloc_table_spec(s1, s2, level, new_base),
        ensures
            (s2, new_base) == s1.alloc_table(level),
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
        // `arch` is unchanged
        &&& s2.arch == s1.arch
        // `root` is unchanged
        &&& s2.root == s1.root
        // `base` is removed
        &&& s2.tables == s1.tables.remove(base)
        &&& s2.contents == s1.contents.remove(
            base,
        )
        // other tables' contents are preserved
        &&& forall|base2: SpecPAddr| #[trigger]
            s2.tables.contains_key(base2) ==> s1.contents[base2] == s2.contents[base2]
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
    pub open spec fn write(self, base: SpecPAddr, index: nat, entry: u64) -> Self
        recommends
            self.accessible(base, index),
    {
        Self {
            contents: self.contents.insert(base, self.contents[base].update(index as int, entry)),
            ..self
        }
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

    /// Lemma. `dealloc_table` preserves accessibility.
    pub broadcast proof fn lemma_dealloc_table_preserves_accessibility(
        s1: Self,
        s2: Self,
        base: SpecPAddr,
        base2: SpecPAddr,
        index: nat,
    )
        requires
            s1.wf(),
            #[trigger] Self::dealloc_table_spec(s1, s2, base),
            #[trigger] s1.accessible(base2, index),
            base != base2,
        ensures
            s2.accessible(base2, index),
    {
        Self::lemma_dealloc_table_preserves_wf(s1, s2, base);
    }

    /// Lemma. `write` preserves wf.
    pub broadcast proof fn lemma_write_preserves_wf(self, base: SpecPAddr, index: nat, entry: u64)
        requires
            self.wf(),
            self.accessible(base, index),
        ensures
            #[trigger] self.write(base, index, entry).wf(),
    {
        let s2 = self.write(base, index, entry);
        assert(s2.contents.dom() == self.contents.dom());
    }

    /// Lemma. Facts about `write`.
    pub broadcast proof fn lemma_write_facts(
        s1: Self,
        s2: Self,
        base: SpecPAddr,
        index: nat,
        entry: u64,
    )
        requires
            s1.wf(),
            s1.accessible(base, index),
            s2 == #[trigger] s1.write(base, index, entry),
        ensures
            #[trigger] s2.contents[base] == s1.contents[base].update(index as int, entry),
            forall|base2: SpecPAddr|
                base2 != base && #[trigger] s1.tables.contains_key(base2) ==> s2.contents[base2]
                    == s1.contents[base2],
    {
    }
}

/// Broadcast page table memory related lemmas.
pub broadcast group group_pt_mem_lemmas {
    SpecPageTableMem::alloc_table_facts,
    SpecPageTableMem::alloc_table_facts_rev,
    SpecPageTableMem::dealloc_table_facts,
    SpecPageTableMem::lemma_init_implies_wf,
    SpecPageTableMem::lemma_alloc_table_preserves_wf,
    SpecPageTableMem::lemma_alloc_table_preserves_accessibility,
    SpecPageTableMem::lemma_dealloc_table_preserves_wf,
    SpecPageTableMem::lemma_dealloc_table_preserves_accessibility,
    SpecPageTableMem::lemma_write_preserves_wf,
    SpecPageTableMem::lemma_write_facts,
}

/// Concrete page table memory implementation. The type parameter `A` is the backend frame
/// allocator used to allocate/deallocate page tables.
pub struct PageTableMem<A> where A: BitmapAllocator {
    /// Page table architecture
    pub arch: PTArch,
    /// Root page table address, should be allocated at initialization and never change after that.
    pub root: PAddr,
    /// Global frame allocator client id
    pub cid: Tracked<ClientID>,
    /// Tables in the page table memory (saved as ghost variable).
    pub tables: Ghost<Map<SpecPAddr, nat>>,
    /// Phantom data
    pub _phantom: PhantomData<A>,
}

impl<A> PageTableMem<A> where A: BitmapAllocator {
    /// Get the abstract view of the page table memory, based on the global frame allocator state.
    pub open spec fn view(&self, allocator: &GlobalAllocatorModel) -> SpecPageTableMem {
        SpecPageTableMem {
            tables: self.tables@,
            contents: Map::new(
                |base: SpecPAddr| self.tables@.contains_key(base),
                |base: SpecPAddr|
                    frame4k_to_u64_seq(&allocator.clients[self.cid@][allocator.paddr_to_fid(base)]),
            ),
            arch: self.arch@,
            root: self.root@,
        }
    }

    /// Invariants that must be implied at initial state and preseved after each operation.
    pub open spec fn invariants(&self, allocator: &GlobalAllocatorModel) -> bool {
        // Model invariants
        &&& self.view(
            allocator,
        ).wf()
        // Invariants of the page table memory.
        &&& self.arch.view().valid()
        // The client is valid.
        &&& allocator.clients.contains_key(
            self.cid@,
        )
        // The root table is allocated to the client.
        &&& allocator.clients[self.cid@].contains_key(
            allocator.paddr_to_fid(self.root@),
        )
        // Tables are in valid address ranges and properly aligned.
        &&& forall|base: SpecPAddr| #[trigger]
            self.tables.contains_key(base) ==> base.0 >= allocator.base.0 && base.aligned(
                GlobalAllocator::<A>::FRAME_SIZE as nat,
            )
        // Tables are consistent with allocator.
        &&& self.tables.dom().map(|addr: SpecPAddr| allocator.paddr_to_fid(addr))
            == allocator.clients[self.cid@].dom()
        // TODO: we assume all tables in the hierarchical page table contain 512 8-byte entries, which is true
        // for hvisor's aarch64 implementation. We can make it more general in the future.
        &&& forall|level: nat|
            level < self.arch.view().level_count() ==> self.arch.view().entry_count(level) == 512
        &&& GlobalAllocator::<A>::FRAME_SIZE == 4096
    }

    /// Create a new page table memory.
    pub fn new(allocator: &mut GlobalAllocator<A>, arch: PTArch) -> (res: Self)
        requires
            old(allocator).invariants(),
            !old(allocator).view().free.is_empty(),
            arch@.valid(),
            // TODO: remove this assumption by supporting different page table layouts.
            forall|level: nat| level < arch@.level_count() ==> arch@.entry_count(level) == 512,
            GlobalAllocator::<A>::FRAME_SIZE == 4096,
        ensures
            res.arch == arch,
            res.view(&allocator.state).init(),
            res.invariants(&allocator.state),
            allocator.invariants(),
    {
        broadcast use lemma_frame4k_to_u64_seq_eq;

        let tracked cid = allocator.state.tracked_add_client();
        proof {
            GlobalAllocator::lemma_add_client_preserves_invariants(
                *old(allocator),
                *allocator,
                cid,
            );
            assert(allocator.invariants());
        }
        let root = allocator.alloc(Tracked(&cid));
        let tables = Ghost(Map::empty().insert(root@, 0));
        let res = Self { arch, cid: Tracked(cid), root, tables, _phantom: PhantomData };
        proof {
            // Prove invariants
            assert(res.tables.view().dom() == Set::empty().insert(root@));
            Set::empty().lemma_set_map_insert_commute(
                root@,
                |addr: SpecPAddr| allocator@.paddr_to_fid(addr),
            );
            assert(res.tables.view().dom().map(|addr: SpecPAddr| allocator@.paddr_to_fid(addr))
                == Set::empty().insert(allocator@.paddr_to_fid(root@)));
            assert(res.tables.view().dom().map(
                |addr: SpecPAddr| allocator.state@.paddr_to_fid(addr),
            ) == allocator.state@.clients[cid].dom());
            assert(res.view(&allocator.state).contents.dom() == Set::empty().insert(root@));
            assert(res.view(&allocator.state).wf());

            assert(res.invariants(&allocator.state));

            // Prove `init`
            // Assume true, not verifiable yet
            assume(res.view(&allocator.state).contents[res.root@] == Seq::new(
                arch@.entry_count(0),
                |_i| 0u64,
            ));
            assert(res.view(&allocator.state).contents == Map::empty().insert(
                res.root@,
                Seq::new(arch@.entry_count(0), |_i| 0u64),
            ));
        }
        res
    }

    /// Allocate a new table and returns the table base address and size.
    pub fn alloc_table(&mut self, allocator: &mut GlobalAllocator<A>, level: usize) -> (res: PAddr)
        requires
            old(allocator).invariants(),
            old(self).invariants(&old(allocator).state),
            !old(allocator).view().free.is_empty(),
            level < old(self).arch.view().level_count(),
        ensures
            SpecPageTableMem::alloc_table_spec(
                old(self).view(&old(allocator).state),
                self.view(&allocator.state),
                level as nat,
                res@,
            ),
            allocator.invariants(),
            self.invariants(&allocator.state),
    {
        let new_base = allocator.alloc(Tracked(self.cid.borrow()));
        self.tables = Ghost(self.tables@.insert(new_base@, level as nat));

        proof {
            let a1 = old(allocator).view();
            let a2 = allocator.view();
            let cid = self.cid@;
            let fid = allocator@.paddr_to_fid(new_base@);
            assert(GlobalAllocatorModel::alloc(a1, a2, cid, fid));

            let s1: SpecPageTableMem = old(self).view(&old(allocator).state);
            let s2: SpecPageTableMem = self.view(&allocator.state);

            assert(new_base@.aligned(self.arch.view().table_size(level as nat)));
            // new table doesn't overlap with existing tables
            assert forall|base: SpecPAddr| #[trigger]
                s1.tables.contains_key(base) implies !SpecPAddr::overlap(
                new_base@,
                s1.arch.table_size(level as nat),
                base,
                s1.arch.table_size(s1.level(base)),
            ) by {
                let fid2 = allocator@.paddr_to_fid(base);
                assert(old(allocator).view().clients[cid].contains_key(fid2));
                assert(base != new_base@);
            }
            // new table is added
            assert(s2.tables == s1.tables.insert(new_base@, level as nat));

            // Assume: new table is empty
            assume(s2.contents[new_base@] == Seq::new(
                s2.arch.entry_count(level as nat),
                |_i| 0u64,
            ));
            assert(s2.contents == s1.contents.insert(
                new_base@,
                Seq::new(s2.arch.entry_count(level as nat), |_i| 0u64),
            ));
            // Consistent with model spec
            assert(SpecPageTableMem::alloc_table_spec(s1, s2, level as nat, new_base@));

            // Invariants preserved
            SpecPageTableMem::lemma_alloc_table_preserves_wf(s1, s2, level as nat, new_base@);
            old(self).tables.view().dom().lemma_set_map_insert_commute(
                new_base@,
                |addr: SpecPAddr| allocator@.paddr_to_fid(addr),
            );
            assert(self.tables.view().dom().map(|addr: SpecPAddr| allocator@.paddr_to_fid(addr))
                == allocator.state@.clients[cid].dom());
            assert(self.invariants(&allocator.state));
        }
        new_base
    }

    /// Deallocate a table.
    pub fn dealloc_table(&mut self, allocator: &mut GlobalAllocator<A>, base: PAddr)
        requires
            old(allocator).invariants(),
            old(self).invariants(&old(allocator).state),
            old(self).tables@.contains_key(base@),
            base != old(self).root,
        ensures
            SpecPageTableMem::dealloc_table_spec(
                old(self).view(&old(allocator).state),
                self.view(&allocator.state),
                base@,
            ),
            allocator.invariants(),
            self.invariants(&allocator.state),
    {
        // For simplicity we assume the deallocated table is always empty, so we don't zero it.
        allocator.dealloc(Tracked(self.cid.borrow()), base);
        self.tables = Ghost(self.tables@.remove(base@));

        proof {
            let cid = self.cid@;
            let s1: SpecPageTableMem = old(self).view(&old(allocator).state);
            let s2: SpecPageTableMem = self.view(&allocator.state);

            assert(s2.tables == s1.tables.remove(base@));
            assert(s2.contents == s1.contents.remove(base@));
            // Consistent with model spec
            assert(SpecPageTableMem::dealloc_table_spec(s1, s2, base@));

            // Invariants preserved
            SpecPageTableMem::lemma_dealloc_table_preserves_wf(s1, s2, base@);
            assert(self.tables.view().dom().map(|addr: SpecPAddr| allocator@.paddr_to_fid(addr))
                == allocator.state@.clients[cid].dom());
            assert(self.invariants(&allocator.state));
        }
    }

    /// Get the value at the given index in the given table.
    pub fn read(
        &self,
        Tracked(allocator): Tracked<&GlobalAllocatorModel>,
        base: PAddr,
        index: usize,
    ) -> (res: u64)
        requires
            self.invariants(allocator),
            self.view(allocator).accessible(base@, index as nat),
            allocator.wf(),
        ensures
            #[trigger] self.view(allocator).read(base@, index as nat) == res,
    {
        let ghost cid = self.cid@;
        let ghost fid = allocator.paddr_to_fid(base@);
        // Borrow permission from the allocator
        let tracked frame_perm: &Frame4KPerm = allocator.clients.tracked_borrow(cid).tracked_borrow(
            fid,
        );
        assert(allocator.clients.contains_key(cid) && allocator.clients[cid].contains_key(fid));
        assert(frame_perm.addr() == base.0);

        // Convert the permission to table permission
        let tracked table_perm: &Table512Perm = frame4k_perm_ref_to_table512_perm_ref(frame_perm);
        assert(table_perm.addr() == base.0);
        assert(table_perm.is_init());

        // Use PPtr to read the entry
        let pptr = PPtr::<Table512>::from_addr(base.0);
        let table = pptr.read(Tracked(table_perm));
        table.index(index)
    }

    /// Write the value to the given index in the given table.
    pub fn write(
        &mut self,
        Tracked(allocator): Tracked<&mut GlobalAllocatorModel>,
        base: PAddr,
        index: usize,
        value: u64,
    )
        requires
            old(self).invariants(old(allocator)),
            old(self).view(old(allocator)).accessible(base@, index as nat),
            old(allocator).wf(),
        ensures
            self.view(allocator) == old(self).view(old(allocator)).write(
                base@,
                index as nat,
                value,
            ),
            self.invariants(allocator),
            allocator.wf(),
    {
        let ghost cid = self.cid@;
        let ghost fid = allocator.paddr_to_fid(base@);
        assert(allocator.clients.contains_key(cid));

        // Take permission from the allocator
        let tracked mut client = allocator.clients.tracked_remove(cid);
        assert(client.contains_key(fid));
        let tracked frame_perm: Frame4KPerm = client.tracked_remove(fid);

        // Convert the permission to table permission
        let tracked table_perm: Table512Perm = frame4k_perm_to_table512_perm(frame_perm);

        // Use PPtr to write the entry
        let pptr = PPtr::<Table512>::from_addr(base.0);
        let mut table = pptr.read(Tracked(&table_perm));
        table.set(index, value);
        pptr.write(Tracked(&mut table_perm), table);

        let tracked frame_perm: Frame4KPerm = table512_perm_to_frame4k_perm(table_perm);
        proof {
            // Restore the permission to the allocator
            client.tracked_insert(fid, frame_perm);
            allocator.clients.tracked_insert(self.cid@, client);
            assert(self.tables.view().dom().map(|addr: SpecPAddr| allocator.paddr_to_fid(addr))
                == allocator.clients[cid].dom());
            assert(self.view(allocator).contents == self.view(old(allocator)).contents.insert(
                base@,
                frame4k_to_u64_seq(&frame_perm),
            ));
        }
    }
}

/// A single page table, which contains a fixed number of `u64` entries. The type parameter `N` is the
/// number of entries in the table.
#[derive(Clone, Copy)]
pub struct Table<const N: usize> {
    pub entries: [u64; N],
}

impl<const N: usize> Table<N> {
    pub open spec fn view(&self) -> Seq<u64> {
        self.entries.view()
    }

    pub open spec fn spec_index(&self, index: usize) -> u64
        recommends
            0 <= index < N,
    {
        self.view()[index as int]
    }

    pub open spec fn spec_is_empty(&self) -> bool {
        forall|x: usize| 0 <= x < N ==> self.spec_index(x) == 0
    }

    pub fn init(&mut self)
        ensures
            forall|i: usize| 0 <= i < N ==> self.spec_index(i) == 0,
    {
        for i in 0..N
            invariant
                0 <= i <= N,
                forall|j: usize| 0 <= j < i ==> self.spec_index(j) == 0,
        {
            let ghost old_self = *self;
            self.entries[i] = 0;
            assert forall|j: usize| 0 <= j < i implies self.spec_index(j) == 0 by {
                assert(self.spec_index(j) == old_self.spec_index(j));
            }
        }
    }

    pub fn index(&self, index: usize) -> (res: u64)
        requires
            0 <= index < N,
        ensures
            res == self.spec_index(index),
    {
        self.entries[index]
    }

    pub fn set(&mut self, index: usize, value: u64)
        requires
            0 <= index < N,
        ensures
            self@ == old(self)@.update(index as int, value),
    {
        self.entries[index] = value;
    }
}

/// A 4K byte page table with 512 entries.
pub type Table512 = Table<512>;

/// Permission for a 4K byte page table, which points to a `Table512`.
pub type Table512Perm = PointsTo<Table512>;

/// Convert a `Frame4KPerm` referenceto a `Table512Perm` reference. Assume safety.
#[verifier::external_body]
proof fn frame4k_perm_ref_to_table512_perm_ref(
    tracked frame_perm: &Frame4KPerm,
) -> (tracked table_perm: &Table512Perm)
    ensures
        table_perm.addr() == frame_perm.addr(),
        table_perm.is_init() == frame_perm.is_init(),
        table_perm.mem_contents().value()@ == frame4k_to_u64_seq(frame_perm),
{
    let tracked table_perm: Tracked<&Table512Perm> = Tracked::assume_new();
    table_perm@
}

/// Convert a `Table512Perm` to a `Frame4KPerm`. Assume safety.
#[verifier::external_body]
proof fn frame4k_perm_to_table512_perm(tracked frame_perm: Frame4KPerm) -> (tracked table_perm:
    Table512Perm)
    ensures
        table_perm.addr() == frame_perm.addr(),
        table_perm.is_init() == frame_perm.is_init(),
        table_perm.mem_contents().value()@ == frame4k_to_u64_seq(&frame_perm),
{
    let tracked table_perm: Tracked<Table512Perm> = Tracked::assume_new();
    table_perm@
}

/// Convert a `Table512Perm` to a `Frame4KPerm`. Assume safety.
#[verifier::external_body]
proof fn table512_perm_to_frame4k_perm(tracked table_perm: Table512Perm) -> (tracked frame_perm:
    Frame4KPerm)
    ensures
        frame_perm.addr() == table_perm.addr(),
        frame_perm.is_init() == table_perm.is_init(),
        frame4k_to_u64_seq(&frame_perm) == table_perm.mem_contents().value()@,
{
    let tracked frame_perm: Tracked<Frame4KPerm> = Tracked::assume_new();
    frame_perm@
}

/// Interpret the contents of a `Frame4KPerm` as a sequence of `u64` entries.
pub uninterp spec fn frame4k_to_u64_seq(perm: &Frame4KPerm) -> Seq<u64>;

broadcast proof fn lemma_frame4k_to_u64_seq_eq(perm: &Frame4KPerm)
    ensures
        #[trigger] frame4k_to_u64_seq(perm).len() == 512,
{
    admit();
}

} // verus!
