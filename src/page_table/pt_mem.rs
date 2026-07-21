//! Abstract page table memory and specification.
//!
//! Page Table Memory is a collection of page tables, and provides read/write, alloc/dealloc functionality.
//! The implementation should refine the specification defined in `spec::memory::PageTableMem`.
use crate::{
    address::addr::{PAddr, SpecPAddr},
    bitmap_allocator::bitmap_trait::BitmapAllocator,
    page_table::{
        pt_arch::{PTArch, SpecPTArch},
        table::*,
    },
};
use core::marker::PhantomData;
use vstd::{prelude::*, simple_pptr::PPtr};

verus! {

use crate::global_allocator::*;

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
        // Contains only one level 0 table.
        &&& forall|base: SpecPAddr| #[trigger]
            self.tables.contains_key(base) && self.tables[base] == 0 ==> base
                == self.root
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
    ///
    /// Design note: this is intentionally uninterpreted. The allocator chooses a
    /// fresh physical base, preserves the existing table map, and initializes the
    /// new table contents; describing that choice directly as executable spec code
    /// is awkward and would duplicate allocator reasoning. The admitted facts below
    /// are the TCB restriction that pins this uninterpreted function to
    /// `alloc_table_spec`.
    pub uninterp spec fn alloc_table(self, level: nat) -> (Self, SpecPAddr)
        recommends
            self.alloc_table_pre(level),
    ;

    /// Precondition for `alloc_table`.
    pub open spec fn alloc_table_pre(self, level: nat) -> bool {
        0 < level < self.arch.level_count()
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
    ///
    /// Design note: this is also intentionally uninterpreted. The admitted fact
    /// below restricts it to `dealloc_table_spec`, which captures the required
    /// effect: remove exactly the non-root table and preserve all other table
    /// contents.
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
    /// Base address of the allocator.
    pub allocator_base: Ghost<SpecPAddr>,
    /// Abstract allocator client that tracks all page-table frames.
    pub client: Tracked<Option<ClientState>>,
    /// Tables in the page table memory (saved as ghost variable).
    pub tables: Ghost<Map<SpecPAddr, nat>>,
    /// Phantom data
    pub _phantom: PhantomData<A>,
}

impl<A> PageTableMem<A> where A: BitmapAllocator {
    pub open spec fn inst_id(&self) -> InstanceId {
        self.client@->Some_0.inst_id()
    }

    pub open spec fn paddr_to_fid_spec(&self, addr: SpecPAddr) -> FrameID {
        (addr.0 - self.allocator_base@.0) as nat / SPEC_FRAME_SIZE
    }

    /// Get the abstract view of the page table memory from the client-owned frames.
    pub open spec fn view(&self) -> SpecPageTableMem
        recommends
            self.client@ is Some,
    {
        SpecPageTableMem {
            tables: self.tables@,
            contents: Map::new(
                |base: SpecPAddr| self.tables@.contains_key(base),
                |base: SpecPAddr|
                    frame4k_to_u64_seq(
                        &self.client@->Some_0.frame_perms[self.paddr_to_fid_spec(base)],
                    ),
            ),
            arch: self.arch@,
            root: self.root@,
        }
    }

    /// Invariants that must be implied at initial state and preseved after each operation.
    pub open spec fn invariants(&self) -> bool {
        // Model invariants
        &&& self.view().wf()
        // Invariants of the page table memory.
        &&& self.arch.view().valid()
        &&& self.client@ is Some
        // The client is valid.
        &&& self.client@->Some_0.wf(
            self.inst_id(),
        )
        // Base address consistent with AllocSpec instance
        &&& self.allocator_base@ == inst_base(self.inst_id())
        &&& self.allocator_base@.aligned(
            SPEC_FRAME_SIZE,
        )
        // The root table is allocated to the client.
        &&& self.client@->Some_0.owns(
            self.paddr_to_fid_spec(self.root@),
        )
        // Tables are in valid address ranges and properly aligned.
        &&& forall|base: SpecPAddr| #[trigger]
            self.tables.contains_key(base) ==> base.0 >= self.allocator_base@.0 && base.aligned(
                SPEC_FRAME_SIZE,
            )
        // Tables are consistent with allocator.
        &&& self.tables.dom().map(|addr: SpecPAddr| self.paddr_to_fid_spec(addr))
            == self.client@->Some_0.owned_frames()
        // TODO: we assume all tables in the hierarchical page table contain 512 8-byte entries, which is true
        // for hvisor's aarch64 implementation. We can make it more general in the future.
        &&& forall|level: nat|
            level < self.arch.view().level_count() ==> self.arch.view().entry_count(level) == 512
    }

    /// Create a new page table memory.
    pub fn new(allocator: &GlobalAllocator<A>, arch: PTArch) -> (res: Self)
        requires
            allocator.invariants(),
            arch@.valid(),
            // TODO: remove this assumption by supporting different page table layouts.
            forall|level: nat| level < arch@.level_count() ==> arch@.entry_count(level) == 512,
        ensures
            res.arch == arch,
            res.inst_id() == allocator.inst_id(),
            res.view().init(),
            res.invariants(),
            allocator.invariants(),
    {
        broadcast use lemma_frame4k_to_u64_seq;

        let Tracked(client) = allocator.register_client();
        let (root, Tracked(client)) = allocator.alloc(Tracked(client));

        let tables = Ghost(Map::empty().insert(root@, 0));
        let ghost fid = allocator.paddr_to_fid_spec(root@);
        let tracked frame_perm: &Frame4KPerm = client.borrow_perm(fid, Ghost(allocator.inst_id()));

        let res = Self {
            arch,
            root,
            allocator_base: Ghost(inst_base(allocator.inst_id())),
            client: Tracked(Some(client)),
            tables,
            _phantom: PhantomData,
        };
        proof {
            assert(res.client@ is Some);
            assert(fid == res.paddr_to_fid_spec(root@));
            assert(res.tables@.dom() == Set::empty().insert(root@));
            assert(res.client@->Some_0.owned_frames() =~= Set::empty().insert(fid));
            assert(res.view().contents.dom() == Set::empty().insert(root@));
            assert(frame_is_empty(frame_perm));
            assert(res.view().contents[res.root@] == Seq::new(arch@.entry_count(0), |_i| 0u64));
            assert(res.view().contents == Map::empty().insert(
                res.root@,
                Seq::new(arch@.entry_count(0), |_i| 0u64),
            ));
            SpecPageTableMem::lemma_init_implies_wf(res.view());
            assert(res.client@->Some_0.wf(res.inst_id()));
            assert(res.allocator_base@.aligned(SPEC_FRAME_SIZE));
            assert(res.client@->Some_0.owns(res.paddr_to_fid_spec(res.root@)));
            assert(res.tables@.dom().map(|addr: SpecPAddr| res.paddr_to_fid_spec(addr))
                == res.client@->Some_0.owned_frames());
            assert(res.invariants());
        }
        res
    }

    /// Allocate a new table and returns the table base address and size.
    pub fn alloc_table(&mut self, allocator: &GlobalAllocator<A>, level: usize) -> (res: PAddr)
        requires
            allocator.invariants(),
            old(self).invariants(),
            old(self).inst_id() == allocator.inst_id(),
            0 < level < old(self).arch.view().level_count(),
        ensures
            SpecPageTableMem::alloc_table_spec(old(self).view(), self.view(), level as nat, res@),
            self.inst_id() == old(self).inst_id(),
            allocator.invariants(),
            self.invariants(),
    {
        broadcast use lemma_frame4k_to_u64_seq;

        let tracked client = self.client.tracked_take();
        // Alloc a new frame
        let (new_base, Tracked(client)) = allocator.alloc(Tracked(client));
        assert(new_base@.aligned(self.arch.view().table_size(level as nat)));

        let ghost fid = self.paddr_to_fid_spec(new_base@);
        let tracked frame_perm: &Frame4KPerm = client.frame_perms.tracked_borrow(fid);
        self.client = Tracked(Some(client));
        self.tables = Ghost(self.tables@.insert(new_base@, level as nat));

        proof {
            let s1: SpecPageTableMem = old(self).view();
            let s2: SpecPageTableMem = self.view();

            // Old client doesn't have the new table
            assert(!old(self).client@->Some_0.owned_frames().contains(fid));
            assert(!s1.contains_table(new_base@)) by {
                if s1.contains_table(new_base@) {
                    assert(old(self).tables@.dom().contains(new_base@));
                    assert(old(self).tables@.dom().map(
                        |addr: SpecPAddr| old(self).paddr_to_fid_spec(addr),
                    ).contains(fid));
                }
            }
            // New table doesn't overlap with existing tables
            assert forall|base: SpecPAddr| #[trigger]
                s1.tables.contains_key(base) implies !SpecPAddr::overlap(
                new_base@,
                s1.arch.table_size(level as nat),
                base,
                s1.arch.table_size(s1.level(base)),
            ) by {
                let fid2 = old(self).paddr_to_fid_spec(base);
                assert(old(self).client@->Some_0.owned_frames().contains(fid2));
                assert(fid2 != fid);
                assert(base != new_base@);
            }
            // New table is added
            assert(s2.tables == s1.tables.insert(new_base@, level as nat));
            // New table is empty
            assert(frame_is_empty(frame_perm));
            assert(s2.contents[new_base@] == Seq::new(
                s2.arch.entry_count(level as nat),
                |_i| 0u64,
            ));

            // Old tables are unchanged
            assert forall|base2| #[trigger]
                s1.contents.contains_key(base2) implies s2.contents[base2]
                == s1.contents[base2] by {
                let fid2 = old(self).paddr_to_fid_spec(base2);
                assert(old(self).tables@.dom().contains(base2));
                assert(old(self).tables@.dom().map(
                    |addr: SpecPAddr| old(self).paddr_to_fid_spec(addr),
                ).contains(fid2));
                assert(old(self).client@->Some_0.owns(fid2));
                assert(self.client@->Some_0.frame_perms[fid2] == old(
                    self,
                ).client@->Some_0.frame_perms[fid2]);
                assert(s1.contents[base2] == s2.contents[base2]);
            }
            // Only the content of new table is updated
            assert(s2.contents == s1.contents.insert(
                new_base@,
                Seq::new(s2.arch.entry_count(level as nat), |_i| 0u64),
            ));
            // Consistent with model spec
            assert(SpecPageTableMem::alloc_table_spec(s1, s2, level as nat, new_base@));

            // Invariants preserved
            SpecPageTableMem::lemma_alloc_table_preserves_wf(s1, s2, level as nat, new_base@);
            old(self).tables@.dom().lemma_set_map_insert_commute(
                new_base@,
                |addr: SpecPAddr| self.paddr_to_fid_spec(addr),
            );
            assert(self.tables@.dom().map(|addr: SpecPAddr| self.paddr_to_fid_spec(addr))
                == self.client@->Some_0.owned_frames());
            assert(self.invariants());
        }
        new_base
    }

    /// Deallocate a table.
    pub fn dealloc_table(&mut self, allocator: &GlobalAllocator<A>, base: PAddr)
        requires
            allocator.invariants(),
            old(self).invariants(),
            old(self).inst_id() == allocator.inst_id(),
            old(self).tables@.contains_key(base@),
            base != old(self).root,
        ensures
            SpecPageTableMem::dealloc_table_spec(old(self).view(), self.view(), base@),
            self.inst_id() == old(self).inst_id(),
            allocator.invariants(),
            self.invariants(),
    {
        broadcast use BitmapAllocator::lemma_view_len_is_cap;

        let ghost fid = self.paddr_to_fid_spec(base@);
        // Clear the table contents before returning the frame to the free pool.
        let tracked mut client = self.client.tracked_take();
        assert(client.frame_perms.contains_key(fid));
        let tracked frame_perm: Frame4KPerm = client.frame_perms.tracked_remove(fid);

        // Convert the permission to table permission
        let tracked table_perm: Table512Perm = frame4k_perm_to_table512_perm(frame_perm);
        assert(table_perm.addr() == base.0);
        assert(table_perm.is_init());

        // Use PPtr to clear the table contents before deallocating the frame
        let pptr = PPtr::<Table512>::from_addr(base.0);
        let mut table = pptr.read(Tracked(&table_perm));
        table.clear();
        pptr.write(Tracked(&mut table_perm), table);

        let tracked frame_perm: Frame4KPerm = table512_perm_to_frame4k_perm(table_perm);
        proof {
            // Put the frame permission back
            client.frame_perms.tracked_insert(fid, frame_perm);

            // The deallocated table is emptied
            lemma_frame4k_to_u64_seq(&frame_perm);
            assert(frame4k_to_u64_seq(&frame_perm) == table_perm.mem_contents().value()@);
            assert(table_perm.mem_contents().value().spec_is_empty());
            assert forall|i: int| 0 <= i < 512 implies frame4k_to_u64_seq(&frame_perm)[i]
                == 0u64 by {
                assert(table_perm.mem_contents().value()@[i] == 0u64);
            }
            assert(frame_is_empty(&frame_perm));

            // Other tables are unchanged
            assert forall|fid2| #[trigger]
                old(self).client@->Some_0.frame_perms.contains_key(fid2) && fid2
                    != fid implies client.frame_perms[fid2] == old(
                self,
            ).client@->Some_0.frame_perms[fid2] by {
                assert(old(self).client@->Some_0.frame_perms.contains_key(fid2));
            }
        }

        // Dealloc the frame
        let Tracked(client) = allocator.dealloc(Tracked(client), base);
        self.client = Tracked(Some(client));
        self.tables = Ghost(self.tables@.remove(base@));

        proof {
            let s1: SpecPageTableMem = old(self).view();
            let s2: SpecPageTableMem = self.view();

            assert(s2.tables == s1.tables.remove(base@));
            // Other tables are unchanged
            assert forall|base2: SpecPAddr| #[trigger]
                s2.tables.contains_key(base2) implies s1.contents[base2] == s2.contents[base2] by {
                assert(base2 != base@);
                let fid2 = old(self).paddr_to_fid_spec(base2);
                assert(s1.tables.contains_key(base2));
                assert(old(self).tables@.dom().contains(base2));
                assert(old(self).tables@.dom().map(
                    |addr: SpecPAddr| old(self).paddr_to_fid_spec(addr),
                ).contains(fid2));
                assert(old(self).client@->Some_0.owns(fid2));
                assert(self.client@->Some_0.frame_perms[fid2] == old(
                    self,
                ).client@->Some_0.frame_perms[fid2]);
            }
            assert(s2.contents == s1.contents.remove(base@));
            // Consistent with model spec
            assert(SpecPageTableMem::dealloc_table_spec(s1, s2, base@));

            // Invariants preserved
            SpecPageTableMem::lemma_dealloc_table_preserves_wf(s1, s2, base@);
            assert(self.tables@.dom().map(|addr: SpecPAddr| self.paddr_to_fid_spec(addr))
                == self.client@->Some_0.owned_frames());
            assert(self.invariants());
        }
    }

    /// Deallocate the root table when destroying this page-table memory.
    ///
    /// This operation consumes `self` because removing the root invalidates the
    /// page-table memory invariants. Higher layers only call it after proving the
    /// page table has no mappings.
    pub fn dealloc_root(self, allocator: &GlobalAllocator<A>)
        requires
            allocator.invariants(),
            self.invariants(),
            self.inst_id() == allocator.inst_id(),
        ensures
            allocator.invariants(),
    {
        broadcast use BitmapAllocator::lemma_view_len_is_cap;

        let mut this = self;
        let root = this.root;
        let ghost fid = this.paddr_to_fid_spec(root@);
        let tracked mut client = this.client.tracked_take();
        assert(client.frame_perms.contains_key(fid));
        let tracked frame_perm: Frame4KPerm = client.frame_perms.tracked_remove(fid);

        let tracked table_perm: Table512Perm = frame4k_perm_to_table512_perm(frame_perm);
        assert(table_perm.addr() == root.0);
        assert(table_perm.is_init());

        let pptr = PPtr::<Table512>::from_addr(root.0);
        let mut table = pptr.read(Tracked(&table_perm));
        table.clear();
        pptr.write(Tracked(&mut table_perm), table);

        let tracked frame_perm: Frame4KPerm = table512_perm_to_frame4k_perm(table_perm);
        proof {
            client.frame_perms.tracked_insert(fid, frame_perm);
            lemma_frame4k_to_u64_seq(&frame_perm);
            assert(frame4k_to_u64_seq(&frame_perm) == table_perm.mem_contents().value()@);
            assert(table_perm.mem_contents().value().spec_is_empty());
            assert forall|i: int| 0 <= i < 512 implies frame4k_to_u64_seq(&frame_perm)[i]
                == 0u64 by {
                assert(table_perm.mem_contents().value()@[i] == 0u64);
            }
            assert(frame_is_empty(&frame_perm));
        }

        let Tracked(_client) = allocator.dealloc(Tracked(client), root);
    }

    /// Get the value at the given index in the given table.
    pub fn read(&self, base: PAddr, index: usize) -> (res: u64)
        requires
            self.invariants(),
            self.view().accessible(base@, index as nat),
        ensures
            #[trigger] self.view().read(base@, index as nat) == res,
    {
        let ghost fid = self.paddr_to_fid_spec(base@);
        assert(self.client->Some_0.owns(fid));
        // Borrow the frame permission
        let tracked frame_perm: &Frame4KPerm =
            self.client.tracked_borrow().frame_perms.tracked_borrow(fid);
        assert(frame_perm.addr() == base.0);
        assert(frame_perm.is_init());

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
    pub fn write(&mut self, base: PAddr, index: usize, value: u64)
        requires
            old(self).invariants(),
            old(self).view().accessible(base@, index as nat),
        ensures
            self.view() == old(self).view().write(base@, index as nat, value),
            self.inst_id() == old(self).inst_id(),
            self.invariants(),
    {
        let ghost fid = self.paddr_to_fid_spec(base@);
        // Take the client to get the permission for the frame
        let tracked mut client = self.client.tracked_take();
        assert(client.frame_perms.contains_key(fid));
        let tracked frame_perm: Frame4KPerm = client.frame_perms.tracked_remove(fid);

        // Convert the permission to table permission
        let tracked table_perm: Table512Perm = frame4k_perm_to_table512_perm(frame_perm);
        assert(table_perm.addr() == base.0);
        assert(table_perm.is_init());

        // Use PPtr to write the entry
        let pptr = PPtr::<Table512>::from_addr(base.0);
        let mut table = pptr.read(Tracked(&table_perm));
        table.set(index, value);
        pptr.write(Tracked(&mut table_perm), table);

        let tracked frame_perm: Frame4KPerm = table512_perm_to_frame4k_perm(table_perm);
        proof {
            // Put the frame permission back
            client.frame_perms.tracked_insert(fid, frame_perm);
        }
        self.client = Tracked(Some(client));
        proof {
            assert(self.view().contents == old(self).view().contents.insert(
                base@,
                frame4k_to_u64_seq(&frame_perm),
            ));
            // Invariants preserved
            assert(self.tables@.dom().map(|addr: SpecPAddr| self.paddr_to_fid_spec(addr))
                == self.client@->Some_0.owned_frames());
            assert(self.invariants());
        }
    }
}

} // verus!
