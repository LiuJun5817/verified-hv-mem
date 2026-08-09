//! Abstract page table memory and specification.
//!
//! Page Table Memory is a collection of page tables, and provides read/write, alloc/dealloc functionality.
//!
//! Address-space convention:
//! - All addresses in `SpecPageTableMem`, including table-map keys and `root`, are physical
//!   addresses (PA). All table addresses accepted from or returned to `PageTable` are also PA.
//! - The global allocator returns hypervisor virtual addresses (HVA). Frame permissions and
//!   `PPtr` accesses are indexed by those HVA values.
//! - `PageTableMem` alone translates between PA and HVA using `hva_to_pa_offset`; the abstract
//!   model and `PageTable` therefore remain PA-only.
//! The implementation should refine the specification defined in `spec::memory::PageTableMem`.
use crate::{
    address::addr::{PAddr, SpecPAddr},
    bitmap_allocator::bitmap_trait::BitmapAllocator,
    constants::*,
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
    /// All tables in the hierarchy, keyed by the physical base address (PA) of each table.
    /// The value is the table level.
    pub tables: Map<SpecPAddr, nat>,
    /// Table contents, keyed by the same physical table bases (PA) as `tables`.
    pub contents: Map<SpecPAddr, Seq<u64>>,
    /// Page table architecture.
    pub arch: SpecPTArch,
    /// Physical address (PA) of the root table.
    pub root: SpecPAddr,
}

impl SpecPageTableMem {
    /// Get the level of the table at physical base address `base` (PA).
    pub open spec fn level(self, base: SpecPAddr) -> nat
        recommends
            self.contains_table(base),
    {
        self.tables[base]
    }

    /// Whether a table exists at physical base address `base` (PA).
    pub open spec fn contains_table(self, base: SpecPAddr) -> bool {
        self.tables.contains_key(base)
    }

    /// Whether a table with `level` exists at physical base address `base` (PA).
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
            self.tables.contains_key(base) ==> base.aligned(self.arch.table_size(self.tables[base]))
        &&& forall|base: SpecPAddr| #[trigger]
            self.tables.contains_key(base) ==> base.0 + self.arch.table_size(self.tables[base])
                <= PADDR_UPPER_BOUND
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
        &&& self.root.aligned(self.arch.table_size(0))
        &&& self.root.0 + self.arch.table_size(0)
            <= PADDR_UPPER_BOUND
        // Root table is empty
        &&& self.contents[self.root] == Seq::new(self.arch.entry_count(0), |_i| 0u64)
    }

    /// Whether `index` is accessible in the table at physical base `base` (PA).
    pub open spec fn accessible(self, base: SpecPAddr, index: nat) -> bool {
        self.contains_table(base) && index < self.arch.entry_count(self.tables[base])
    }

    /// Read an entry from the table at physical base `base` (PA).
    pub open spec fn read(self, base: SpecPAddr, index: nat) -> u64
        recommends
            self.accessible(base, index),
    {
        self.contents[base][index as int]
    }

    /// Allocate a new table.
    ///
    /// Design note: this is intentionally uninterpreted. The implementation allocator chooses
    /// a fresh HVA, but `PageTableMem` translates it before exposing `new_base`, so this model
    /// observes only the resulting physical base (PA). The admitted facts below are the TCB
    /// restriction that pins this uninterpreted function to `alloc_table_spec`.
    pub uninterp spec fn alloc_table(self, level: nat) -> (Self, SpecPAddr)
        recommends
            self.alloc_table_pre(level),
    ;

    /// Precondition for `alloc_table`.
    pub open spec fn alloc_table_pre(self, level: nat) -> bool {
        0 < level < self.arch.level_count()
    }

    /// Specification of `alloc_table`; `new_base` is the new table's physical base (PA).
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
        &&& new_base.0 < usize::MAX
        &&& new_base.0 + s1.arch.table_size(level)
            <= PADDR_UPPER_BOUND
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

    /// Deallocate the non-root table at physical base `base` (PA).
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

    /// Specification of `dealloc_table`; `base` is a physical table base (PA).
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

    /// Update an entry in the table at physical base `base` (PA).
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

/// Concrete page-table memory implementation and the sole PA/HVA translation boundary.
/// The type parameter `A` is the backend frame allocator, whose addresses are HVA.
pub struct PageTableMem<A> where A: BitmapAllocator {
    /// Page table architecture
    pub arch: PTArch,
    /// Physical address (PA) of the root table. It is fixed after initialization.
    pub root: PAddr,
    /// Fixed direct-map offset: `PA = HVA - hva_to_pa_offset`.
    pub hva_to_pa_offset: usize,
    /// Hypervisor virtual base address (HVA) of the allocator's frame range.
    pub allocator_base: Ghost<SpecPAddr>,
    /// Abstract allocator client that tracks all page-table frames.
    pub client: Tracked<Option<ClientState>>,
    /// Ghost table map keyed by physical table bases (PA).
    pub tables: Ghost<Map<SpecPAddr, nat>>,
    /// Phantom data
    pub _phantom: PhantomData<A>,
}

impl<A> PageTableMem<A> where A: BitmapAllocator {
    pub open spec fn inst_id(&self) -> InstanceId {
        self.client@->Some_0.inst_id()
    }

    /// Convert a physical table address `addr` (PA) to its allocator frame ID.
    /// Frame IDs are computed from the corresponding HVA because allocator state and
    /// frame permissions are HVA-based.
    pub open spec fn paddr_to_fid_spec(&self, addr: SpecPAddr) -> FrameID {
        (self.pa_to_hva_spec(addr).0 - self.allocator_base@.0) as nat / SPEC_FRAME_SIZE
    }

    /// Translate a hypervisor virtual address `addr` (HVA) to a physical address (PA).
    pub open spec fn hva_to_pa_spec(&self, addr: SpecPAddr) -> SpecPAddr {
        SpecPAddr((addr.0 - self.hva_to_pa_offset) as nat)
    }

    /// Translate a physical address `addr` (PA) to a hypervisor virtual address (HVA).
    pub open spec fn pa_to_hva_spec(&self, addr: SpecPAddr) -> SpecPAddr {
        SpecPAddr((addr.0 + self.hva_to_pa_offset) as nat)
    }

    /// Get the PA-only abstract view from client-owned permissions whose addresses are HVA.
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
        &&& self@.wf()
        // Invariants of the page table memory.
        &&& self.arch.view().valid()
        &&& self.client@ is Some
        // The client is valid.
        &&& self.client@->Some_0.wf(
            self.inst_id(),
        )
        // The allocator base is an HVA consistent with the AllocSpec instance.
        &&& self.allocator_base@ == inst_base(self.inst_id())
        &&& self.allocator_base@.aligned(
            SPEC_FRAME_SIZE,
        )
        // The direct-map offset preserves page alignment, and every allocator HVA
        // can be translated to a PA without underflow.
        &&& SpecPAddr(self.hva_to_pa_offset as nat).aligned(SPEC_FRAME_SIZE)
        &&& self.hva_to_pa_offset <= self.allocator_base@.0
        &&& self.allocator_base@.0 - self.hva_to_pa_offset + A::spec_cap() * SPEC_FRAME_SIZE
            <= PADDR_UPPER_BOUND
        // The PA root translates to an HVA frame allocated to this client.
        &&& self.client@->Some_0.owns(
            self.paddr_to_fid_spec(self.root@),
        )
        // Each PA table base is aligned and translates to an in-range allocator HVA.
        &&& forall|base: SpecPAddr| #[trigger]
            self.tables.contains_key(base) ==> {
                &&& base.aligned(SPEC_FRAME_SIZE)
                &&& self.pa_to_hva_spec(base).0 >= self.allocator_base@.0
                &&& self.pa_to_hva_spec(base).0 <= usize::MAX
            }
            // PA table bases correspond exactly to the allocator's HVA-backed frame IDs.
        &&& self.tables.dom().map(|addr: SpecPAddr| self.paddr_to_fid_spec(addr))
            == self.client@->Some_0.owned_frames()
        // TODO: we assume all tables in the hierarchical page table contain 512 8-byte entries, which is true
        // for hvisor's aarch64 implementation. We can make it more general in the future.
        &&& forall|level: nat|
            level < self.arch.view().level_count() ==> self.arch.view().entry_count(level) == 512
    }

    /// Translate an allocator or permission address `addr` (HVA) to a table address (PA).
    pub fn hva_to_pa(&self, addr: PAddr) -> (res: PAddr)
        requires
            addr.0 >= self.hva_to_pa_offset,
        ensures
            res@ == self.hva_to_pa_spec(addr@),
            self.pa_to_hva_spec(res@) == addr@,
    {
        PAddr((addr.0 - self.hva_to_pa_offset) as usize)
    }

    /// Translate a table address `addr` (PA) to an allocator and `PPtr` address (HVA).
    pub fn pa_to_hva(&self, addr: PAddr) -> (res: PAddr)
        requires
            addr.0 + self.hva_to_pa_offset <= usize::MAX,
        ensures
            res@ == self.pa_to_hva_spec(addr@),
            self.hva_to_pa_spec(res@) == addr@,
    {
        PAddr((addr.0 + self.hva_to_pa_offset) as usize)
    }

    /// Create page-table memory. The allocator supplies the root in HVA space; `root` stores PA.
    pub fn new(allocator: &GlobalAllocator<A>, arch: PTArch, hva_to_pa_offset: usize) -> (res: Self)
        requires
            allocator.invariants(),
            arch@.valid(),
            hva_to_pa_offset <= allocator.base.0,
            SpecPAddr(hva_to_pa_offset as nat).aligned(SPEC_FRAME_SIZE),
            allocator.base@.0 - hva_to_pa_offset + A::spec_cap() * SPEC_FRAME_SIZE
                <= PADDR_UPPER_BOUND,
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
        // The allocator and permission use `root_hva`; the page table and model use `root` (PA).
        let (root_hva, Tracked(client)) = allocator.alloc(Tracked(client));
        let root = PAddr(root_hva.0 - hva_to_pa_offset);

        let tables = Ghost(Map::empty().insert(root@, 0));
        let ghost fid = allocator.paddr_to_fid_spec(root_hva@);
        let tracked frame_perm: &Frame4KPerm = client.borrow_perm(fid, Ghost(allocator.inst_id()));

        let res = Self {
            arch,
            root,
            hva_to_pa_offset,
            allocator_base: Ghost(inst_base(allocator.inst_id())),
            client: Tracked(Some(client)),
            tables,
            _phantom: PhantomData,
        };
        proof {
            assert(res.client@ is Some);
            assert(res.pa_to_hva_spec(root@) == root_hva@);
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
            vstd::arithmetic::div_mod::lemma_sub_mod_noop(
                root_hva@.0 as int,
                hva_to_pa_offset as int,
                SPEC_FRAME_SIZE as int,
            );
            assert(root@.aligned(SPEC_FRAME_SIZE));
            assert(arch@.table_size(0) == SPEC_FRAME_SIZE);
            assert(root_hva@.0 + SPEC_FRAME_SIZE <= allocator.base@.0 + A::spec_cap()
                * SPEC_FRAME_SIZE);
            assert(root@.0 + hva_to_pa_offset == root_hva@.0);
            assert(allocator.base@.0 - hva_to_pa_offset + hva_to_pa_offset == allocator.base@.0);
            assert(root@.0 + SPEC_FRAME_SIZE <= PADDR_UPPER_BOUND);
            assert(res.view().init());
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

    /// Allocate a new table and return its physical base address (PA) to `PageTable`.
    pub fn alloc_table(&mut self, allocator: &GlobalAllocator<A>, level: usize) -> (res: PAddr)
        requires
            allocator.invariants(),
            old(self).invariants(),
            old(self).inst_id() == allocator.inst_id(),
            0 < level < old(self).arch.view().level_count(),
        ensures
            SpecPageTableMem::alloc_table_spec(old(self)@, self@, level as nat, res@),
            self.inst_id() == old(self).inst_id(),
            allocator.invariants(),
            self.invariants(),
    {
        broadcast use lemma_frame4k_to_u64_seq;

        let tracked client = self.client.tracked_take();
        // The allocator returns `new_hva`; translate it to `new_base` (PA) before exposing it.
        let (new_hva, Tracked(client)) = allocator.alloc(Tracked(client));
        let new_base = self.hva_to_pa(new_hva);

        let ghost fid = self.paddr_to_fid_spec(new_base@);
        let tracked frame_perm: &Frame4KPerm = client.frame_perms.tracked_borrow(fid);
        self.client = Tracked(Some(client));
        self.tables = Ghost(self.tables@.insert(new_base@, level as nat));

        proof {
            let s1: SpecPageTableMem = old(self)@;
            let s2: SpecPageTableMem = self@;

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
            assert(new_hva@.0 + SPEC_FRAME_SIZE <= old(self).allocator_base@.0 + A::spec_cap()
                * SPEC_FRAME_SIZE);
            assert(new_base@.0 + old(self).hva_to_pa_offset == new_hva@.0);
            assert(old(self).allocator_base@.0 - old(self).hva_to_pa_offset + old(
                self,
            ).hva_to_pa_offset == old(self).allocator_base@.0);
            assert((level as nat) < s1.arch.level_count());
            assert(s1.arch.table_size(level as nat) == SPEC_FRAME_SIZE);
            assert(new_base@.0 + s1.arch.table_size(level as nat) <= PADDR_UPPER_BOUND);
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

    /// Deallocate the non-root table at physical base `base` (PA).
    pub fn dealloc_table(&mut self, allocator: &GlobalAllocator<A>, base: PAddr)
        requires
            allocator.invariants(),
            old(self).invariants(),
            old(self).inst_id() == allocator.inst_id(),
            old(self).tables@.contains_key(base@),
            base != old(self).root,
        ensures
            SpecPageTableMem::dealloc_table_spec(old(self)@, self@, base@),
            self.inst_id() == old(self).inst_id(),
            allocator.invariants(),
            self.invariants(),
    {
        broadcast use BitmapAllocator::lemma_view_len_is_cap;
        // Recover the HVA used by the allocator, frame permission, and `PPtr`.

        let hva = self.pa_to_hva(base);
        let ghost fid = self.paddr_to_fid_spec(base@);
        // Clear the table contents before returning the frame to the free pool.
        let tracked mut client = self.client.tracked_take();
        assert(client.frame_perms.contains_key(fid));
        let tracked frame_perm: Frame4KPerm = client.frame_perms.tracked_remove(fid);

        // Convert the permission to table permission
        let tracked table_perm: Table512Perm = frame4k_perm_to_table512_perm(frame_perm);
        assert(table_perm.addr() == hva.0);
        assert(table_perm.is_init());

        // `PPtr` dereferences the table through its HVA before allocator deallocation.
        let pptr = PPtr::<Table512>::from_addr(hva.0);
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

        // Return the HVA frame to the HVA-based allocator.
        let Tracked(client) = allocator.dealloc(Tracked(client), hva);
        self.client = Tracked(Some(client));
        self.tables = Ghost(self.tables@.remove(base@));

        proof {
            let s1: SpecPageTableMem = old(self)@;
            let s2: SpecPageTableMem = self@;

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

            // Invariants preserved
            SpecPageTableMem::lemma_dealloc_table_preserves_wf(s1, s2, base@);
            assert(self.tables@.dom().map(|addr: SpecPAddr| self.paddr_to_fid_spec(addr))
                == self.client@->Some_0.owned_frames());
            assert(self.invariants());
        }
    }

    /// Deallocate the root table, whose stored address is PA, when destroying this memory.
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
        // `root` remains the PA seen by PageTable; `root_hva` is used for memory access/freeing.
        let root = this.root;
        let root_hva = this.pa_to_hva(root);
        let ghost fid = this.paddr_to_fid_spec(root@);
        let tracked mut client = this.client.tracked_take();
        let tracked frame_perm: Frame4KPerm = client.frame_perms.tracked_remove(fid);

        let tracked table_perm: Table512Perm = frame4k_perm_to_table512_perm(frame_perm);
        assert(table_perm.addr() == root_hva.0);
        assert(table_perm.is_init());

        let pptr = PPtr::<Table512>::from_addr(root_hva.0);
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

        let Tracked(_client) = allocator.dealloc(Tracked(client), root_hva);
    }

    /// Read from the table at physical base `base` (PA).
    pub fn read(&self, base: PAddr, index: usize) -> (res: u64)
        requires
            self.invariants(),
            self@.accessible(base@, index as nat),
        ensures
            #[trigger] self@.read(base@, index as nat) == res,
    {
        // Translate the caller's PA to the HVA carried by its permission and used by `PPtr`.
        let hva = self.pa_to_hva(base);
        let ghost fid = self.paddr_to_fid_spec(base@);
        assert(self.client->Some_0.owns(fid));
        // Borrow the frame permission
        let tracked frame_perm: &Frame4KPerm =
            self.client.tracked_borrow().frame_perms.tracked_borrow(fid);
        assert(frame_perm.addr() == hva.0);
        assert(frame_perm.is_init());

        // Convert the permission to table permission
        let tracked table_perm: &Table512Perm = frame4k_perm_ref_to_table512_perm_ref(frame_perm);
        assert(table_perm.addr() == hva.0);
        assert(table_perm.is_init());

        // Dereference through the HVA; the abstract read remains keyed by PA.
        let pptr = PPtr::<Table512>::from_addr(hva.0);
        let table = pptr.read(Tracked(table_perm));
        table.index(index)
    }

    /// Write to the table at physical base `base` (PA).
    pub fn write(&mut self, base: PAddr, index: usize, value: u64)
        requires
            old(self).invariants(),
            old(self)@.accessible(base@, index as nat),
        ensures
            self@ == old(self)@.write(base@, index as nat, value),
            self.inst_id() == old(self).inst_id(),
            self.invariants(),
    {
        // Translate the caller's PA to the HVA carried by its permission and used by `PPtr`.
        let hva = self.pa_to_hva(base);
        let ghost fid = self.paddr_to_fid_spec(base@);
        // Take the client to get the permission for the frame
        let tracked mut client = self.client.tracked_take();
        assert(client.frame_perms.contains_key(fid));
        let tracked frame_perm: Frame4KPerm = client.frame_perms.tracked_remove(fid);

        // Convert the permission to table permission
        let tracked table_perm: Table512Perm = frame4k_perm_to_table512_perm(frame_perm);
        assert(table_perm.addr() == hva.0);
        assert(table_perm.is_init());

        // Dereference through the HVA; the abstract write remains keyed by PA.
        let pptr = PPtr::<Table512>::from_addr(hva.0);
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
            assert(self@.contents == old(self)@.contents.insert(
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
