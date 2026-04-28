//! Global memory allocator and its abstract model.
//!
//! There is a global pool of free frames, and multiple clients can allocate/deallocate frames
//! from/to the global pool. The global allocator model maintains the free frames and the frames
//! allocated to each client. A client represents an entity that uses some frames for a specific
//! purpose. For example, a PageTableMem can be regarded as a client that allocates frames for 
//! page tables.
//!
//! A client can request to allocate a frame from the global free pool. If there is at least one
//! free frame, the allocation succeeds and the frame is moved from the free pool to the client's
//! allocated list. A client can only deallocate a frame that it has allocated before, and the
//! deallocation moves the frame from the client's allocated list back to the global free pool.
use crate::{
    address::addr::{PAddr, SpecPAddr},
    bitmap_allocator::bitmap_trait::BitmapAllocator,
};
use vstd::{
    prelude::*,
    set_lib::lemma_len_subset,
    simple_pptr::{PPtr, PointsTo},
};

verus! {

/// Frame ID
pub type FrameID = nat;

/// Unique Identifier allocated by the global allocator.
pub tracked struct ClientID(int);

/// Axiom: the set of all ClientIDs is infinite.
axiom fn axiom_client_id_fullset_infinite()
    ensures
        !Set::<ClientID>::full().finite(),
;

/// Lemma: For any finite set of ClientIDs, there exists a different ClientID not in the set.
pub proof fn lemma_exists_different_client_id(s: Set<ClientID>)
    requires
        s.finite(),
    ensures
        exists|other: ClientID| !s.contains(other),
{
    let full = Set::<ClientID>::full();
    axiom_client_id_fullset_infinite();

    if forall|other: ClientID| s.contains(other) {
        assert(full.subset_of(s));
        // contradiction
        assert(full.finite());
    }
}

/// Global memory allocator model. The global allocator maintains a set of free frames and a mapping
/// from clients to their allocated frames.
///
/// A frame is represented by a natural number (nat) as its ID, FrameID = base address / page size.
pub struct GlobalAllocatorModel {
    /// Free frames available for allocation.
    pub free: Set<FrameID>,
    /// Clients using frames.
    pub clients: Map<ClientID, Set<FrameID>>,
}

impl GlobalAllocatorModel {
    /// Well-formedness of the global allocator model.
    pub open spec fn wf(self) -> bool {
        // No frame is both in free list and clients
        &&& forall|cid: ClientID| #[trigger]
            self.clients.contains_key(cid) ==> self.clients[cid].disjoint(
                self.free,
            )
        // No frame is in multiple clients
        &&& forall|c1: ClientID, c2: ClientID| #[trigger]
            self.clients.contains_key(c1) && #[trigger] self.clients.contains_key(c2) && c1 != c2
                ==> self.clients[c1].disjoint(self.clients[c2])
    }

    /// If free contains a contiguous range of `count` frames.
    pub open spec fn has_contiguous_free(self, count: nat, align_log2: nat) -> bool {
        count > 0 && exists|fid: FrameID|
            fid + count <= self.free.len() && fid % (1 << align_log2) as nat == 0
                && self.has_contiguous_free_from(count, fid)
    }

    /// If free contains a range of `count` frames starting from `fid`.
    pub open spec fn has_contiguous_free_from(self, count: nat, fid: FrameID) -> bool {
        forall|i: nat| 0 <= i < count ==> #[trigger] self.free.contains(fid + i)
    }

    /// Allocate a frame for a client.
    pub open spec fn alloc(s1: Self, s2: Self, cid: ClientID, fid: FrameID) -> bool {
        &&& s1.free.contains(fid)
        &&& s2.free == s1.free.remove(fid)
        &&& s2.clients == if s1.clients.contains_key(cid) {
            s1.clients.insert(cid, s1.clients[cid].insert(fid))
        } else {
            s1.clients.insert(cid, set![fid])
        }
    }

    /// Deallocate a frame from a client.
    pub open spec fn dealloc(s1: Self, s2: Self, cid: ClientID, fid: FrameID) -> bool {
        &&& s2.free == s1.free.insert(fid)
        &&& s2.clients == s1.clients.insert(cid, s1.clients[cid].remove(fid))
    }

    /// Allocate a contiguous range of frames for a client.
    pub open spec fn alloc_contiguous(
        s1: Self,
        s2: Self,
        cid: ClientID,
        count: nat,
        fid: FrameID,
    ) -> bool {
        let allocated: Set<FrameID> = Set::new(|fid2: FrameID| fid <= fid2 < fid + count);
        &&& allocated.subset_of(s1.free)
        &&& s2.free == s1.free.difference(allocated)
        &&& s2.clients == if s1.clients.contains_key(cid) {
            s1.clients.insert(cid, s1.clients[cid].union(allocated))
        } else {
            s1.clients.insert(cid, allocated)
        }
    }

    /// Add a new client to the global allocator.
    pub open spec fn add_client(s1: Self, s2: Self, cid: ClientID) -> bool {
        &&& !s1.clients.contains_key(cid)
        &&& s2.clients == s1.clients.insert(cid, Set::empty())
        &&& s2.free == s1.free
    }

    /// Lemma. `alloc` preserves wf.
    pub proof fn lemma_alloc_preserves_wf(s1: Self, s2: Self, cid: ClientID, fid: FrameID)
        requires
            s1.wf(),
            !s1.free.is_empty(),
            s1.clients.contains_key(cid),
            Self::alloc(s1, s2, cid, fid),
        ensures
            s2.wf(),
    {
        assert(s2.wf());
    }

    /// Lemma. `alloc_contiguous` preserves wf.
    pub proof fn lemma_alloc_contiguous_preserves_wf(
        s1: Self,
        s2: Self,
        cid: ClientID,
        count: nat,
        fid: FrameID,
    )
        requires
            s1.wf(),
            s1.has_contiguous_free_from(count, fid),
            s1.clients.contains_key(cid),
            Self::alloc_contiguous(s1, s2, cid, count, fid),
        ensures
            s2.wf(),
    {
        assume(s2.wf());
    }

    /// Lemma. `dealloc` preserves wf.
    pub proof fn lemma_dealloc_preserves_wf(s1: Self, s2: Self, cid: ClientID, fid: FrameID)
        requires
            s1.wf(),
            s1.clients.contains_key(cid),
            #[trigger] s1.clients[cid].contains(fid),
            Self::dealloc(s1, s2, cid, fid),
        ensures
            s2.wf(),
    {
        assert(s2.wf());
    }
}

/// Permission to access a 4K Frame
pub type Frame4KPerm = PointsTo<[u8; 4096]>;

/// Global memory allocator implementation using a bitmap allocator as the backend.
pub struct GlobalAllocator<A> where A: BitmapAllocator {
    /// Base address of the memory region managed by the global allocator.
    pub base: PAddr,
    /// The backend bitmap allocator.
    pub allocator: A,
    /// Permissions of free frames.
    pub free: Tracked<Map<FrameID, Frame4KPerm>>,
    /// Permissions of frames allocated to each client.
    pub tracked clients: Tracked<Map<ClientID, Map<FrameID, Frame4KPerm>>>,
}

impl<A> GlobalAllocator<A> where A: BitmapAllocator {
        /// Unit size of frames managed by the global allocator.
    pub const FRAME_SIZE: usize = 4096;

    /// Basic well-formedness
    pub open spec fn basic_wf(&self) -> bool {
        // Invariants of the backend allocator.
        &&& self.allocator.wf()
        // Base address must be aligned to frame size.
        &&& self.base.view().aligned(
            Self::FRAME_SIZE as nat,
        )
        // Max address must be representable in usize.
        &&& self.base.0 + (A::spec_cap() * Self::FRAME_SIZE)
            <= usize::MAX
        // New cid can always be generated.
        &&& self.clients@.dom().finite()
    }

    /// All frames in `free` are free in the backend allocator
    pub open spec fn free_consistent_and_complete(&self) -> bool {
        self.free@.dom() == Set::new(|i: nat| i < A::spec_cap() && self.allocator.view()[i as int])
    }

    /// All frames in client `cid` are allocated in the backend allocator.
    pub open spec fn clients_consistent(&self) -> bool {
        forall|cid: ClientID|
            self.clients@.contains_key(cid) ==> forall|i: nat| #[trigger]
                self.clients@[cid].contains_key(i) ==> i < A::spec_cap()
                    && !self.allocator.view()[i as int]
    }

    /// Any allocated frame must be tracked by some client.
    pub open spec fn clients_complete(&self) -> bool {
        forall|i: nat|
            i < A::spec_cap() && !self.allocator.view()[i as int] ==> (exists|cid: ClientID|
             #[trigger]
                self.clients@.contains_key(cid) && self.clients@[cid].contains_key(i))
    }

    /// Permissions initialized and consistent with the physical address
    pub open spec fn perm_wf(&self) -> bool {
        &&& forall|fid: FrameID| #[trigger]
            self.free@.contains_key(fid) ==> self.free@[fid].is_init() && self.base.0 + fid
                * Self::FRAME_SIZE == self.free@[fid].addr()
        &&& forall|cid: ClientID, fid: FrameID| #[trigger]
            self.clients@.contains_key(cid) && #[trigger] self.clients@[cid].contains_key(fid)
                ==> self.clients@[cid][fid].is_init() && self.base.0 + fid * Self::FRAME_SIZE
                == self.clients@[cid][fid].addr()
    }

    /// Total well-formedness
    pub open spec fn invariants(&self) -> bool {
        &&& self.view().wf()
        &&& self.basic_wf()
        &&& self.free_consistent_and_complete()
        &&& self.clients_consistent()
        &&& self.clients_complete()
        &&& self.perm_wf()
    }

    /// Spec function to calculate the frame ID from a physical address.
    pub open spec fn spec_paddr_to_fid(&self, addr: SpecPAddr) -> (res: FrameID) {
        (addr.0 - self.base@.0) as nat / Self::FRAME_SIZE as nat
    }

    /// Calculate the frame ID from a physical address.
    pub fn paddr_to_fid(&self, addr: PAddr) -> (res: usize)
        requires
            self.base@.aligned(Self::FRAME_SIZE as nat),
            addr@.aligned(Self::FRAME_SIZE as nat),
            addr.0 >= self.base.0,
        ensures
            res == self.spec_paddr_to_fid(addr@),
    {
        (addr.0 - self.base.0) / Self::FRAME_SIZE
    }

    /// Calculate the physical address from a frame ID.
    pub fn fid_to_paddr(&self, fid: usize) -> (res: PAddr)
        by (nonlinear_arith)
        requires
            self.base@.aligned(Self::FRAME_SIZE as nat),
            self.base.0 + fid * Self::FRAME_SIZE <= usize::MAX,
        ensures
            res@.aligned(Self::FRAME_SIZE as nat),
            res.0 == self.base.0 + fid * Self::FRAME_SIZE,
    {
        PAddr(self.base.0 + fid * Self::FRAME_SIZE)
    }

    /// Lemma. `free.len()` is less than or equal to the capacity of the backend allocator.
    proof fn lemma_free_len_le_allocator_cap(&self)
        requires
            self.invariants(),
        ensures
            self.view().free.len() <= A::spec_cap(),
    {
        let free = Set::new(|i: nat| i < A::spec_cap() && self.allocator.view()[i as int]);
        let full = Set::new(|i: nat| i < A::spec_cap());
        assert(free.subset_of(full));
        self.allocator.lemma_view_len_is_cap();
        lemma_len_nat_range_set(A::spec_cap() as nat);
        lemma_len_subset(free, full);
        assert(free.len() <= full.len() <= A::spec_cap());
    }

    /// View function to get the abstract model of the global allocator.
    pub open spec fn view(&self) -> GlobalAllocatorModel {
        GlobalAllocatorModel {
            free: self.free.view().dom(),
            clients: self.clients.view().map_values(
                |frames: Map<FrameID, Frame4KPerm>| frames.dom(),
            ),
        }
    }

    /// Allocate a frame for a client.
    pub fn alloc(&mut self, Tracked(cid): Tracked<ClientID>) -> (frame: PAddr)
        requires
            !old(self)@.free.is_empty(),
            old(self).clients@.contains_key(cid),
            old(self).invariants(),
        ensures
            frame@.aligned(Self::FRAME_SIZE as nat),
            frame.0 >= old(self).base@.0,
            GlobalAllocatorModel::alloc(old(self)@, self@, cid, self.spec_paddr_to_fid(frame@)),
            self.base@ == old(self).base@,
            self.invariants(),
    {
        // Alloc in the backend allocator
        let alloc_res = self.allocator.alloc();
        proof {
            // Prove there must be free slots
            old(self).allocator.lemma_view_len_is_cap();
            self.allocator.lemma_view_len_is_cap();
            if alloc_res is None {
                // Contradiction
                assert(forall|j: int| 0 <= j < A::spec_cap() ==> !self.allocator@[j]);
                assert(false);
            }
            assert(alloc_res is Some);
        }
        let fid = alloc_res.unwrap();
        proof {
            let fid: FrameID = fid as FrameID;
            assert(self.free@.contains_key(fid));

            // Move permission from free to the client
            let tracked perm: Frame4KPerm = self.free.tracked_remove(fid);
            assert(perm.is_init());
            let tracked mut client = self.clients.tracked_remove(cid);
            client.tracked_insert(fid, perm);
            self.clients.tracked_insert(cid, client);

            // Prove the slot is correctly allocated
            assert(self.allocator@ == old(self).allocator@.update(fid as int, false));
            assert(self@.free == old(self)@.free.remove(fid));
            assert(self@.clients[cid] == old(self)@.clients[cid].insert(fid));
            assert(self@.clients == old(self)@.clients.insert(
                cid,
                old(self)@.clients[cid].insert(fid),
            ));

            // Prove invariants hold
            assert(self.free@.dom() == Set::new(
                |i: nat| i < A::spec_cap() && self.allocator.view()[i as int],
            ));
            assert(self.invariants());
        }
        self.fid_to_paddr(fid)
    }

    /// Deallocate a frame from a client.
    pub fn dealloc(&mut self, Tracked(cid): Tracked<ClientID>, frame: PAddr)
        requires
            old(self)@.clients.contains_key(cid),
            frame@.aligned(Self::FRAME_SIZE as nat),
            frame.0 >= old(self).base@.0,
            old(self)@.clients[cid].contains(old(self).spec_paddr_to_fid(frame@)),
            old(self).invariants(),
        ensures
            GlobalAllocatorModel::dealloc(old(self)@, self@, cid, self.spec_paddr_to_fid(frame@)),
            self.base@ == old(self).base@,
            self.invariants(),
    {
        let fid = self.paddr_to_fid(frame);
        // Free in the backend allocator
        self.allocator.dealloc(fid);
        proof {
            let fid: FrameID = fid as nat;
            old(self).allocator.lemma_view_len_is_cap();
            self.allocator.lemma_view_len_is_cap();

            // Move permission from the client to free
            let tracked mut client = self.clients.tracked_remove(cid);
            let tracked perm = client.tracked_remove(fid);
            self.clients.tracked_insert(cid, client);
            self.free.tracked_insert(fid, perm);

            // Prove the slot is correctly freed
            assert(self.allocator@ == old(self).allocator@.update(fid as int, true));
            assert(self@.free == old(self)@.free.insert(fid));
            assert(self@.clients[cid] == old(self)@.clients[cid].remove(fid));
            assert(self@.clients == old(self)@.clients.insert(
                cid,
                old(self)@.clients[cid].remove(fid),
            ));

            // Prove invariants hold
            assert(self.free@.dom() == Set::new(
                |i: nat| i < A::spec_cap() && self.allocator.view()[i as int],
            ));
            assert forall|cid2: ClientID| self.clients@.contains_key(cid2) implies {
                forall|fid2: FrameID| #[trigger]
                    self.clients@[cid2].contains_key(fid2) ==> fid2 < A::spec_cap()
                        && !self.allocator.view()[fid2 as int]
            } by {
                if cid2 != cid {
                    assert(self.view().wf());
                    assert(self@.free.contains(fid));
                    assert(self@.clients.contains_key(cid2));
                    assert(self.clients@.contains_key(cid2));
                    assert(!self@.clients[cid2].contains(fid));
                }
            }
            assert(self.invariants());
        }
    }

    /// Allocate a contiguous range of frames for a client.
    pub fn alloc_contiguous(
        &mut self,
        Tracked(cid): Tracked<ClientID>,
        count: usize,
        align_log2: usize,
    ) -> (frame: PAddr)
        requires
            old(self)@.clients.contains_key(cid),
            old(self)@.has_contiguous_free(count as nat, align_log2 as nat),
            old(self).invariants(),
            count < old(self)@.free.len(),
            (1usize << align_log2) < old(self)@.free.len(),
            align_log2 < 64,
        ensures
            frame@.aligned(Self::FRAME_SIZE as nat),
            GlobalAllocatorModel::alloc_contiguous(
                old(self)@,
                self@,
                cid,
                count as nat,
                self.spec_paddr_to_fid(frame@),
            ),
            self.base@ == old(self).base@,
            self.invariants(),
    {
        proof {
            old(self).allocator.lemma_view_len_is_cap();
            self.allocator.lemma_view_len_is_cap();
            // TODO: this is essential
            assume(1usize << align_log2 == 1 << align_log2);
            // Preconditions of `alloc_contiguous`
            self.lemma_free_len_le_allocator_cap();
            assert(0 < count <= A::spec_cap());
        }
        // Alloc in the backend allocator
        let alloc_res = self.allocator.alloc_contiguous(count, align_log2);
        proof {
            assert(forall|j: nat|
                old(self)@.free.contains(j) ==> old(self).allocator@[j as int] && j
                    < A::spec_cap());
            // Preconditions ensure there must be contiguous free slots and meet alignment requirement
            assert(old(self).view().has_contiguous_free(count as nat, align_log2 as nat));
            let base = choose|base: nat|
                base + count <= A::spec_cap() && old(self).view().has_contiguous_free_from(
                    count as nat,
                    base,
                ) && base % (1 << align_log2) as nat == 0;
            assert(forall|i: nat| 0 <= i < count ==> #[trigger] old(self)@.free.contains(base + i));
            assert forall|j: nat| base <= j < base + count implies #[trigger] old(
                self,
            )@.free.contains(j) by {
                assert(0 <= (j - base) < count);
                assert(old(self)@.free.contains(base + (j - base) as nat));
            }
            // Must has contiguous free slots
            assert(alloc_res is Some) by {
                // Contradiction if allocation fails
                assert(A::spec_cap() >= 1usize << align_log2);
                assert(exists|i: int|
                    0 <= i <= A::spec_cap() - count
                        && !crate::bitmap_allocator::bitmap_trait::has_obstruction(
                        old(self).allocator@,
                        i,
                        count as int,
                        (1usize << align_log2) as int,
                    )) by {
                    // `base` is a candidate
                    assert(0 <= base as int <= A::spec_cap() - count);
                    assert(base as int % (1usize << align_log2) as int == 0);
                    assert(forall|k| base <= k < base + count ==> old(self).allocator@[k]);
                    assert(!crate::bitmap_allocator::bitmap_trait::has_obstruction(
                        old(self).allocator@,
                        base as int,
                        count as int,
                        (1usize << align_log2) as int,
                    ))
                }
            }
        }
        let fid = alloc_res.unwrap();
        proof {
            let fid: FrameID = fid as FrameID;
            assert(forall|j: nat| fid <= j < fid + count ==> old(self)@.free.contains(j));

            // Prove the slots are correctly allocated
            let allocated = Set::new(|i: nat| fid <= i < fid + count);
            assert(allocated.subset_of(old(self)@.free));

            // Move permissions from free to the client
            let tracked perms = self.free.tracked_remove_keys(allocated);
            let tracked mut client = self.clients.tracked_remove(cid);
            client.tracked_union_prefer_right(perms);
            self.clients.tracked_insert(cid, client);

            // `GlobalAllocatorModel::alloc_contiguous` holds
            assert(self@.free == old(self)@.free.difference(allocated));
            assert(self@.clients.dom() == old(self)@.clients.dom());
            assert(self@.clients[cid] == old(self)@.clients[cid].union(
                Set::new(|i: nat| fid <= i < fid + count),
            ));
            assert(self@.clients == old(self)@.clients.insert(
                cid,
                old(self)@.clients[cid].union(Set::new(|i: nat| fid <= i < fid + count)),
            ));
            assert(GlobalAllocatorModel::alloc_contiguous(
                old(self)@,
                self@,
                cid,
                count as nat,
                fid,
            ));

            // Prove invariants hold
            assert(self.free@.dom() == Set::new(
                |i: nat| i < A::spec_cap() && self.allocator.view()[i as int],
            ));
            assert(self.invariants());
        }
        self.fid_to_paddr(fid)
    }

    /// Add a new client to the global allocator and return its ClientID.
    pub proof fn add_client(tracked &mut self) -> (res: ClientID)
        requires
            old(self).invariants(),
        ensures
            GlobalAllocatorModel::add_client(old(self)@, self@, res),
            old(self).base == self.base,
            self.invariants(),
    {
        lemma_exists_different_client_id(self.clients@.dom());
        let cid = choose|cid: ClientID| !self.clients@.contains_key(cid);

        // Add the new client with an empty set of allocated frames
        self.clients.tracked_insert(cid, Map::tracked_empty());
        assert(self@.clients == old(self)@.clients.insert(cid, Set::empty()));
        assert forall|i: nat| i < A::spec_cap() && !self.allocator.view()[i as int] implies (exists|
            cid2: ClientID,
        | #[trigger]
            self.clients@.contains_key(cid2) && self.clients@[cid2].contains_key(i)) by {
            let cid2 = choose|cid2: ClientID| #[trigger]
                old(self).clients@.contains_key(cid2) && old(self).clients@[cid2].contains_key(i);
            assert(self.clients@.contains_key(cid2));
            assert(self.clients@[cid2].contains_key(i));
        }
        cid
    }
}


pub proof fn add_client_model(
    tracked clients: &mut Map<ClientID, Map<FrameID, Frame4KPerm>>,
) -> ClientID {
    let cid = choose|cid: ClientID| !clients.contains_key(cid);
    cid
}


/// Lemma. The set of natural numbers less than `len` is finite and has length `len`.
proof fn lemma_len_nat_range_set(len: nat)
    ensures
        Set::new(|i: nat| i < len).finite(),
        Set::new(|i: nat| i < len).len() == len,
    decreases len,
{
    let set = Set::new(|i: nat| i < len);
    if !set.finite() {
        nat_range_set_contradiction(len);
    }
    assert(set.finite());
    if len == 0 {
        assert(set.is_empty());
    } else {
        let sub_set = Set::new(|i: nat| i < len - 1);
        assert(sub_set == set.remove((len - 1) as nat));
        lemma_len_nat_range_set((len - 1) as nat);
    }
}

/// Contradiction lemma for the set of natural numbers less than `len` being finite.
proof fn nat_range_set_contradiction(len: nat)
    requires
        !Set::new(|i: nat| i < len).finite(),
    ensures
        !Set::<nat>::empty().finite(),
    decreases len,
{
    let set = Set::new(|i: nat| i < len);
    if len == 0 {
        assert(set.is_empty());
    } else {
        let sub_set = Set::new(|i: nat| i < len - 1);
        assert(sub_set == set.remove((len - 1) as nat));
        nat_range_set_contradiction((len - 1) as nat);
    }
}

} // verus!
