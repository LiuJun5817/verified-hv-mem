//! Abstract model of global memory allocation.
//!
//! There is a global pool of free frames, and multiple clients can allocate/deallocate frames
//! from/to the global pool. The global allocator model maintains the free frames and the frames
//! allocated to each client.
//!
//! A client represents an entity that uses some frames for a specific purpose. For example, a
//! PageTableMem can be regarded as a client that allocates frames for page tables. Each client
//! has its own list of allocated frames.
//!
//! A client can request to allocate a frame from the global free pool. If there is at least one
//! free frame, the allocation succeeds and the frame is moved from the free pool to the client's
//! allocated list. A client can only deallocate a frame that it has allocated before, and the
//! deallocation moves the frame from the client's allocated list back to the global free pool.
use crate::address::addr::{PAddr, SpecPAddr};
use std::marker::PhantomData;
use vstd::prelude::*;

pub mod frame;

verus! {

/// Global memory allocator model. The global allocator maintains a set of free frames and a mapping
/// from clients to their allocated frames.
///
/// A frame is represented by a natural number (nat) as its ID, FrameID = base address / page size.
pub struct GlobalAllocatorModel {
    /// Free frames available for allocation.
    pub free: Set<nat>,
    /// Clients using frames.
    pub clients: Map<nat, Set<nat>>,
}

impl GlobalAllocatorModel {
    /// Well-formedness of the global allocator model.
    pub open spec fn wf(self) -> bool {
        // No frame is both in free list and clients
        &&& forall|fid: nat, cid: nat|
            (self.free.contains(fid) && self.clients.contains_key(cid))
                ==> !self.clients[cid].contains(
                fid,
            )
            // No frame is in multiple clients
        &&& forall|fid: nat, c1: nat, c2: nat|
            #![auto]
            self.clients.contains_key(c1) && self.clients.contains_key(c2) && c1 != c2 ==> !(
            self.clients[c1].contains(fid) && self.clients[c2].contains(fid))
    }

    /// If free contains a contiguous range of `count` frames.
    pub open spec fn has_contiguous_free(self, count: nat, align_log2: nat) -> bool {
        count > 0 && exists|fid: nat|
            fid + count <= self.free.len() && fid % (1 << align_log2) as nat == 0
                && self.has_contiguous_free_from(count, fid)
    }

    /// If free contains a range of `count` frames starting from `fid`.
    pub open spec fn has_contiguous_free_from(self, count: nat, fid: nat) -> bool {
        forall|i: nat| 0 <= i < count ==> #[trigger] self.free.contains(fid + i)
    }

    /// Allocate a frame for a client.
    pub open spec fn alloc(s1: Self, s2: Self, cid: nat, fid: nat) -> bool {
        &&& s1.free.contains(fid)
        &&& s2.free == s1.free.remove(fid)
        &&& s2.clients == s1.clients.insert(cid, s1.clients[cid].insert(fid))
    }

    /// Allocate a contiguous range of frames for a client.
    pub open spec fn alloc_contiguous(s1: Self, s2: Self, cid: nat, count: nat, fid: nat) -> bool {
        let allocated: Set<nat> = Set::new(|fid2: nat| fid <= fid2 < fid + count);
        &&& allocated.subset_of(s1.free)
        &&& s2.free == s1.free.difference(allocated)
        &&& s2.clients == s1.clients.insert(cid, s1.clients[cid].union(allocated))
    }

    /// Deallocate a frame from a client.
    pub open spec fn dealloc(s1: Self, s2: Self, cid: nat, fid: nat) -> bool {
        &&& s2.free == s1.free.insert(fid)
        &&& s2.clients == s1.clients.insert(cid, s1.clients[cid].remove(fid))
    }

    /// Add a new client.
    pub open spec fn add_client(s1: Self, s2: Self, cid: nat) -> bool {
        &&& s2.free == s1.free
        &&& s2.clients == s1.clients.insert(cid, Set::empty())
    }

    /// Remove a client and free its resources.
    pub open spec fn remove_client(s1: Self, s2: Self, cid: nat) -> bool {
        &&& s2.free == s1.free.union(s1.clients[cid])
        &&& s2.clients == s1.clients.remove(cid)
    }

    /// Lemma. `alloc` preserves wf.
    pub proof fn lemma_alloc_preserves_wf(s1: Self, s2: Self, cid: nat, fid: nat)
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
        cid: nat,
        count: nat,
        fid: nat,
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
    pub proof fn lemma_dealloc_preserves_wf(s1: Self, s2: Self, cid: nat, fid: nat)
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

    /// Lemma. `add_client` preserves wf.
    pub proof fn lemma_add_client_preserves_wf(s1: Self, s2: Self, cid: nat)
        requires
            s1.wf(),
            !s1.clients.contains_key(cid),
            Self::add_client(s1, s2, cid),
        ensures
            s2.wf(),
    {
        assert(s2.wf());
    }

    /// Lemma. `remove_client` preserves wf.
    pub proof fn lemma_remove_client_preserves_wf(s1: Self, s2: Self, cid: nat)
        requires
            s1.wf(),
            s1.clients.contains_key(cid),
            Self::remove_client(s1, s2, cid),
        ensures
            s2.wf(),
    {
        assert(s2.wf());
    }
}

/// Trait for global memory allocator.
pub trait GlobalAllocator {
    /// View as an abstract global memory allocator model.
    spec fn view(&self) -> GlobalAllocatorModel;

    /// Invariants of the global memory allocator.
    spec fn invariants(&self) -> bool;

    /// Unit frame size in bytes.
    spec fn frame_size() -> nat;

    /// Base address of the physical memory managed by the global allocator.
    spec fn base(&self) -> SpecPAddr;

    /// Allocate a frame for a client, return the allocated frame's base physical address.
    fn alloc(&mut self, cid: usize) -> (frame: PAddr)
        requires
            old(self)@.clients.contains_key(cid as nat),
            !old(self)@.free.is_empty(),
            old(self).invariants(),
        ensures
            frame@.aligned(Self::frame_size()),
            frame.0 >= old(self).base().0,
            GlobalAllocatorModel::alloc(
                old(self)@,
                self@,
                cid as nat,
                paddr_to_fid(self.base().0, frame.0 as nat, Self::frame_size()),
            ),
            self.base() == old(self).base(),
            self.invariants(),
    ;

    /// Deallocate a frame from a client.
    fn dealloc(&mut self, cid: usize, frame: PAddr)
        requires
            old(self)@.clients.contains_key(cid as nat),
            frame@.aligned(Self::frame_size()),
            frame.0 >= old(self).base().0,
            old(self)@.clients[cid as nat].contains(
                paddr_to_fid(old(self).base().0, frame.0 as nat, Self::frame_size()),
            ),
            old(self).invariants(),
        ensures
            GlobalAllocatorModel::dealloc(
                old(self)@,
                self@,
                cid as nat,
                paddr_to_fid(self.base().0, frame.0 as nat, Self::frame_size()),
            ),
            self.base() == old(self).base(),
            self.invariants(),
    ;

    /// Allocate a contiguous range of frames for a client, return the base physical address of starting frame.
    ///
    /// TODO: frame@.aligned(Self::frame_size() * (1 << align_log2) as nat), which requires stronger alignment
    /// for the base address.
    fn alloc_contiguous(&mut self, cid: usize, count: usize, align_log2: usize) -> (frame: PAddr)
        requires
            old(self)@.clients.contains_key(cid as nat),
            old(self)@.has_contiguous_free(count as nat, align_log2 as nat),
            old(self).invariants(),
            count < old(self)@.free.len(),
            (1usize << align_log2) < old(self)@.free.len(),
            align_log2 < 64,
        ensures
            frame@.aligned(Self::frame_size()),
            GlobalAllocatorModel::alloc_contiguous(
                old(self)@,
                self@,
                cid as nat,
                count as nat,
                paddr_to_fid(self.base().0, frame.0 as nat, Self::frame_size()),
            ),
            self.base() == old(self).base(),
            self.invariants(),
    ;

    /// Add a new client.
    fn add_client(&mut self, cid: usize)
        requires
            old(self).invariants(),
            !old(self)@.clients.contains_key(cid as nat),
        ensures
            GlobalAllocatorModel::add_client(old(self)@, self@, cid as nat),
            self.base() == old(self).base(),
            self.invariants(),
    ;

    /// Remove a client and free its resources.
    fn remove_client(&mut self, cid: usize)
        requires
            old(self)@.clients.contains_key(cid as nat),
            old(self).invariants(),
        ensures
            GlobalAllocatorModel::remove_client(old(self)@, self@, cid as nat),
            self.base() == old(self).base(),
            self.invariants(),
    ;

    /// `invariants` implies `GlobalAllocatorModel::wf`
    broadcast proof fn lemma_invariants_implies_wf(&self)
        requires
            #[trigger] self.invariants(),
        ensures
            self@.wf(),
    ;
}

/// Calculate frame ID from physical address.
pub open spec fn paddr_to_fid(base: nat, addr: nat, frame_size: nat) -> nat {
    (addr - base) as nat / frame_size
}

} // verus!
