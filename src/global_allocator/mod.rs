//! An abstract model of global resource allocation.
//!
//! A resource (e.g. memory frame, IO port) is represented by a unique token. There is a global pool of
//! free resources, and multiple clients can allocate/deallocate resources from/to the global pool.
//! The global allocator model maintains the free resources and the resources allocated to each client.
//!
//! A client represents an entity that uses some resources for a specific purpose. For example, a
//! PageTableMem can be regarded as a client that allocates frames for page tables. Each client
//! has its own list of allocated resources.
//!
//! A client can request to allocate a resource from the global free pool. If there is at least one
//! free resource, the allocation succeeds and the resource is moved from the free pool to the client's
//! allocated list. A client can only deallocate a resource that it has allocated before. The deallocation
//! moves the resource from the client's allocated list back to the global free pool.
//!
//! The global allocator model maintains the following invariant: a resource can only be in one place at a time, i.e.
//! either in the global free pool or in one client's allocated list.
use std::{marker::PhantomData, str};

use vstd::prelude::*;

pub mod frame;

verus! {

/// Global allocator model.
pub struct GlobalAllocatorModel {
    /// Free resources available for allocation.
    pub free: Set<nat>,
    /// Clients using resources.
    pub clients: Map<nat, Set<nat>>,
}

impl GlobalAllocatorModel {
    /// Invariants of the global allocator model.
    pub open spec fn invariants(self) -> bool {
        // No resource is both in free list and clients
        &&& forall|rid: nat, cid: nat|
            self.free.contains(rid) && self.clients.contains_key(cid)
                ==> !self.clients[cid].contains(
                rid,
            )
            // No resource is in multiple clients
        &&& forall|rid: nat, c1: nat, c2: nat|
            self.clients.contains_key(c1) && self.clients.contains_key(c2) && c1 != c2 ==> !(
            #[trigger] self.clients[c1].contains(rid) && #[trigger] self.clients[c2].contains(rid))
    }

    /// Allocate a resource for a client.
    pub open spec fn alloc(s1: Self, s2: Self, cid: nat, rid: nat) -> bool
        recommends
            s1.invariants(),
            !s1.free.is_empty(),
            s1.clients.contains_key(cid),
    {
        s1.free.contains(rid) && s2.free == s1.free.remove(rid) && s2.clients == s1.clients.insert(
            cid,
            s1.clients[cid].insert(rid),
        )
    }

    /// Deallocate a resource from a client.
    pub open spec fn dealloc(s1: Self, s2: Self, cid: nat, rid: nat) -> bool
        recommends
            s1.invariants(),
            s1.clients.contains_key(cid),
            #[trigger] s1.clients[cid].contains(rid),
    {
        s2.free == s1.free.insert(rid) && s2.clients == s1.clients.insert(
            cid,
            s1.clients[cid].remove(rid),
        )
    }

    /// Add a new client.
    pub open spec fn add_client(s1: Self, s2: Self, cid: nat) -> bool
        recommends
            s1.invariants(),
            !s1.clients.contains_key(cid),
    {
        s2.free == s1.free && s2.clients == s1.clients.insert(cid, Set::empty())
    }

    /// Remove a client and free its resources.
    pub open spec fn remove_client(s1: Self, s2: Self, cid: nat) -> bool
        recommends
            s1.invariants(),
            s1.clients.contains_key(cid),
    {
        s2.free == s1.free.union(s1.clients[cid]) && s2.clients == s1.clients.remove(cid)
    }

    /// Lemma. `alloc` preserves invariants.
    pub proof fn lemma_alloc_preserves_invariants(s1: Self, s2: Self, cid: nat, rid: nat)
        requires
            s1.invariants(),
            !s1.free.is_empty(),
            s1.clients.contains_key(cid),
            Self::alloc(s1, s2, cid, rid),
        ensures
            s2.invariants(),
    {
        assert(s2.invariants());
    }

    /// Lemma. `dealloc` preserves invariants.
    pub proof fn lemma_dealloc_preserves_invariants(s1: Self, s2: Self, cid: nat, rid: nat)
        requires
            s1.invariants(),
            s1.clients.contains_key(cid),
            #[trigger] s1.clients[cid].contains(rid),
            Self::dealloc(s1, s2, cid, rid),
        ensures
            s2.invariants(),
    {
        assert(s2.invariants());
    }

    /// Lemma. `add_client` preserves invariants.
    pub proof fn lemma_add_client_preserves_invariants(s1: Self, s2: Self, cid: nat)
        requires
            s1.invariants(),
            !s1.clients.contains_key(cid),
            Self::add_client(s1, s2, cid),
        ensures
            s2.invariants(),
    {
        assert(s2.invariants());
    }

    /// Lemma. `remove_client` preserves invariants.
    pub proof fn lemma_remove_client_preserves_invariants(s1: Self, s2: Self, cid: nat)
        requires
            s1.invariants(),
            s1.clients.contains_key(cid),
            Self::remove_client(s1, s2, cid),
        ensures
            s2.invariants(),
    {
        assert(s2.invariants());
    }
}

/// Resource type - a token that can be mapped to/from nat. User can define their own resource type
/// by implementing the `Resource` trait.
pub trait Resource: Sized {
    /// Convert the resource to a unique nat token.
    spec fn to_nat(self) -> nat;

    /// Convert a nat token back to the resource.
    spec fn from_nat(n: nat) -> Self;

    /// Lemma. `to_nat` and `from_nat` are inverses.
    proof fn lemma_to_from_nat(self)
        ensures
            Self::from_nat(self.to_nat()) == self,
    ;
}

/// Trait for global allocator.
pub trait GlobalAllocator<R> where R: Resource {
    /// View as an abstract global allocator model.
    spec fn view(self) -> GlobalAllocatorModel;

    /// Invariants of the global allocator.
    spec fn invariants(self) -> bool;

    /// Allocate a resource for a client.
    fn alloc(&mut self, cid: usize) -> (res: R)
        requires
            old(self).view().clients.contains_key(cid as nat),
            !old(self).view().free.is_empty(),
            old(self).invariants(),
        ensures
            GlobalAllocatorModel::alloc(old(self)@, self@, cid as nat, res.to_nat()),
            self.invariants(),
    ;

    /// Deallocate a resource from a client.
    fn dealloc(&mut self, cid: usize, rid: R)
        requires
            old(self).view().clients.contains_key(cid as nat),
            #[trigger] old(self).view().clients[cid as nat].contains(rid.to_nat()),
            old(self).invariants(),
        ensures
            GlobalAllocatorModel::dealloc(old(self)@, self@, cid as nat, rid.to_nat()),
            self.invariants(),
    ;

    /// Add a new client.
    fn add_client(&mut self, cid: usize)
        requires
            old(self).invariants(),
        ensures
            GlobalAllocatorModel::add_client(old(self)@, self@, cid as nat),
            self.invariants(),
    ;

    /// Remove a client and free its resources.
    fn remove_client(&mut self, cid: usize)
        requires
            old(self).view().clients.contains_key(cid as nat),
            old(self).invariants(),
        ensures
            GlobalAllocatorModel::remove_client(old(self)@, self@, cid as nat),
            self.invariants(),
    ;

    /// `invariants` implies `GlobalAllocatorModel::invariants`
    proof fn lemma_implies_invariants(self)
        requires
            self.invariants(),
        ensures
            self@.invariants(),
    ;
}

} // verus!
