//! Global Frame Allocator, implementing trait `GlobalAllocator`.
use super::{GlobalAllocator, GlobalAllocatorModel, Resource};
use crate::{address::addr::PAddr, frame_allocator::frame_trait::FrameAllocator};
use vstd::prelude::*;

verus! {

/// Resouce type allocated by `GlobalFrameAllocator` - a 4KB frame.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Frame4K(pub PAddr);

/// Use Frame4K as the resource type.
impl Resource for Frame4K {
    open spec fn to_nat(self) -> nat {
        self.0.0 as nat
    }

    open spec fn from_nat(n: nat) -> Self {
        Frame4K(PAddr(n as usize))
    }

    proof fn lemma_to_from_nat(self)
        ensures
            Self::from_nat(self.to_nat()) == self,
    {
    }
}

/// An allocator client manages a set of indices.
pub struct FrameAllocatorClient {
    /// Client ID.
    pub id: usize,
    /// The set of indices allocated to this client.
    pub indices: Vec<Frame4K>,
}

impl Clone for FrameAllocatorClient {
    fn clone(&self) -> Self {
        Self { id: self.id, indices: self.indices.clone() }
    }
}

/// Global frame allocator implementation using a frame allocator as the backend.
pub struct GlobalFrameAllocator<FA> where FA: FrameAllocator {
    /// The backend frame allocator.
    pub allocator: FA,
    /// Allocator clients.
    pub clients: Vec<FrameAllocatorClient>,
}

impl<FA> GlobalFrameAllocator<FA> where FA: FrameAllocator {
    /// If there exists a client with the given id.
    pub open spec fn has_client(&self, cid: usize) -> bool {
        exists|i| #[trigger] self.clients[i].id == cid
    }

    /// Find the client with the given id, return its index.
    pub fn find_client(&self, cid: usize) -> (res: Option<usize>)
        ensures
            match res {
                Some(i) => 0 <= i < self.clients.len() && self.clients[i as int].id == cid,
                None => !self.has_client(cid),
            },
    {
        let mut i = 0;
        while i < self.clients.len()
            decreases self.clients.len() - i,
        {
            if self.clients[i].id == cid {
                return Some(i);
            }
            i += 1;
        }
        assume(!self.has_client(cid));
        None
    }
}

impl<FA> GlobalAllocator<Frame4K> for GlobalFrameAllocator<FA> where FA: FrameAllocator {
    open spec fn view(self) -> GlobalAllocatorModel {
        GlobalAllocatorModel {
            free: free_frames_to_set(&self.allocator),
            clients: Map::new(
                |id| exists|i| #[trigger] self.clients[i].id == id,
                |id|
                    {
                        let i: int = choose|i|
                            0 <= i < self.clients.len() && #[trigger] self.clients[i].id == id;
                        self.clients[i].indices.view().to_set().map(|frame: Frame4K| frame.to_nat())
                    },
            ),
        }
    }

    open spec fn invariants(self) -> bool {
        // Invariants of the global allocator.
        &&& self.allocator.wf()
        // Invariants of the resource model.
        &&& self.view().invariants()
        // No duplicate client id.
        &&& forall|i, j|
            #![auto]
            0 <= i < self.clients.len() && 0 <= j < self.clients.len() && i != j
                ==> self.clients[i].id
                != self.clients[j].id
        // No duplicate indices in each client.
        &&& forall|cid, i, j|
            0 <= cid < self.clients.len() && 0 <= i < self.clients[cid].indices.len() && 0 <= j
                < self.clients[cid].indices.len() && i != j ==> self.clients[cid].indices[i]
                != self.clients[cid].indices[j]
    }

    fn alloc(&mut self, cid: usize) -> (res: Frame4K) {
        let alloc_res = self.allocator.alloc();
        proof {
            if alloc_res is None {
                // There must be free slots
                self.allocator.lemma_view_len_eq_cap_pages();
                assert(forall|j: int| 0 <= j < FA::cap_pages() ==> !self.allocator.view()[j]);
                assert(free_frames_to_set(&self.allocator) === Set::empty());
                // Contradiction
                assert(false);
            }
        }
        assert(alloc_res is Some);
        let paddr = alloc_res.unwrap();

        // index for &mut not supported, so we need to copy
        let idx = self.find_client(cid).unwrap();
        let mut client = self.clients[idx].clone();
        client.indices.push(Frame4K(paddr));
        // replace back
        self.clients[idx] = client;

        proof {
            assert(old(self)@.invariants());
            // assert(0 <= cid < old(self).clients.len());
            // assert(old(self).view().free.contains(idx as nat));
            // assert(self.view().free == old(self).view().free.remove(idx as nat));
            // assume(self.view().clients[cid as int] == Client {
            //     resources: old(self).view().clients[cid as int].resources.insert(idx as nat),
            // });
            // // TODO: finish this proof
            // assume(ResourceModel::alloc(old(self)@, self@, cid as int, idx as nat));

            // // TODO: This proof needs to use ResourceModel::invariants
            // assume(forall|cid, i, j|
            //     0 <= cid < self.clients.len() && 0 <= i < self.clients[cid].indices.len() && 0 <= j
            //         < self.clients[cid].indices.len() && i != j ==> self.clients[cid].indices[i]
            //         != self.clients[cid].indices[j]);
            assume(false);
        }
        Frame4K(paddr)
    }

    fn dealloc(&mut self, cid: usize, rid: Frame4K) {
        let idx = self.find_client(cid).unwrap();
        let len = self.clients[idx].indices.len();

        // Find the index to remove
        let mut i = 0;
        while i < len
            invariant
                0 <= i <= len,
                0 <= idx < self.clients.len(),
                self.invariants(),
                self.clients[idx as int].indices.len() == len,
                forall|j: int|
                    #![auto]
                    0 <= j < i ==> self.clients[idx as int].indices[j].0 != rid.0,
            decreases len - i,
        {
            if self.clients[idx].indices[i].0.0 == rid.0.0 {
                break ;
            }
            i += 1;
        }

        // Index must be found
        proof {
            if i == len {
                assert(forall|j: int|
                    #![auto]
                    0 <= j < len ==> self.clients[idx as int].indices[j].0 != rid.0);
                assert(!self.clients[idx as int].indices.view().to_set().contains(rid));
                // Contradiction
                assert(false);
            }
            assert(i < len);
        }

        let mut client = self.clients[idx].clone();
        // TODO: why cloned != original?
        assume(client == self.clients[idx as int]);
        assert(i < self.clients[idx as int].indices.len());
        client.indices.swap_remove(i);
        self.clients[idx] = client;

        // Free in the backend allocator
        proof {
            // Prove preconditions
            assume(false);
        }
        self.allocator.dealloc(rid.0);

        proof {
            // TODO: finish this proof
            // assume(GlobalAllocatorModel::dealloc(old(self)@, self@, cid as nat, rid.0 as nat));
            // TODO: This proof needs to use ResourceModel::invariants
            assume(forall|cid, i, j|
                0 <= cid < self.clients.len() && 0 <= i < self.clients[cid].indices.len() && 0 <= j
                    < self.clients[cid].indices.len() && i != j ==> self.clients[cid].indices[i]
                    != self.clients[cid].indices[j]);
        }
    }

    fn add_client(&mut self, cid: usize) {
        self.clients.push(FrameAllocatorClient { id: cid, indices: Vec::new() });
        assume(false);
    }

    fn remove_client(&mut self, cid: usize) {
        // Free all resources allocated to this client
        let idx = self.find_client(cid).unwrap();
        let len = self.clients[idx].indices.len();
        let mut i = 0;
        while i < len
            invariant
                0 <= i <= len,
                0 <= idx < self.clients.len(),
                self.allocator.wf(),
                self.clients[idx as int].indices.len() == len,
            decreases len - i,
        {
            let rid = self.clients[idx].indices[i];
            proof {
                // Prove preconditions
                assume(false);
            }
            self.allocator.dealloc(rid.0);
            i += 1;
        }
        self.clients.swap_remove(idx);

        proof {
            // TODO: finish this proof
            assume(GlobalAllocatorModel::remove_client(old(self)@, self@, cid as nat));

            // TODO: This proof needs to use GlobalAllocatorModel::invariants
            assume(forall|cid, i, j|
                0 <= cid < self.clients.len() && 0 <= i < self.clients[cid].indices.len() && 0 <= j
                    < self.clients[cid].indices.len() && i != j ==> self.clients[cid].indices[i]
                    != self.clients[cid].indices[j]);

            assume(false);
        }
    }

    proof fn lemma_implies_invariants(self) {
    }
}

/// Collect free frames of a frame allocator into a set of physical addresses.
pub open spec fn free_frames_to_set<FA: FrameAllocator>(allocator: &FA) -> Set<nat> {
    Set::new(|i: nat| i < allocator.view().len() && allocator.view()[i as int]).map(
        |i: nat| (allocator.base().0 as usize + i * FA::spec_page_size()) as nat,
    )
}

} // verus!
