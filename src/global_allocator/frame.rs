//! Global Frame Allocator, implementing trait `GlobalAllocator`.
use super::{GlobalAllocator, GlobalAllocatorModel};
use crate::{address::addr::PAddr, bitmap_allocator::bitmap_trait::BitmapAllocator};
use vstd::{invariant, prelude::*};

verus! {

/// An allocator client manages a set of frames.
pub struct AllocatorClient {
    /// Client ID.
    pub id: usize,
    /// The set of frames allocated to this client.
    pub frames: Vec<usize>,
}

impl Clone for AllocatorClient {
    fn clone(&self) -> Self {
        Self { id: self.id, frames: self.frames.clone() }
    }
}

/// Global memory allocator implementation using a bitmap allocator as the backend.
pub struct GlobalBitmapAllocator<A> where A: BitmapAllocator {
    /// Base address of the memory region managed by the global allocator.
    pub base: PAddr,
    /// The backend bitmap allocator.
    pub allocator: A,
    /// Allocator clients.
    pub clients: Vec<AllocatorClient>,
}

impl<A> GlobalBitmapAllocator<A> where A: BitmapAllocator {
    /// If there exists a client with the given id.
    pub open spec fn has_client(&self, cid: usize) -> bool {
        exists|i| 0 <= i < self.clients.len() && #[trigger] self.clients[i].id == cid
    }

    /// Find the client with the given id, return its index.
    pub fn find_client(&self, cid: usize) -> (res: usize)
        requires
            self.has_client(cid),
        ensures
            0 <= res < self.clients.len() && self.clients[res as int].id == cid,
    {
        let mut i = 0;
        while i < self.clients.len()
            invariant
                0 <= i <= self.clients.len(),
                forall|j: int| #![auto] 0 <= j < i ==> self.clients[j].id != cid,
            decreases self.clients.len() - i,
        {
            if self.clients[i].id == cid {
                return i;
            }
            i += 1;
        }
        // Unreachable
        self.clients.len()
    }
}

impl<A> GlobalAllocator for GlobalBitmapAllocator<A> where A: BitmapAllocator {
    open spec fn frame_size(&self) -> nat {
        4096
    }

    open spec fn view(&self) -> GlobalAllocatorModel {
        GlobalAllocatorModel {
            free: free_frames_to_set(&self.allocator),
            clients: Map::new(
                |id| exists|i| 0 <= i < self.clients.len() && #[trigger] self.clients[i].id == id,
                |id|
                    {
                        let i: int = choose|i|
                            0 <= i < self.clients.len() && #[trigger] self.clients[i].id == id;
                        self.clients[i].frames.view().to_set().map(|frame: usize| frame as nat)
                    },
            ),
        }
    }

    open spec fn invariants(&self) -> bool {
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
        // No duplicate frames in each client.
        &&& forall|cid, i, j|
            0 <= cid < self.clients.len() && 0 <= i < self.clients[cid].frames.len() && 0 <= j
                < self.clients[cid].frames.len() && i != j ==> self.clients[cid].frames[i]
                != self.clients[cid].frames[j]
    }

    fn alloc(&mut self, cid: usize) -> (res: PAddr) {
        let alloc_res = self.allocator.alloc();
        proof {
            if alloc_res is None {
                // There must be free slots
                self.allocator.lemma_view_len_eq_cap_pages();
                assert(forall|j: int| 0 <= j < A::cap_pages() ==> !self.allocator.view()[j]);
                assert(free_frames_to_set(&self.allocator) === Set::empty());
                // Contradiction
            }
            assert(alloc_res is Some);
        }
        let paddr = alloc_res.unwrap();

        // index for &mut not supported, so we need to copy
        let idx = 0;
        // let client = self.clients[0].clone();
        // client.frames.push(Frame4K(paddr));
        // replace back
        // assume(0 <= idx < self.clients.len());
        // assume(client == self.clients[idx as int]);
        assume(self.clients.len() > 0);
        self.clients[0] = AllocatorClient { id: 0, frames: Vec::new() };

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
            //     0 <= cid < self.clients.len() && 0 <= i < self.clients[cid].frames.len() && 0 <= j
            //         < self.clients[cid].frames.len() && i != j ==> self.clients[cid].frames[i]
            //         != self.clients[cid].frames[j]);
            assume(false);
        }
        PAddr(0)  // placeholder

    }

    fn alloc_contiguous(&mut self, cid: usize, count: usize, align_log2: usize) -> (frame: PAddr) {
        PAddr(0)  // placeholder

    }

    fn dealloc(&mut self, cid: usize, frame: PAddr) {
        let idx = self.find_client(cid);
        let len = self.clients[idx].frames.len();
        let fid = frame.0 / Self::frame_size() as usize;

        // Find the index to remove
        let mut i = 0;
        while i < len
            invariant
                0 <= i <= len,
                0 <= idx < self.clients.len(),
                self.invariants(),
                self.clients[idx as int].frames.len() == len,
                forall|j: int| #![auto] 0 <= j < i ==> self.clients[idx as int].frames[j].0 != fid,
            decreases len - i,
        {
            if self.clients[idx].frames[i].0 == fid {
                break ;
            }
            i += 1;
        }

        // Index must be found
        proof {
            if i == len {
                assert(forall|j: int|
                    #![auto]
                    0 <= j < len ==> self.clients[idx as int].frames[j] != fid);
                assert(!self.clients[idx as int].frames.view().to_set().contains(fid));
                // Contradiction
                assert(false);
            }
            assert(i < len);
        }

        let mut client = self.clients[idx].clone();
        // TODO: why cloned != original?
        assume(client == self.clients[idx as int]);
        assert(i < self.clients[idx as int].frames.len());
        client.frames.swap_remove(i);
        self.clients[idx] = client;

        // Free in the backend allocator
        proof {
            // Prove preconditions
            assume(false);
        }
        self.allocator.dealloc(fid);

        proof {
            // TODO: finish this proof
            // assume(GlobalAllocatorModel::dealloc(old(self)@, self@, cid as nat, rid.0 as nat));
            // TODO: This proof needs to use ResourceModel::invariants
            assume(forall|cid, i, j|
                0 <= cid < self.clients.len() && 0 <= i < self.clients[cid].frames.len() && 0 <= j
                    < self.clients[cid].frames.len() && i != j ==> self.clients[cid].frames[i]
                    != self.clients[cid].frames[j]);
        }
    }

    fn add_client(&mut self, cid: usize) {
        self.clients.push(AllocatorClient { id: cid, frames: Vec::new() });
        assume(false);
    }

    fn remove_client(&mut self, cid: usize) {
        // Free all resources allocated to this client
        let idx = self.find_client(cid);
        let len = self.clients[idx].frames.len();
        let mut i = 0;
        while i < len
            invariant
                0 <= i <= len,
                0 <= idx < self.clients.len(),
                self.allocator.wf(),
                self.clients[idx as int].frames.len() == len,
            decreases len - i,
        {
            let rid = self.clients[idx].frames[i];
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
                0 <= cid < self.clients.len() && 0 <= i < self.clients[cid].frames.len() && 0 <= j
                    < self.clients[cid].frames.len() && i != j ==> self.clients[cid].frames[i]
                    != self.clients[cid].frames[j]);

            assume(false);
        }
    }

    proof fn lemma_implies_invariants(self) {
    }
}

// /// Collect free frames of a frame allocator into a set of physical addresses.
// pub open spec fn free_frames_to_set<A: BitmapAllocator>(allocator: &A) -> Set<nat> {
//     Set::new(|i: nat| i < allocator.view().len() && allocator.view()[i as int]).map(
//         |i: nat| (allocator.base().0 as usize + i * A::spec_page_size()) as nat,
//     )
// }
} // verus!
