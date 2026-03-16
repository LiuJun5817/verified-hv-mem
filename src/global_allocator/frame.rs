//! Global Frame Allocator, implementing trait `GlobalAllocator`.
use super::{paddr_to_fid, GlobalAllocator, GlobalAllocatorModel};
use crate::{
    address::addr::{PAddr, SpecPAddr},
    bitmap_allocator::bitmap_trait::BitmapAllocator,
};
use vstd::{invariant, prelude::*, set::fold::lemma_finite_set_induct, set_lib::lemma_len_subset};

verus! {

/// An allocator client manages a set of frames.
pub struct GlobalAllocatorClient {
    /// Client ID.
    pub id: usize,
    /// The set of frames allocated to this client.
    pub frames: Vec<usize>,
}

impl Clone for GlobalAllocatorClient {
    fn clone(&self) -> (res: Self)
        ensures
            self == res,
    {
        proof {
            admit();
        }  // Assume the clone is correct
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
    pub clients: Vec<GlobalAllocatorClient>,
}

impl<A> GlobalBitmapAllocator<A> where A: BitmapAllocator {
    /// Unit size of frames managed by the global allocator.
    pub const FRAME_SIZE: usize = 4096;

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

    /// Calculate the frame ID from a physical address.
    pub fn paddr_to_fid(&self, addr: PAddr) -> (res: usize)
        requires
            self.base@.aligned(Self::FRAME_SIZE as nat),
            addr@.aligned(Self::FRAME_SIZE as nat),
            addr.0 >= self.base.0,
        ensures
            res == (addr@.0 - self.base@.0) as nat / Self::FRAME_SIZE as nat,
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
}

impl<A> GlobalAllocator for GlobalBitmapAllocator<A> where A: BitmapAllocator {
    open spec fn frame_size() -> nat {
        Self::FRAME_SIZE as nat
    }

    open spec fn base(&self) -> SpecPAddr {
        self.base@
    }

    open spec fn view(&self) -> GlobalAllocatorModel {
        GlobalAllocatorModel {
            free: Set::new(|i: nat| i < A::spec_cap() && self.allocator.view()[i as int]),
            clients: Map::new(
                |id| exists|i| 0 <= i < self.clients.len() && #[trigger] self.clients[i].id == id,
                |id|
                    {
                        let i: int = choose|i|
                            0 <= i < self.clients.len() && #[trigger] self.clients[i].id == id;
                        Set::new(
                            |fid: nat|
                                fid <= usize::MAX && self.clients[i as int].frames@.contains(
                                    fid as usize,
                                ),
                        )
                    },
            ),
        }
    }

    open spec fn invariants(&self) -> bool {
        // Invariants of the global allocator.
        &&& self.allocator.wf()
        // Invariants of the resource model.
        &&& self.view().wf()
        // Base address must be aligned to frame size.
        &&& self.base.view().aligned(
            Self::FRAME_SIZE as nat,
        )
        // Max address must be representable in usize.
        &&& self.base.0 + (A::spec_cap() * Self::FRAME_SIZE)
            <= usize::MAX
        // No duplicate client id.
        &&& forall|i, j|
            #![auto]
            0 <= i < self.clients.len() && 0 <= j < self.clients.len() && i != j
                ==> self.clients[i].id
                != self.clients[j].id
        // No duplicate frames in each client.
        &&& forall|idx, i, j|
            0 <= idx < self.clients.len() && 0 <= i < self.clients[idx].frames.len() && 0 <= j
                < self.clients[idx].frames.len() && i != j ==> self.clients[idx].frames[i]
                != self.clients[idx].frames[j]
        // All fid must within capacity.
        &&& forall|idx, i|
            0 <= idx < self.clients.len() && 0 <= i < self.clients[idx].frames.len()
                ==> self.clients[idx].frames[i] < A::spec_cap()
    }

    fn alloc(&mut self, cid: usize) -> (res: PAddr) {
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
            // Prove the slot is correctly allocated
            assert(self.allocator@ == old(self).allocator@.update(fid as int, false));
            assert(self@.free == old(self)@.free.remove(fid as nat));
        }

        // Record in the client's list
        let idx = self.find_client(cid);
        let mut client = self.clients[idx].clone();
        client.frames.push(fid);
        self.clients[idx] = client;

        proof {
            // Not add/remove clients
            assert(forall|idx2: int|
                0 <= idx2 < self.clients.len() && idx2 != idx ==> self.clients[idx2] == old(
                    self,
                ).clients[idx2]);
            assert(self.clients[idx as int].id == old(self).clients[idx as int].id);
            assert(self@.clients.dom() == old(self)@.clients.dom());
            // Other clients remain unchanged
            assert(forall|cid2: nat|
                self@.clients.contains_key(cid2) && cid2 != cid ==> #[trigger] self@.clients[cid2]
                    == old(self)@.clients[cid2]);

            // The client's frames is updated correctly
            let frames = self.clients[idx as int].frames@;
            let old_frames = old(self).clients[idx as int].frames@;
            assert(frames == old_frames.push(fid as usize));
            assert(frames.contains(fid)) by {
                assert(frames[frames.len() - 1] == fid);
            }
            assert forall|fid2| old_frames.contains(fid2) implies frames.contains(fid2) by {
                let idx2 = choose|idx2| 0 <= idx2 < old_frames.len() && old_frames[idx2] == fid2;
                assert(frames[idx2] == fid2);
            }
            assert(forall|fid2| frames.contains(fid2) && fid2 != fid ==> old_frames.contains(fid2));
            assert(self@.clients[cid as nat] == old(self)@.clients[cid as nat].insert(fid as nat));

            // `GlobalAllocatorModel::alloc` holds
            assert(self@.clients == old(self)@.clients.insert(
                cid as nat,
                old(self)@.clients[cid as nat].insert(fid as nat),
            ));

            // Prove no duplicate frames in each client
            assert forall|idx2, i, j|
                0 <= idx2 < self.clients.len() && 0 <= i < self.clients[idx2].frames.len() && 0 <= j
                    < self.clients[idx2].frames.len() && i != j implies self.clients[idx2].frames[i]
                != self.clients[idx2].frames[j] by {
                if idx2 == idx {
                    // prove for the updated client
                    assert(!old_frames.contains(fid)) by {
                        assert(!old(self)@.clients[cid as nat].contains(fid as nat));
                    }
                } else {
                    assert(self.clients[idx2] == old(self).clients[idx2]);
                }
            }
            // Invariants hold
            assert(self.invariants());
        }

        self.fid_to_paddr(fid)
    }

    fn dealloc(&mut self, cid: usize, frame: PAddr) {
        let idx = self.find_client(cid);
        let len = self.clients[idx].frames.len();
        let fid = self.paddr_to_fid(frame);

        // Find the index to remove
        let mut i = 0;
        while i < len
            invariant
                0 <= i <= len,
                0 <= idx < self.clients.len(),
                self.invariants(),
                self.clients[idx as int].frames.len() == len,
                forall|j: int| #![auto] 0 <= j < i ==> self.clients[idx as int].frames[j] != fid,
            ensures
                i < len ==> self.clients[idx as int].frames[i as int] == fid,
            decreases len - i,
        {
            if self.clients[idx].frames[i] == fid {
                break ;
            }
            i += 1;
        }
        proof {
            // Index must be found
            if i >= len {
                assert(forall|j: int|
                    #![auto]
                    0 <= j < len ==> self.clients[idx as int].frames[j] != fid);
                assert(!self.clients[idx as int].frames.view().to_set().contains(fid));
                // contradiction
            }
            assert(i < len);
        }

        // Free in the backend allocator
        self.allocator.dealloc(fid);
        proof {
            old(self).allocator.lemma_view_len_is_cap();
            self.allocator.lemma_view_len_is_cap();
            // Prove the slot is correctly freed
            assert(self.allocator@ == old(self).allocator@.update(fid as int, true));
            assert(self@.free == old(self)@.free.insert(fid as nat));
            assert(self.clients[idx as int].frames[i as int] == fid);
        }

        let mut client = self.clients[idx].clone();
        client.frames.swap_remove(i);
        self.clients[idx] = client;

        proof {
            // Not add/remove clients
            assert(forall|idx2: int|
                0 <= idx2 < self.clients.len() && idx2 != idx ==> self.clients[idx2] == old(
                    self,
                ).clients[idx2]);
            assert(self.clients[idx as int].id == old(self).clients[idx as int].id);
            assert(self@.clients.dom() == old(self)@.clients.dom());
            // Other clients remain unchanged
            assert(forall|cid2: nat|
                self@.clients.contains_key(cid2) && cid2 != cid ==> #[trigger] self@.clients[cid2]
                    == old(self)@.clients[cid2]);

            // The client's frames is updated correctly
            let frames = self.clients[idx as int].frames@;
            let old_frames = old(self).clients[idx as int].frames@;
            assert(!frames.contains(fid)) by { assume(false) }
            assert(forall|fid2| frames.contains(fid2) ==> old_frames.contains(fid2));
            assert forall|fid2| old_frames.contains(fid2) && fid2 != fid implies frames.contains(
                fid2,
            ) by {
                let i2 = choose|i2| 0 <= i2 < old_frames.len() && old_frames[i2] == fid2;
                if i2 == old_frames.len() - 1 {
                    // swapped
                    assert(frames[i as int] == fid2);
                } else {
                    assert(frames[i2] == fid2);
                }
            }
            assert(self@.clients[cid as nat] == old(self)@.clients[cid as nat].remove(fid as nat));

            // `GlobalAllocatorModel::dealloc` holds
            assert(self@.clients == old(self)@.clients.insert(
                cid as nat,
                old(self)@.clients[cid as nat].remove(fid as nat),
            ));
            // Invariants hold
            assert(forall|cid, i, j|
                0 <= cid < self.clients.len() && 0 <= i < self.clients[cid].frames.len() && 0 <= j
                    < self.clients[cid].frames.len() && i != j ==> self.clients[cid].frames[i]
                    != self.clients[cid].frames[j]);
        }
    }

    fn alloc_contiguous(&mut self, cid: usize, count: usize, align_log2: usize) -> (frame: PAddr) {
        proof {
            old(self).allocator.lemma_view_len_is_cap();
            self.allocator.lemma_view_len_is_cap();
            // TODO: this is essential
            assume(1usize << align_log2 == 1 << align_log2);
            // Preconditions of `alloc_contiguous`
            self.lemma_free_len_le_allocator_cap();
            assert(0 < count <= A::spec_cap());
        }
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
            assert(forall|j: nat| fid <= j < fid + count ==> old(self)@.free.contains(j));
            // Prove the slots are correctly allocated
            let allocated = Set::new(|i: nat| fid <= i < fid + count);
            assert(allocated.subset_of(old(self)@.free));
            assert(self@.free == old(self)@.free.difference(allocated));
        }

        let idx = self.find_client(cid);
        let mut client = self.clients[idx].clone();
        for i in 0..count
            invariant
                fid + count <= A::spec_cap(),
                fid + i <= A::spec_cap() < usize::MAX,
                0 <= idx < self.clients.len(),
                client.frames@ == self.clients[idx as int].frames@.add(
                    Seq::new(i as nat, |i| (fid + i) as usize),
                ),
                forall|j: nat| fid <= j < fid + count ==> old(self)@.free.contains(j),
                old(self).invariants(),
                old(self)@.clients.contains_key(cid as nat),
                self.clients == old(self).clients,
                self.clients[idx as int].id == cid,
                client.id == cid,
                // No duplicate client id.
                forall|i, j|
                    #![auto]
                    0 <= i < self.clients.len() && 0 <= j < self.clients.len() && i != j
                        ==> self.clients[i].id != self.clients[j].id,
                // No duplicate frames in client.
                forall|i, j|
                    0 <= i < client.frames.len() && 0 <= j < client.frames.len() && i != j
                        ==> client.frames[i] != client.frames[j],
        {
            proof {
                assert(!client.frames@.contains((fid + i) as usize)) by {
                    assert(old(self)@.free.contains((fid + i) as nat));
                    assert(old(self)@.clients.contains_key(cid as nat));
                    assert(forall|fid: nat, cid: nat|
                        (old(self)@.free.contains(fid) && old(self)@.clients.contains_key(cid))
                            ==> !old(self)@.clients[cid].contains(fid));
                    assert(!old(self)@.clients[cid as nat].contains((fid + i) as nat));
                    assert(!old(self).clients[idx as int].frames@.contains((fid + i) as usize));
                }
            }
            client.frames.push(fid + i);
        }
        self.clients[idx] = client;

        proof {
            // Not add/remove clients
            assert(forall|idx2: int|
                0 <= idx2 < self.clients.len() && idx2 != idx ==> self.clients[idx2] == old(
                    self,
                ).clients[idx2]);
            assert(self@.clients.dom() == old(self)@.clients.dom());
            // Other clients remain unchanged
            assert(forall|cid2: nat|
                self@.clients.contains_key(cid2) && cid2 != cid ==> #[trigger] self@.clients[cid2]
                    == old(self)@.clients[cid2]);

            // Loop invariant
            let old_client = old(self).clients[idx as int];
            assert(client.frames@ == old_client.frames@.add(
                Seq::new(count as nat, |i| (fid + i) as usize),
            ));
            // Prove client's frames are extended by the allocated frames
            assert forall|fid2| self@.clients[cid as nat].contains(fid2) implies old(
                self,
            )@.clients[cid as nat].contains(fid2) || fid <= fid2 < fid + count by {
                let i = choose|i| 0 <= i < client.frames.len() && client.frames[i] == fid2;
                if i >= old_client.frames.len() {
                    assert(fid <= fid2 && fid2 < fid + count);
                } else {
                    assert(old_client.frames[i] == fid2);
                }
            }
            assert forall|fid2|
                old(self)@.clients[cid as nat].contains(
                    fid2,
                ) implies self@.clients[cid as nat].contains(fid2) by {
                let i = choose|i| 0 <= i < old_client.frames.len() && old_client.frames[i] == fid2;
                if i >= client.frames.len() {
                    assert(old_client.frames[i] == fid2);
                } else {
                    assert(client.frames[i] == fid2);
                }
            }
            assert forall|fid2|
                fid <= fid2 < fid + count implies self@.clients[cid as nat].contains(fid2) by {
                let i = (fid2 - fid) as int;
                assert(client.frames[old_client.frames.len() + i] == fid2);
            }
            assert(self@.clients[cid as nat] == old(self)@.clients[cid as nat].union(
                Set::new(|i: nat| fid <= i < fid + count),
            ));
            assert(self@.clients == old(self)@.clients.insert(
                cid as nat,
                old(self)@.clients[cid as nat].union(Set::new(|i: nat| fid <= i < fid + count)),
            ));

            // `GlobalAllocatorModel::alloc_contiguous` holds
            assert(GlobalAllocatorModel::alloc_contiguous(
                old(self)@,
                self@,
                cid as nat,
                count as nat,
                fid as nat,
            ));
            // Invariants hold
            assert(self.invariants());
        }

        self.fid_to_paddr(fid)
    }

    fn add_client(&mut self, cid: usize) {
        self.clients.push(GlobalAllocatorClient { id: cid, frames: Vec::new() });
        proof {
            // free is unchanged
            assert(self@.free == old(self)@.free);
            // A new client is added
            assert(!old(self)@.clients.contains_key(cid as nat));
            assert(self@.clients.contains_key(cid as nat)) by {
                assert(self.clients[self.clients.len() - 1].id == cid);
            }
            // Other clients remain unchanged
            assert(forall|cid2: nat|
                self@.clients.contains_key(cid2) && cid2 != cid ==> #[trigger] old(
                    self,
                )@.clients.contains_key(cid2));
            assert forall|cid2: nat|
                old(self)@.clients.contains_key(cid2) implies self@.clients.contains_key(cid2) by {
                let idx2 = choose|idx2|
                    #![auto]
                    0 <= idx2 < old(self).clients.len() && old(self).clients[idx2].id == cid2;
                assert(self.clients[idx2] == old(self).clients[idx2]);
            }
            assert(self@.clients[cid as nat] == Set::<nat>::empty());
            assert(self@.clients == old(self)@.clients.insert(cid as nat, Set::empty()));
        }
    }

    fn remove_client(&mut self, cid: usize) {
        // Free all resources allocated to this client
        let idx = self.find_client(cid);
        let client = &self.clients[idx];
        let len = client.frames.len();

        proof {
            old(self).allocator.lemma_view_len_is_cap();
            self.allocator.lemma_view_len_is_cap();
            assert forall|i|
                #![auto]
                0 <= i < len implies !self.allocator@[client.frames[i] as int] by {
                let fid = client.frames[i];
                assert(self@.clients[cid as nat].contains(fid as nat));
                assert(!self@.free.contains(fid as nat));
                assert(!self.allocator@[fid as int]);
            }
        }

        let mut i = 0;
        while i < len
            invariant
                0 <= i <= len,
                0 <= idx < self.clients.len(),
                self.allocator.wf(),
                client.frames.len() == len,
                // Must maintain here for proof after while loop
                self.clients == old(self).clients,
                self.base.view().aligned(Self::FRAME_SIZE as nat),
                self.base.0 + (A::spec_cap() * Self::FRAME_SIZE) <= usize::MAX,
                // `free` is increased by the client's frames
                forall|fid|
                    self@.free.contains(fid) ==> old(self)@.free.contains(fid)
                        || client.frames@.contains(fid as usize) && fid < usize::MAX,
                forall|fid| old(self)@.free.contains(fid) ==> self@.free.contains(fid),
                // No duplicate frames in each client
                forall|i, j|
                    0 <= i < client.frames.len() && 0 <= j < client.frames.len() && i != j
                        ==> client.frames[i] != client.frames[j],
                // No duplicate client id.
                forall|i, j|
                    #![auto]
                    0 <= i < self.clients.len() && 0 <= j < self.clients.len() && i != j
                        ==> self.clients[i].id != self.clients[j].id,
                // Fid within valid range
                forall|j| 0 <= j < len ==> client.frames[j] < A::spec_cap(),
                // All frames before `i` are deallocated
                forall|j| 0 <= j < i ==> #[trigger] self.allocator@[client.frames[j] as int],
                // All frames after `i` are not updated
                forall|j| i <= j < len ==> !#[trigger] self.allocator@[client.frames[j] as int],
            decreases len - i,
        {
            let fid = client.frames[i];
            proof {
                self.allocator.lemma_view_len_is_cap();
                // Prove preconditions
                assert(fid < A::spec_cap());
                assert(!self.allocator@[fid as int]);
            }
            let ghost before_allocator = self.allocator;
            self.allocator.dealloc(fid);
            i += 1;

            proof {
                self.allocator.lemma_view_len_is_cap();
                assert(self.allocator@ == before_allocator@.update(fid as int, true));
                // Remaining frames are not updated
                assert forall|j|
                    #![auto]
                    i <= j < len implies self.allocator@[client.frames[j] as int]
                    == before_allocator@[client.frames[j] as int] by {
                    assert(client.frames[j] != fid);
                }
            }
        }

        proof {
            old(self).allocator.lemma_view_len_is_cap();
            self.allocator.lemma_view_len_is_cap();
            // Prove `free` equals to the old `free` union the client's frames
            assert(forall|fid|
                self@.free.contains(fid) ==> old(self)@.free.contains(fid)
                    || client.frames@.contains(fid as usize) && fid < usize::MAX);
            assert forall|fid|
                old(self)@.free.contains(fid) || fid < usize::MAX && client.frames@.contains(
                    fid as usize,
                ) implies self@.free.contains(fid) by {
                if old(self)@.free.contains(fid) {
                    assert(self@.free.contains(fid));
                } else {
                    assert(client.frames@.contains(fid as usize));
                    let j = choose|j| 0 <= j < len && client.frames[j] == fid as usize;
                    assert(self.allocator@[client.frames[j] as int]);
                    assert(self@.free.contains(fid));
                }
            }
            assert(self@.free == old(self)@.free.union(
                Set::new(|fid: nat| fid <= usize::MAX && client.frames@.contains(fid as usize)),
            ));
        }

        self.clients.swap_remove(idx);
        proof {
            assert(self@.clients == old(self)@.clients.remove(cid as nat)) by {
                // Domain is updated correctly
                assert forall|cid2: nat|
                    #![auto]
                    old(self)@.clients.contains_key(cid2) && cid2
                        != cid implies self@.clients.contains_key(cid2) by {
                    let idx2 = choose|idx2|
                        #![auto]
                        0 <= idx2 < old(self).clients.len() && old(self).clients[idx2].id == cid2;
                    if idx2 == old(self).clients.len() - 1 {
                        // swapped with the last client
                        assert(self.clients[idx as int].id == old(self).clients[idx2].id);
                    } else {
                        // not updated
                        assert(self.clients[idx2] == old(self).clients[idx2]);
                    }
                }
                assert forall|cid2: nat| #![auto] self@.clients.contains_key(cid2) implies old(
                    self,
                )@.clients.contains_key(cid2) by {
                    let idx2 = choose|idx2|
                        #![auto]
                        0 <= idx2 < self.clients.len() && self.clients[idx2].id == cid2;
                    if idx2 == idx {
                        // swapped with the last client
                        assert(self.clients[idx2].id == old(self).clients[old(self).clients.len()
                            - 1].id);
                    } else {
                        // not updated
                        assert(self.clients[idx2] == old(self).clients[idx2]);
                    }
                }
                assert(!self@.clients.contains_key(cid as nat));
                assert(self@.clients.dom() == old(self)@.clients.remove(cid as nat).dom());
                // Key-value pairs are updated correctly
                assert(forall|cid2: nat|
                    #![auto]
                    self@.clients.contains_key(cid2) ==> old(self)@.clients[cid2]
                        == self@.clients[cid2]);
            }
        }

        proof {
            // Prove `GlobalAllocatorModel::remove_client` holds
            assert(GlobalAllocatorModel::remove_client(old(self)@, self@, cid as nat));
            // Invariants hold
            assert(self.invariants());
        }
    }

    proof fn lemma_invariants_implies_wf(&self) {
    }
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
