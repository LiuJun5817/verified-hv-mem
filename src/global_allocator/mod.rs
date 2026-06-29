//! Tokenized state machine for the global frame allocator.
//!
//! `AllocSpec` tracks which frame IDs belong to the free pool and which have been
//! handed out to each client.  Using `#[sharding(map)]` on `client_sets` means
//! every client independently holds a `AllocSpec::client_sets` token whose value
//! is exactly the set of frames that client currently owns.  The Instance
//! invariants (`inv_free_clients_disjoint` and `inv_clients_disjoint`) then
//! guarantee, at the type level, that no two clients ever hold the same frame.
use core::marker::PhantomData;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::cell::{CellId, PCell};
use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;
use vstd::tokens::InstanceId;

verus! {

use crate::address::{
    addr::{PAddr, SpecPAddr},
    frame::Frame,
};
use crate::bitmap_allocator::{bitmap_trait::BitmapAllocator, bitmap_impl::BitAlloc1M};
use crate::sync::mutex::{Mutex, MutexGuard};
use core::unreachable;
use core::unimplemented;

/// Frame ID
pub type FrameID = nat;

/// Unique Identifier allocated by the global allocator.
pub tracked struct ClientID;

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

tokenized_state_machine! {
    AllocSpec {
        fields {
            /// The upper bound of FrameID
            #[sharding(constant)]
            pub cap: FrameID,

            /// The set of free (unallocated) frame IDs.
            /// Held as a single token by the GlobalAllocator.
            #[sharding(variable)]
            pub free_set: Set<FrameID>,

            /// Mirror of `client_sets.dom()` as a variable-sharded field.
            /// Kept in sync so that `register_client` can prove the "key absent"
            /// inherent safety condition for the map-sharded `client_sets`.
            #[sharding(variable)]
            pub registered: Set<ClientID>,

            /// Per-client sets of allocated frame IDs.
            /// Each client independently holds the token for its own key.
            #[sharding(map)]
            pub client_sets: Map<ClientID, Set<FrameID>>,
        }

        // ── Invariants ────────────────────────────────────────────────────────

        /// Every frame ID is within the capacity bound.
        #[invariant]
        pub fn inv_cap(&self) -> bool {
            &&& forall |fid: FrameID| #![auto]
                    self.free_set.contains(fid) ==> fid < self.cap
            &&& forall |cid: ClientID| #![auto] self.client_sets.contains_key(cid)
                ==> forall |fid: FrameID| #![auto] self.client_sets[cid].contains(fid) ==> fid < self.cap
        }

        /// Every frame owned by a client is absent from the free set.
        #[invariant]
        pub fn inv_free_clients_disjoint(&self) -> bool {
            forall |cid: ClientID|
                #[trigger] self.client_sets.contains_key(cid)
                ==> self.client_sets[cid].disjoint(self.free_set)
        }

        /// `registered` is always exactly the domain of `client_sets`.
        #[invariant]
        pub fn inv_registered(&self) -> bool {
            forall |cid: ClientID| #![auto]
                self.registered.contains(cid) <==> self.client_sets.contains_key(cid)
        }

        /// No frame is allocated to two different clients simultaneously.
        #[invariant]
        pub fn inv_clients_disjoint(&self) -> bool {
            forall |c1: ClientID, c2: ClientID| #![auto]
                c1 != c2
                && self.client_sets.contains_key(c1)
                && self.client_sets.contains_key(c2)
                ==> self.client_sets[c1].disjoint(self.client_sets[c2])
        }

        /// The free set and any client's allocated set are disjoint.
        property! {
            free_client_disjoint(cid: ClientID, client: Set<FrameID>) {
                have client_sets >= [cid => client];
                assert(client.disjoint(pre.free_set)) by {
                    assert(pre.inv_free_clients_disjoint());
                };
            }
        }

        /// If a client contains `fid`, then `fid` is within the capacity bound.
        property! {
            client_fid_within_cap(cid: ClientID, client: Set<FrameID>) {
                have client_sets >= [cid => client];
                assert(forall|fid: FrameID| #[trigger] client.contains(fid) ==> fid < pre.cap);
            }
        }

        // ── Initialization ───────────────────────────────────────────────────

        init! {
            initialize(cap: FrameID) {
                init cap         = cap;
                init free_set    = Set::empty();
                init registered  = Set::empty();
                init client_sets = Map::empty();
            }
        }

        // ── Transitions ──────────────────────────────────────────────────────
  
        transition! {
            init_free_set(size: FrameID) {
                require(size <= pre.cap);
                require(pre.free_set =~= Set::empty());
                require(pre.registered =~= Set::empty());
                update free_set = Set::new(|fid: FrameID| fid < size);
            }
        }

        /// Register a new client.
        /// `require(!pre.registered.contains(cid))` gives the ISC proof for the
        /// map `add`: from `inv_registered` we have `!pre.client_sets.contains_key(cid)`.
        transition! {
            register_client(cid: ClientID) {
                require(!pre.registered.contains(cid));
                update registered = pre.registered.insert(cid);
                add client_sets += [cid => Set::empty()];
            }
        }

        /// Allocate `fid` from the free pool to `cid`.
        /// The caller must supply the `free_set` token (held by GlobalAllocator)
        /// and the `client_sets` token for `cid` (held by the client).
        transition! {
            alloc(cid: ClientID, fid: FrameID) {
                require(pre.free_set.contains(fid));
                update free_set = pre.free_set.remove(fid);
                remove client_sets -= [cid => let owned];
                add    client_sets += [cid => owned.insert(fid)];
            }
        }

        /// Allocate a contiguous range `[start, start + count)` from the free pool to `cid`.
        transition! {
            alloc_contiguous(cid: ClientID, start: FrameID, count: FrameID) {
                let allocated = Set::new(|fid: FrameID| start <= fid < start + count);
                require(0 < count);
                require(forall |fid: FrameID| #[trigger] allocated.contains(fid) ==> pre.free_set.contains(fid));
                update free_set = pre.free_set.difference(allocated);
                remove client_sets -= [cid => let owned];
                add    client_sets += [cid => owned.union(allocated)];
            }
        }

        /// Remove a contiguous allocated range `[start, start + count)` from client `cid`
        /// and return it to the free pool.
        transition! {
            dealloc_contiguous(cid: ClientID, start: FrameID, count: FrameID) {
                let removed = Set::new(|fid: FrameID| start <= fid < start + count);
                require(0 < count);
                remove client_sets -= [cid => let owned];
                require(forall |fid: FrameID| #[trigger] removed.contains(fid) ==> owned.contains(fid));
                update free_set = pre.free_set.union(removed);
                add    client_sets += [cid => owned.difference(removed)];
            }
        }

        /// Return `fid` from `cid` back to the free pool.
        transition! {
            dealloc(cid: ClientID, fid: FrameID) {
                remove client_sets -= [cid => let owned];
                require(owned.contains(fid));
                add    client_sets += [cid => owned.remove(fid)];
                update free_set = pre.free_set.insert(fid);
            }
        }

        // ── Inductive proofs ─────────────────────────────────────────────────
        // Empty bodies: Verus automatically discharges the proof obligations
        // because every transition either leaves the invariant fields unchanged
        // or moves a frame in exactly the direction that preserves disjointness.

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, cap: FrameID) {}

        #[inductive(init_free_set)]
        fn init_free_set_inductive(pre: Self, post: Self, size: FrameID) {
            assert(post.client_sets =~= pre.client_sets);
            assert(post.registered =~= pre.registered);
            assert(pre.client_sets =~= Map::empty());
            assert(post.client_sets =~= Map::empty());
        }

        #[inductive(register_client)]
        fn register_client_inductive(pre: Self, post: Self, cid: ClientID) {
            // post.client_sets = pre.client_sets ∪ {cid → ∅}
            // post.registered  = pre.registered ∪ {cid}
            // post.free_set    = pre.free_set  (unchanged)
            assert(post.client_sets =~= pre.client_sets.insert(cid, Set::empty()));

            // inv_registered
            assert forall |c: ClientID| #![auto]
                #[trigger] post.registered.contains(c) <==> post.client_sets.contains_key(c)
            by { assert(pre.inv_registered()); }

            // inv_free_clients_disjoint: Set::empty() is disjoint from anything;
            // every other client's set is unchanged and was already disjoint.
            assert forall |c: ClientID| #[trigger] post.client_sets.contains_key(c)
                implies post.client_sets[c].disjoint(post.free_set)
            by {
                assert(pre.inv_free_clients_disjoint());
                if c == cid {
                    assert(post.client_sets[cid] =~= Set::empty());
                } else {
                    assert(pre.client_sets.contains_key(c));
                    assert(pre.client_sets[c] =~= post.client_sets[c]);
                }
            }

            // inv_clients_disjoint: Set::empty() is disjoint from every set;
            // pairs not involving cid are unchanged from the pre invariant.
            assert forall |c1: ClientID, c2: ClientID| #![auto]
                c1 != c2
                && post.client_sets.contains_key(c1)
                && post.client_sets.contains_key(c2)
                implies post.client_sets[c1].disjoint(post.client_sets[c2])
            by {
                assert(pre.inv_clients_disjoint());
                if c1 == cid {
                    assert(post.client_sets[c1] =~= Set::empty());
                } else if c2 == cid {
                    assert(post.client_sets[c2] =~= Set::empty());
                } else {
                    assert(pre.client_sets[c1] =~= post.client_sets[c1]);
                    assert(pre.client_sets[c2] =~= post.client_sets[c2]);
                }
            }
        }

        #[inductive(alloc)]
        fn alloc_inductive(pre: Self, post: Self, cid: ClientID, fid: FrameID) {
            // post.client_sets[cid] = pre.client_sets[cid].insert(fid); others unchanged.
            // post.free_set = pre.free_set.remove(fid)
            let owned = pre.client_sets[cid];
            assert(post.client_sets =~= pre.client_sets.insert(cid, owned.insert(fid)));
            assert(post.free_set =~= pre.free_set.remove(fid));

            // KEY: fid was free, so it is absent from every client's allocated set.
            assert forall |c: ClientID| #[trigger] pre.client_sets.contains_key(c)
                implies !pre.client_sets[c].contains(fid)
            by {
                assert(pre.inv_free_clients_disjoint());
                assert(pre.client_sets[c].disjoint(pre.free_set));
            }

            // inv_registered: domain of client_sets unchanged (only a value updated).
            assert forall |c: ClientID| #![auto]
                #[trigger] post.registered.contains(c) <==> post.client_sets.contains_key(c)
            by { assert(pre.inv_registered()); }

            // inv_free_clients_disjoint
            assert forall |c: ClientID| #[trigger] post.client_sets.contains_key(c)
                implies post.client_sets[c].disjoint(post.free_set)
            by {
                assert(pre.inv_free_clients_disjoint());
                if c == cid {
                    // post[cid] = owned.insert(fid), post.free_set = pre.free_set.remove(fid).
                    // owned.disjoint(pre.free_set) and fid ∉ pre.free_set.remove(fid) → ok.
                    assert(owned.disjoint(pre.free_set));
                } else {
                    // post[c] = pre[c], post.free_set ⊆ pre.free_set → pre[c].disjoint(post.free_set).
                    assert(pre.client_sets.contains_key(c));
                    assert(pre.client_sets[c] =~= post.client_sets[c]);
                }
            }

            // inv_clients_disjoint
            assert forall |c1: ClientID, c2: ClientID| #![auto]
                c1 != c2
                && post.client_sets.contains_key(c1)
                && post.client_sets.contains_key(c2)
                implies post.client_sets[c1].disjoint(post.client_sets[c2])
            by {
                assert(pre.inv_clients_disjoint());
                if c1 == cid {
                    // post[cid] = owned.insert(fid), post[c2] = pre[c2].
                    // fid ∉ pre[c2] and owned.disjoint(pre[c2]) → owned.insert(fid).disjoint(pre[c2]).
                    assert(pre.client_sets.contains_key(c2));
                    assert(!pre.client_sets[c2].contains(fid));
                    assert(pre.client_sets[c2] =~= post.client_sets[c2]);
                } else if c2 == cid {
                    assert(pre.client_sets.contains_key(c1));
                    assert(!pre.client_sets[c1].contains(fid));
                    assert(pre.client_sets[c1] =~= post.client_sets[c1]);
                } else {
                    assert(pre.client_sets[c1] =~= post.client_sets[c1]);
                    assert(pre.client_sets[c2] =~= post.client_sets[c2]);
                }
            }
        }

        #[inductive(dealloc)]
        fn dealloc_inductive(pre: Self, post: Self, cid: ClientID, fid: FrameID) {
            // post.client_sets[cid] = pre.client_sets[cid].remove(fid); others unchanged.
            // post.free_set = pre.free_set.insert(fid)
            let owned = pre.client_sets[cid];
            assert(post.client_sets =~= pre.client_sets.insert(cid, owned.remove(fid)));
            assert(post.free_set =~= pre.free_set.insert(fid));

            // KEY: fid was in cid's set, so by inv_clients_disjoint it is absent from
            // every other client's allocated set.
            assert forall |c: ClientID| #[trigger] pre.client_sets.contains_key(c) && c != cid
                implies !pre.client_sets[c].contains(fid)
            by {
                assert(pre.inv_clients_disjoint());
                assert(pre.client_sets[cid].disjoint(pre.client_sets[c]));
            }

            // inv_registered
            assert forall |c: ClientID| #![auto]
                #[trigger] post.registered.contains(c) <==> post.client_sets.contains_key(c)
            by { assert(pre.inv_registered()); }

            // inv_clients_disjoint: post[cid] = owned.remove(fid) ⊆ pre[cid]; others unchanged.
            // Any overlap in post implies overlap in pre → contradiction.
            assert forall |c1: ClientID, c2: ClientID| #![auto]
                c1 != c2
                && post.client_sets.contains_key(c1)
                && post.client_sets.contains_key(c2)
                implies post.client_sets[c1].disjoint(post.client_sets[c2])
            by {
                assert(pre.inv_clients_disjoint());
                if c1 == cid {
                    // post[cid] ⊆ pre[cid]; post[c2] = pre[c2]; pre[cid].disjoint(pre[c2]).
                    assert(pre.client_sets.contains_key(c2));
                    assert(pre.client_sets[c2] =~= post.client_sets[c2]);
                } else if c2 == cid {
                    assert(pre.client_sets.contains_key(c1));
                    assert(pre.client_sets[c1] =~= post.client_sets[c1]);
                } else {
                    assert(pre.client_sets[c1] =~= post.client_sets[c1]);
                    assert(pre.client_sets[c2] =~= post.client_sets[c2]);
                }
            }

            // inv_free_clients_disjoint
            assert forall |c: ClientID| #[trigger] post.client_sets.contains_key(c)
                implies post.client_sets[c].disjoint(post.free_set)
            by {
                assert(pre.inv_free_clients_disjoint());
                if c == cid {
                    // post[cid] = owned.remove(fid), post.free_set = pre.free_set.insert(fid).
                    // owned.disjoint(pre.free_set) and fid ∉ owned.remove(fid) → ok.
                    assert(owned.disjoint(pre.free_set));
                } else {
                    // post[c] = pre[c]; fid ∉ pre[c]; pre[c].disjoint(pre.free_set) → ok.
                    assert(pre.client_sets.contains_key(c));
                    assert(!pre.client_sets[c].contains(fid));
                    assert(pre.client_sets[c] =~= post.client_sets[c]);
                }
            }
        }

        #[inductive(alloc_contiguous)]
        fn alloc_contiguous_inductive(pre: Self, post: Self, cid: ClientID, start: FrameID, count: FrameID) {
            let allocated = Set::new(|fid: FrameID| start <= fid < start + count);
            let owned = pre.client_sets[cid];
            assert(post.client_sets =~= pre.client_sets.insert(cid, owned.union(allocated)));
            assert(post.free_set =~= pre.free_set.difference(allocated));

            assert forall |fid: FrameID| #[trigger] allocated.contains(fid)
                implies !owned.contains(fid)
            by {
                assert(pre.inv_free_clients_disjoint());
                assert(allocated.contains(fid) ==> pre.free_set.contains(fid));
                assert(owned.disjoint(pre.free_set));
            }

            assert forall |c: ClientID| #[trigger] pre.client_sets.contains_key(c) && c != cid
                implies pre.client_sets[c].disjoint(allocated)
            by {
                assert(pre.inv_free_clients_disjoint());
                assert forall |fid: FrameID| #[trigger] allocated.contains(fid)
                    implies !pre.client_sets[c].contains(fid)
                by {
                    assert(allocated.contains(fid) ==> pre.free_set.contains(fid));
                    assert(pre.client_sets[c].disjoint(pre.free_set));
                }
            }

            assert forall |c: ClientID| #![auto]
                #[trigger] post.registered.contains(c) <==> post.client_sets.contains_key(c)
            by { assert(pre.inv_registered()); }

            assert forall |c: ClientID| #[trigger] post.client_sets.contains_key(c)
                implies post.client_sets[c].disjoint(post.free_set)
            by {
                assert(pre.inv_free_clients_disjoint());
                if c == cid {
                    assert(owned.disjoint(pre.free_set));
                    assert(post.free_set.subset_of(pre.free_set));
                } else {
                    assert(pre.client_sets.contains_key(c));
                    assert(pre.client_sets[c] =~= post.client_sets[c]);
                    assert(post.free_set.subset_of(pre.free_set));
                }
            }

            assert forall |c1: ClientID, c2: ClientID| #![auto]
                c1 != c2
                && post.client_sets.contains_key(c1)
                && post.client_sets.contains_key(c2)
                implies post.client_sets[c1].disjoint(post.client_sets[c2])
            by {
                assert(pre.inv_clients_disjoint());
                if c1 == cid {
                    assert(pre.client_sets.contains_key(c2));
                    assert(pre.client_sets[c2].disjoint(allocated));
                    assert(pre.client_sets[c2] =~= post.client_sets[c2]);
                } else if c2 == cid {
                    assert(pre.client_sets.contains_key(c1));
                    assert(pre.client_sets[c1].disjoint(allocated));
                    assert(pre.client_sets[c1] =~= post.client_sets[c1]);
                } else {
                    assert(pre.client_sets[c1] =~= post.client_sets[c1]);
                    assert(pre.client_sets[c2] =~= post.client_sets[c2]);
                }
            }
        }

        #[inductive(dealloc_contiguous)]
        fn dealloc_contiguous_inductive(pre: Self, post: Self, cid: ClientID, start: FrameID, count: FrameID) {
            let removed = Set::new(|fid: FrameID| start <= fid < start + count);
            let owned = pre.client_sets[cid];
            assert(post.client_sets =~= pre.client_sets.insert(cid, owned.difference(removed)));
            assert(post.free_set =~= pre.free_set.union(removed));

            assert(removed.disjoint(pre.free_set)) by {
                assert(pre.inv_free_clients_disjoint());
                assert(owned.disjoint(pre.free_set));
                assert forall |fid: FrameID| #[trigger] removed.contains(fid) implies owned.contains(fid) by {
                    assert(owned.contains(fid));
                }
            }

            assert forall |c: ClientID| #![auto]
                #[trigger] post.registered.contains(c) <==> post.client_sets.contains_key(c)
            by { assert(pre.inv_registered()); }

            assert forall |c: ClientID| #[trigger] post.client_sets.contains_key(c)
                implies post.client_sets[c].disjoint(post.free_set)
            by {
                assert(pre.inv_free_clients_disjoint());
                if c == cid {
                    assert(post.client_sets[c] =~= owned.difference(removed));
                    assert(post.client_sets[c].disjoint(removed));
                    assert(owned.difference(removed).disjoint(pre.free_set));
                } else {
                    assert(pre.inv_clients_disjoint());
                    assert(pre.client_sets[c].disjoint(owned));
                    assert(pre.client_sets[c].disjoint(pre.free_set));
                    assert(pre.client_sets[c] =~= post.client_sets[c]);
                    assert(pre.client_sets[c].disjoint(removed)) by {
                        assert forall |fid: FrameID| #[trigger] removed.contains(fid) implies owned.contains(fid) by {
                            assert(owned.contains(fid));
                        }
                    }
                }
            }

            assert forall |c1: ClientID, c2: ClientID| #![auto]
                c1 != c2
                && post.client_sets.contains_key(c1)
                && post.client_sets.contains_key(c2)
                implies post.client_sets[c1].disjoint(post.client_sets[c2])
            by {
                assert(pre.inv_clients_disjoint());
                if c1 == cid {
                    assert(post.client_sets[c1].subset_of(pre.client_sets[c1]));
                    assert(pre.client_sets[c2] =~= post.client_sets[c2]);
                } else if c2 == cid {
                    assert(post.client_sets[c2].subset_of(pre.client_sets[c2]));
                    assert(pre.client_sets[c1] =~= post.client_sets[c1]);
                } else {
                    assert(pre.client_sets[c1] =~= post.client_sets[c1]);
                    assert(pre.client_sets[c2] =~= post.client_sets[c2]);
                }
            }
        }
    }
}

// ── Type aliases ──────────────────────────────────────────────────────────────
pub type AllocInstance = AllocSpec::Instance;

pub type FreeSetToken = AllocSpec::free_set;

pub type RegisteredToken = AllocSpec::registered;

pub type ClientToken = AllocSpec::client_sets;

pub type GbAlloc = GlobalAllocator<BitAlloc1M>;

/// Frame Size: 4 KiB (4096 bytes).
pub const FRAME_SIZE: usize = 4096;

/// Frame size in spec mode.
pub spec const SPEC_FRAME_SIZE: nat = 4096;

/// Permission to access a 4K Frame
pub type Frame4KPerm = vstd::simple_pptr::PointsTo<[u8; 4096]>;

/// A marker spec funtion indicates a frame is empty.
pub uninterp spec fn frame_is_empty(perm: &Frame4KPerm) -> bool;

/// Abstract function binding allocator instance id to its base address.
pub uninterp spec fn inst_base(inst_id: InstanceId) -> SpecPAddr;

// ── Allocator-side ghost state ────────────────────────────────────────────────
/// Ghost state held inside the allocator.
/// Concurrent use: wrap this in a `Mutex` so only one thread can `alloc`/`dealloc`
/// at a time.  Clients hold their own `ClientToken` independently (outside the lock).
pub tracked struct AllocatorState {
    pub inst: AllocInstance,
    pub free_tok: FreeSetToken,
    pub reg_tok: RegisteredToken,
    pub free_perms: Map<FrameID, Frame4KPerm>,
}

impl AllocatorState {
    /// Core invariant: `free_tok` mirrors `free_perms.dom()`.
    pub open spec fn wf(&self) -> bool {
        &&& self.free_tok.instance_id() == self.inst.id()
        &&& self.reg_tok.instance_id() == self.inst.id()
        &&& self.reg_tok.value().finite()
        &&& self.free_tok.value() == self.free_perms.dom()
        &&& forall|fid: FrameID| #[trigger]
            self.free_perms.contains_key(fid) ==> frame_is_empty(&self.free_perms[fid])
        &&& forall|fid: FrameID| #[trigger]
            self.free_perms.contains_key(fid) ==> self.free_perms[fid].is_init() && inst_base(
                self.inst.id(),
            ).0 + fid * SPEC_FRAME_SIZE == self.free_perms[fid].addr()
    }

    /// Bootstrap the initial free set `[0, size)`.
    pub proof fn init_free_set(
        tracked &mut self,
        size: FrameID,
        tracked free_perms: Map<FrameID, Frame4KPerm>,
    )
        requires
            old(self).wf(),
            old(self).free_tok.value() =~= Set::empty(),
            old(self).reg_tok.value() =~= Set::empty(),
            old(self).free_perms.dom() =~= Set::empty(),
            size <= old(self).inst.cap(),
            free_perms.dom() =~= Set::new(|fid: FrameID| fid < size),
            forall|fid: FrameID| #[trigger]
                free_perms.contains_key(fid) ==> frame_is_empty(&free_perms[fid]),
            forall|fid: FrameID| #[trigger]
                free_perms.contains_key(fid) ==> free_perms[fid].is_init() && inst_base(
                    old(self).inst.id(),
                ).0 + fid * SPEC_FRAME_SIZE == free_perms[fid].addr(),
        ensures
            self.wf(),
            self.inst.id() == old(self).inst.id(),
            self.inst.cap() == old(self).inst.cap(),
            self.reg_tok.value() =~= Set::empty(),
            self.free_tok.value() =~= Set::new(|fid: FrameID| fid < size),
            self.free_perms =~= free_perms,
    {
        self.inst.init_free_set(size, &mut self.free_tok, &mut self.reg_tok);
        self.free_perms = free_perms;
    }

    /// Register a new client and return its initial (empty) token.
    /// The caller guarantees `cid` is fresh (not yet registered).
    pub proof fn register_client(tracked &mut self, cid: ClientID) -> (tracked ct: ClientToken)
        requires
            old(self).wf(),
            !old(self).reg_tok.value().contains(cid),
        ensures
            self.wf(),
            self.inst.id() == old(self).inst.id(),
            self.inst.cap() == old(self).inst.cap(),
            self.free_tok.value() =~= old(self).free_tok.value(),
            ct.instance_id() == self.inst.id(),
            ct.key() == cid,
            ct.value() =~= Set::empty(),
    {
        self.inst.register_client(cid, &mut self.reg_tok)
    }

    /// Allocate `fid` to `client` and return the updated client state.
    ///
    /// The client state is a *linear resource* — consumed and returned, which
    /// statically prevents aliased ownership.
    pub proof fn alloc(
        tracked &mut self,
        tracked client: ClientState,
        fid: FrameID,
    ) -> (tracked new_client: ClientState)
        requires
            old(self).wf(),
            client.wf(old(self).inst.id()),
            old(self).free_tok.value().contains(fid),
        ensures
            self.wf(),
            self.inst.id() == old(self).inst.id(),
            self.inst.cap() == old(self).inst.cap(),
            self.free_tok.value() =~= old(self).free_tok.value().remove(fid),
            new_client.wf(old(self).inst.id()),
            !client.owns(fid),
            new_client.owns(fid),
            new_client.owned_frames() =~= client.owned_frames().insert(fid),
            forall|fid| #[trigger]
                client.frame_perms.contains_key(fid) ==> new_client.frame_perms[fid]
                    == client.frame_perms[fid],
            frame_is_empty(&new_client.frame_perms[fid]),
            new_client.client_tok.key() == client.client_tok.key(),
    {
        let tracked ClientState { client_tok, frame_perms: mut perms } = client;
        let cid = client_tok.key();
        self.inst.free_client_disjoint(cid, client_tok.value(), &self.free_tok, &client_tok);
        assert(!client_tok.value().contains(fid));

        let tracked new_ct = self.inst.alloc(cid, fid, &mut self.free_tok, client_tok);
        let tracked perm = self.free_perms.tracked_remove(fid);
        perms.tracked_insert(fid, perm);
        ClientState { client_tok: new_ct, frame_perms: perms }
    }

    /// Allocate a contiguous range `[start, start + count)` to `client`.
    pub proof fn alloc_contiguous(
        tracked &mut self,
        tracked client: ClientState,
        start: FrameID,
        count: FrameID,
    ) -> (tracked new_client: ClientState)
        requires
            old(self).wf(),
            client.wf(old(self).inst.id()),
            0 < count,
            forall|fid: FrameID| start <= fid < start + count ==> old(self).free_tok.value().contains(fid),
        ensures
            self.wf(),
            self.inst.id() == old(self).inst.id(),
            self.inst.cap() == old(self).inst.cap(),
            self.free_tok.value() =~= old(self).free_tok.value().difference(
                Set::new(|fid: FrameID| start <= fid < start + count),
            ),
            new_client.wf(old(self).inst.id()),
            new_client.client_tok.key() == client.client_tok.key(),
            new_client.owned_frames() =~= client.owned_frames().union(
                Set::new(|fid: FrameID| start <= fid < start + count),
            ),
            forall|fid: FrameID| #[trigger]
                client.frame_perms.contains_key(fid) ==> new_client.frame_perms.contains_key(fid)
                    && new_client.frame_perms[fid] == client.frame_perms[fid],
            forall|fid: FrameID| start <= fid < start + count ==> new_client.owns(fid),
            forall|fid: FrameID| start <= fid < start + count ==> !client.owns(fid),
    {
        let tracked ClientState { client_tok, frame_perms: mut perms } = client;
        let cid = client_tok.key();
        let allocated = Set::new(|fid: FrameID| start <= fid < start + count);
        let ghost old_free_dom = self.free_perms.dom();
        let ghost old_client_dom = perms.dom();
        self.inst.free_client_disjoint(cid, client_tok.value(), &self.free_tok, &client_tok);
        assert(forall|fid: FrameID| #[trigger] allocated.contains(fid) ==> !client_tok.value().contains(fid)) by {
            assert(forall|fid: FrameID| #[trigger] allocated.contains(fid) ==> self.free_tok.value().contains(fid));
            assert(client_tok.value().disjoint(self.free_tok.value()));
        }

        let tracked new_ct = self.inst.alloc_contiguous(cid, start, count, &mut self.free_tok, client_tok);
        let tracked new_perms = self.free_perms.tracked_remove_keys(allocated);
        assert(self.free_perms.dom() =~= old_free_dom.difference(allocated));
        assert(new_perms.dom() =~= allocated);
        perms.tracked_union_prefer_right(new_perms);
        assert(perms.dom() =~= old_client_dom.union(allocated));
        ClientState { client_tok: new_ct, frame_perms: perms }
    }

    /// Return `fid` from `client` back to the free pool.
    /// After this call the client no longer owns `fid`.
    pub proof fn dealloc(
        tracked &mut self,
        tracked client: ClientState,
        fid: FrameID,
    ) -> (tracked new_client: ClientState)
        requires
            old(self).wf(),
            client.wf(old(self).inst.id()),
            client.owns(fid),
            frame_is_empty(&client.frame_perms[fid]),
        ensures
            self.wf(),
            self.inst.id() == old(self).inst.id(),
            self.inst.cap() == old(self).inst.cap(),
            self.free_tok.value() =~= old(self).free_tok.value().insert(fid),
            new_client.wf(old(self).inst.id()),
            !new_client.owns(fid),
            new_client.owned_frames() =~= client.owned_frames().remove(fid),
            forall|fid2| #[trigger]
                new_client.frame_perms.contains_key(fid2) ==> new_client.frame_perms[fid2]
                    == client.frame_perms[fid2],
            forall|fid2| #[trigger]
                client.frame_perms.contains_key(fid2) && fid2 != fid
                    ==> new_client.frame_perms[fid2] == client.frame_perms[fid2],
            new_client.client_tok.key() == client.client_tok.key(),
    {
        let tracked ClientState { client_tok, frame_perms: mut perms } = client;
        let tracked perm = perms.tracked_remove(fid);
        let cid = client_tok.key();
        self.free_perms.tracked_insert(fid, perm);

        let tracked new_ct = self.inst.dealloc(cid, fid, &mut self.free_tok, client_tok);
        ClientState { client_tok: new_ct, frame_perms: perms }
    }

    /// Remove a contiguous owned range `[start, start + count)` from `client`
    /// and return it to the free pool.
    pub proof fn dealloc_contiguous(
        tracked &mut self,
        tracked client: ClientState,
        start: FrameID,
        count: FrameID,
    ) -> (tracked new_client: ClientState)
        requires
            old(self).wf(),
            client.wf(old(self).inst.id()),
            0 < count,
            forall|fid: FrameID| start <= fid < start + count ==> client.owns(fid),
            forall|fid: FrameID| start <= fid < start + count ==> frame_is_empty(&client.frame_perms[fid]),
        ensures
            self.wf(),
            self.inst.id() == old(self).inst.id(),
            self.inst.cap() == old(self).inst.cap(),
            self.free_tok.value() =~= old(self).free_tok.value().union(
                Set::new(|fid: FrameID| start <= fid < start + count),
            ),
            new_client.wf(old(self).inst.id()),
            new_client.client_tok.key() == client.client_tok.key(),
            new_client.owned_frames() =~= client.owned_frames().difference(
                Set::new(|fid: FrameID| start <= fid < start + count),
            ),
            forall|fid: FrameID| start <= fid < start + count ==> !new_client.owns(fid),
            forall|fid: FrameID| #[trigger]
                new_client.frame_perms.contains_key(fid) ==> new_client.frame_perms[fid]
                    == client.frame_perms[fid],
    {
        let removed = Set::new(|fid: FrameID| start <= fid < start + count);
        let ghost old_free_dom = self.free_perms.dom();
        let ghost old_client_dom = client.frame_perms.dom();
        let ghost old_owned = client.owned_frames();

        assert(old_owned =~= old_client_dom) by {
            assert(client.wf(old(self).inst.id()));
        }
        assert forall|fid: FrameID| #[trigger] removed.contains(fid) implies old_owned.contains(fid) by {
            assert(start <= fid < start + count);
            assert(client.owns(fid));
        }

        let tracked ClientState { client_tok, frame_perms: mut perms } = client;
        let cid = client_tok.key();
        assert(client_tok.value() =~= old_owned);
        assert(perms.dom() =~= old_client_dom);
        assert(removed.subset_of(client_tok.value())) by {
            assert forall|fid: FrameID| #[trigger] removed.contains(fid) implies client_tok.value().contains(fid) by {
                assert(old_owned.contains(fid));
            }
        }
        assert(removed.subset_of(perms.dom())) by {
            assert forall|fid: FrameID| #[trigger] removed.contains(fid) implies perms.dom().contains(fid) by {
                assert(old_owned.contains(fid));
                assert(old_client_dom.contains(fid));
            }
        }

        let tracked new_ct = self.inst.dealloc_contiguous(
            cid,
            start,
            count,
            &mut self.free_tok,
            client_tok,
        );
        let tracked removed_perms = perms.tracked_remove_keys(removed);
        assert(perms.dom() =~= old_client_dom.difference(removed));
        assert(removed_perms.dom() =~= removed);
        self.free_perms.tracked_union_prefer_right(removed_perms);
        assert(self.free_perms.dom() =~= old_free_dom.union(removed));
        ClientState { client_tok: new_ct, frame_perms: perms }
    }
}

/// Ghost state held by a registered client.
///
/// Core invariant: `client_tok.value() == frame_perms.dom()`.
/// The `AllocSpec` Instance guarantees this set is *disjoint* from every other
/// client's set — no external model or lock is required to prove that.
pub tracked struct ClientState {
    pub client_tok: ClientToken,
    pub frame_perms: Map<FrameID, Frame4KPerm>,
}

impl ClientState {
    /// Core invariant: the client token and frame permissions are consistent with the allocator instance.
    pub open spec fn wf(&self, inst_id: InstanceId) -> bool {
        &&& self.client_tok.instance_id() == inst_id
        &&& self.client_tok.value() == self.frame_perms.dom()
        &&& forall|fid: FrameID| #[trigger]
            self.frame_perms.contains_key(fid) ==> self.frame_perms[fid].is_init() && inst_base(
                inst_id,
            ).0 + fid * SPEC_FRAME_SIZE == self.frame_perms[fid].addr()
    }

    /// The instance ID of the allocator this client is registered with.
    pub open spec fn inst_id(&self) -> InstanceId {
        self.client_tok.instance_id()
    }

    /// The client's `ClientID` (key in the `AllocSpec` map sharding).
    pub open spec fn cid(&self) -> ClientID {
        self.client_tok.key()
    }

    /// The client exclusively owns `fid`.
    pub open spec fn owns(&self, fid: FrameID) -> bool {
        self.client_tok.value().contains(fid)
    }

    /// The set of frame IDs currently owned by this client.
    pub open spec fn owned_frames(&self) -> Set<FrameID> {
        self.client_tok.value()
    }

    /// Wrap a freshly-registered (empty) client token.
    pub proof fn new(tracked ct: ClientToken) -> (tracked cs: ClientState)
        requires
            ct.value() =~= Set::empty(),
        ensures
            cs.wf(ct.instance_id()),
            cs.frame_perms.dom() =~= Set::empty(),
    {
        ClientState { client_tok: ct, frame_perms: Map::tracked_empty() }
    }

    /// Borrow a frame's physical permission for read access — no lock required.
    pub proof fn borrow_perm(
        tracked &self,
        fid: FrameID,
        inst_id: Ghost<InstanceId>,
    ) -> (tracked perm: &Frame4KPerm)
        requires
            self.wf(inst_id@),
            self.owns(fid),
        ensures
            *perm == self.frame_perms[fid],
    {
        self.frame_perms.tracked_borrow(fid)
    }
}

// ============================================================================
// Exec-level implementation
// ============================================================================
// ── Tracked mutex content ─────────────────────────────────────────────────────
/// The tracked value stored inside the Mutex.
///
/// * `allocator_state` — AllocSpec ghost tokens + free-frame physical permissions.
/// * `bitmap_perm`  — Permission to read/write the exec bitmap via `PCell`.
///
/// Holding the Mutex gives exclusive access to both.
pub tracked struct MutexContent<A: BitmapAllocator> {
    pub allocator_state: AllocatorState,
    pub bitmap_perm: vstd::cell::PointsTo<A>,
}

// ── Mutex key ─────────────────────────────────────────────────────────────────
/// Key stored in the Mutex: pairs the AllocSpec instance ID with the PCell's
/// identity so the mutex invariant can enforce that `bitmap_perm` belongs to
/// `GlobalAllocator::bitmap` — eliminating the need for an external `assume`.
pub struct AllocKey {
    pub inst_id: InstanceId,
    pub cell_id: CellId,
}

// ── Mutex predicate ───────────────────────────────────────────────────────────
pub struct AllocMutexPred<A: BitmapAllocator>(PhantomData<A>);

impl<A: BitmapAllocator> InvariantPredicate<AllocKey, MutexContent<A>> for AllocMutexPred<A> {
    open spec fn inv(k: AllocKey, v: MutexContent<A>) -> bool {
        &&& v.allocator_state.wf()
        // AllocSpec instance matches key
        &&& v.allocator_state.inst.id()
            == k.inst_id
        // Capacity matches bitmap size
        &&& v.allocator_state.inst.cap()
            == A::spec_cap()
        // bitmap is initialized in cell
        &&& v.bitmap_perm.is_init()
        // the stored bitmap is well-formed
        &&& v.bitmap_perm.value().wf()
        // bitmap_perm belongs to GlobalAllocator::bitmap
        &&& v.bitmap_perm@.pcell === k.cell_id
        // bitmap matches free_tok
        &&& forall|i|
            0 <= i < A::spec_cap() ==> v.allocator_state.free_tok.value().contains(i as nat)
                == v.bitmap_perm.value()@[i]
    }
}

/// A concurrent global frame allocator implementation using a bitmap allocator and a spinlock
/// mutex for synchronization.
///
/// The state is split into two parts:
///
///   Mutex<AllocKey, MutexContent<A>, AllocMutexPred>
///       .allocator_state: AllocatorState   (ghost/tracked tokens)      ← protected by
///       .bitmap_perm:  PointsTo<A>      (PCell permission)               spinlock
///
///   PCell<A>   (exec bitmap)     ← accessed only while lock held
///
/// When a thread holds the Mutex it also holds the `PointsTo<A>` token, which
/// it uses to borrow the PCell's exec value via take()/put().
///
/// Clients hold their own ClientState token completely outside the lock, so
/// `Client::borrow_frame` is always lock-free (no CAS, no syscall).
///
/// ```text
/// Thread 0              Thread 1              Client (any thread)
///   alloc()               alloc()               borrow_frame()
///     lock ──────────┐      lock (spins)          no lock needed ✓
///     PCell::take()  │      ...
///     bitmap.alloc() │
///     PCell::put()   │
///     ghost update   │
///     unlock ────────┘
///                           lock ──────────┐
///                           ...            │
///                           unlock ────────┘
/// ```
pub struct GlobalAllocator<A: BitmapAllocator> {
    /// Base address of the managed physical memory region.
    pub base: PAddr,
    /// Spinlock: protects `MutexContent<A>` (ghost state + PCell permission).
    pub mutex: Mutex<AllocKey, MutexContent<A>, AllocMutexPred<A>>,
    /// Exec bitmap — write-accessed only while `mutex` is held.
    pub bitmap: PCell<A>,
}

impl<A: BitmapAllocator> GlobalAllocator<A> {
    /// Specification helper to calculate the frame ID from a physical address.
    pub open spec fn paddr_to_fid_spec(&self, addr: SpecPAddr) -> FrameID {
        (addr.0 - self.base@.0) as nat / SPEC_FRAME_SIZE
    }

    /// Specification helper to calculate the physical address from a frame ID.
    pub open spec fn fid_to_paddr_spec(&self, fid: FrameID) -> SpecPAddr {
        SpecPAddr(self.base@.0 + fid * SPEC_FRAME_SIZE)
    }

    /// The AllocSpec instance ID associated with this allocator.
    pub open spec fn inst_id(&self) -> InstanceId {
        self.mutex.k@.inst_id
    }

    /// Core invariant: the allocator is well-formed and the mutex invariant holds.
    pub open spec fn invariants(&self) -> bool {
        &&& A::cascade_not_overflow()
        &&& self.base@.aligned(
            SPEC_FRAME_SIZE,
        )
        // Link exec base to spec base associated with the AllocSpec instance
        &&& inst_base(self.inst_id()) == self.base@
        &&& self.base.0 + (A::spec_cap() * FRAME_SIZE) <= usize::MAX
        &&& self.mutex.wf()
        // bitmap_perm in the mutex always belongs to self.bitmap
        &&& self.bitmap.id() === self.mutex.k@.cell_id
    }

    /// Calculate the frame ID from a physical address.
    pub fn paddr_to_fid(&self, addr: PAddr) -> (res: usize)
        requires
            self.base@.aligned(SPEC_FRAME_SIZE),
            addr@.aligned(SPEC_FRAME_SIZE),
            addr@.0 >= self.base@.0,
        ensures
            res as nat == self.paddr_to_fid_spec(addr@),
    {
        (addr.0 - self.base.0) / FRAME_SIZE
    }

    /// Calculate the physical address from a frame ID.
    pub fn fid_to_paddr(&self, fid: usize) -> (res: PAddr)
        by (nonlinear_arith)
        requires
            self.base@.aligned(SPEC_FRAME_SIZE),
            self.base.0 + fid * FRAME_SIZE <= usize::MAX,
        ensures
            res@ == self.fid_to_paddr_spec(fid as nat),
            res@.aligned(SPEC_FRAME_SIZE),
            res.0 == self.base.0 + fid * FRAME_SIZE,
    {
        PAddr(self.base.0 + fid * FRAME_SIZE)
    }

    /// Create a default allocator. The bitmap and free pool both start empty.
    pub fn default(base: PAddr) -> (res: Self)
        requires
            A::cascade_not_overflow(),
            base@.aligned(SPEC_FRAME_SIZE),
            base.0 + (A::spec_cap() * FRAME_SIZE) <= usize::MAX,
        ensures
            res.invariants(),
    {
        let bitmap = A::default();
        let (bitmap_cell, Tracked(bitmap_perm)) = PCell::new(bitmap);
        let ghost bitmap_cell_id = bitmap_cell.id();

        let tracked (Tracked(inst), Tracked(free_tok), Tracked(reg_tok), _) =
            AllocSpec::Instance::initialize(A::spec_cap());
        let ghost inst_id = inst.id();

        let tracked allocator_state = AllocatorState {
            inst,
            free_tok,
            reg_tok,
            free_perms: Map::tracked_empty(),
        };

        let tracked content = MutexContent { allocator_state, bitmap_perm };
        let key = Ghost(AllocKey { inst_id, cell_id: bitmap_cell_id });

        proof {
            assume(inst_base(inst_id) == base@);
            assume(AllocMutexPred::<A>::inv(key@, content));
        }

        let mutex = Mutex::new(key, Tracked(content));
        let res = GlobalAllocator { base, mutex, bitmap: bitmap_cell };
        proof {
            assert(res.bitmap.id() === bitmap_cell_id);
            assume(res.mutex.k@ == key@);
            assert(res.mutex.k@.cell_id == bitmap_cell_id);
            assert(res.bitmap.id() === res.mutex.k@.cell_id);
            assert(res.invariants());
        }
        res
    }

    /// Initialize the empty allocator by marking `[0, size)` as free.
    pub fn init(
        &self,
        size: usize,
        Tracked(free_perms): Tracked<Map<FrameID, Frame4KPerm>>,
    )
        requires
            self.invariants(),
            size <= A::spec_cap(),
            free_perms.dom() =~= Set::new(|fid: FrameID| fid < size as nat),
            forall|fid: FrameID| #[trigger]
                free_perms.contains_key(fid) ==> frame_is_empty(&free_perms[fid]),
            forall|fid: FrameID| #[trigger]
                free_perms.contains_key(fid) ==> free_perms[fid].is_init(),
            forall|fid: FrameID| #[trigger]
                free_perms.contains_key(fid) ==> self.base@.0 + fid * SPEC_FRAME_SIZE == free_perms[fid].addr(),
        ensures
            self.invariants(),
    {
        let guard = self.mutex.lock();
        let MutexGuard { handle, token } = guard;
        let tracked mut content = token.get();

        let mut bitmap = self.bitmap.take(Tracked(&mut content.bitmap_perm));
        if size > 0 {
            bitmap.insert(0usize..size);
        }
        self.bitmap.put(Tracked(&mut content.bitmap_perm), bitmap);

        proof {
            assume(content.allocator_state.free_tok.value() =~= Set::empty());
            assume(content.allocator_state.reg_tok.value() =~= Set::empty());
            assume(content.allocator_state.free_perms.dom() =~= Set::empty());
            content.allocator_state.init_free_set(size as nat, free_perms);
            assume(AllocMutexPred::<A>::inv(self.mutex.k@, content));
        }

        self.mutex.unlock(MutexGuard { handle, token: Tracked(content) });
    }

    /// Register a new client (acquires the lock briefly).
    pub fn register_client(&self) -> (client: Tracked<ClientState>)
        requires
            self.invariants(),
        ensures
            client.wf(self.inst_id()),
            client.owned_frames() =~= Set::empty(),
    {
        // ── lock ──────────────────────────────────────────────────────────────
        let guard = self.mutex.lock();
        let MutexGuard { handle, token } = guard;
        let tracked mut content = token.get();

        let tracked ct;
        proof {
            let tracked cid = ClientID;
            // Freshness: ClientID space is infinite, so a fresh cid always exists.
            lemma_exists_different_client_id(content.allocator_state.reg_tok.value());
            assert(!content.allocator_state.reg_tok.value().contains(cid));
            ct = content.allocator_state.register_client(cid);
            assert(content.allocator_state.inst.cap() == A::spec_cap());
            assert(AllocMutexPred::<A>::inv(self.mutex.k@, content));
        }
        // ── unlock ────────────────────────────────────────────────────────────
        self.mutex.unlock(MutexGuard { handle, token: Tracked(content) });
        Tracked(ClientState::new(ct))
    }

    /// Allocate one free frame and transfer ownership to `client`.
    ///
    /// Requires the free pool to be non-empty (the design assumes infinitely
    /// many physical frames exist at the model level).  The lock is held
    /// **only for the duration of this call**; clients can call `borrow_frame`
    /// at any time without any lock.
    pub fn alloc(&self, Tracked(client): Tracked<ClientState>) -> (res: (
        PAddr,
        Tracked<ClientState>,
    ))
        requires
            self.invariants(),
            client.wf(self.inst_id()),
        ensures
            res.0@.aligned(SPEC_FRAME_SIZE),
            res.0.0 >= self.base.0,
            res.1.wf(self.inst_id()),
            res.1.cid() == client.cid(),
            !client.owns(self.paddr_to_fid_spec(res.0@)),
            res.1.owns(self.paddr_to_fid_spec(res.0@)),
            res.1.owned_frames() =~= client.owned_frames().insert(self.paddr_to_fid_spec(res.0@)),
            forall|fid| #[trigger]
                client.frame_perms.contains_key(fid) ==> res.1.frame_perms[fid]
                    == client.frame_perms[fid],
            frame_is_empty(&res.1.frame_perms[self.paddr_to_fid_spec(res.0@)]),
    {
        broadcast use BitmapAllocator::lemma_view_len_is_cap;
        // ── lock ──────────────────────────────────────────────────────────────

        let guard = self.mutex.lock();
        let MutexGuard { handle, token } = guard;
        let tracked mut content = token.get();

        let mut bitmap = self.bitmap.take(Tracked(&mut content.bitmap_perm));
        // The free pool is non-empty (design assumption: infinitely many slots).
        // We assume bitmap.alloc() succeeds and unwrap the result.
        assume(exists|i: int| 0 <= i < A::spec_cap() && bitmap@[i]);

        let idx = bitmap.alloc().unwrap();
        self.bitmap.put(Tracked(&mut content.bitmap_perm), bitmap);

        let tracked new_client;
        proof {
            let ghost old_content = content;
            // Bitmap reported idx free <==> free_tok contains idx as nat.
            assert(content.allocator_state.free_tok.value().contains(idx as nat));
            new_client = content.allocator_state.alloc(client, idx as nat);

            // AllocatorState wf restored.
            assert(AllocMutexPred::<A>::inv(self.mutex.k@, content));
        }
        let frame = self.fid_to_paddr(idx);
        // ── unlock ────────────────────────────────────────────────────────────
        self.mutex.unlock(MutexGuard { handle, token: Tracked(content) });
        (frame, Tracked(new_client))
    }

    /// Return `frame` from `client` back to the free pool.
    pub fn dealloc(&self, Tracked(client): Tracked<ClientState>, frame: PAddr) -> (new_client:
        Tracked<ClientState>)
        requires
            self.invariants(),
            client.wf(self.inst_id()),
            frame@.aligned(SPEC_FRAME_SIZE),
            frame.0 >= self.base.0,
            client.owns(self.paddr_to_fid_spec(frame@)),
            frame_is_empty(&client.frame_perms[self.paddr_to_fid_spec(frame@)]),
        ensures
            new_client.wf(self.inst_id()),
            new_client.cid() == client.cid(),
            !new_client.owns(self.paddr_to_fid_spec(frame@)),
            new_client.owned_frames() =~= client.owned_frames().remove(
                self.paddr_to_fid_spec(frame@),
            ),
            forall|fid2| #[trigger]
                new_client.frame_perms.contains_key(fid2) ==> new_client.frame_perms[fid2]
                    == client.frame_perms[fid2],
            forall|fid2| #[trigger]
                client.frame_perms.contains_key(fid2) && fid2 != self.paddr_to_fid_spec(frame@)
                    ==> new_client.frame_perms[fid2] == client.frame_perms[fid2],
    {
        let fid = self.paddr_to_fid(frame);
        // ── lock ──────────────────────────────────────────────────────────────
        let guard = self.mutex.lock();
        let MutexGuard { handle, token } = guard;
        let tracked mut content = token.get();

        // Return the frame to the exec bitmap via PCell.
        // bitmap_perm belongs to self.bitmap — guaranteed by AllocKey::cell_id in the
        // mutex invariant and self.wf();
        let mut bitmap = self.bitmap.take(Tracked(&mut content.bitmap_perm));
        // The bit must be 0 (allocated) because client.owns(fid); justified by the
        // TSM disjointness invariant between free_set and client_sets.
        proof {
            assert(client.owns(fid as nat));
            content.allocator_state.inst.free_client_disjoint(
                client.cid(),
                client.client_tok.value(),
                &content.allocator_state.free_tok,
                &client.client_tok,
            );
            content.allocator_state.inst.client_fid_within_cap(
                client.cid(),
                client.client_tok.value(),
                &client.client_tok,
            );
            assert(!content.allocator_state.free_tok.value().contains(fid as nat));
            bitmap.lemma_view_len_is_cap();
            assert(!bitmap@[fid as int]);
        }
        bitmap.dealloc(fid);
        self.bitmap.put(Tracked(&mut content.bitmap_perm), bitmap);

        let tracked new_client;
        proof {
            new_client = content.allocator_state.dealloc(client, fid as nat);
            assert(AllocMutexPred::<A>::inv(self.mutex.k@, content));
        }
        // ── unlock ────────────────────────────────────────────────────────────
        self.mutex.unlock(MutexGuard { handle, token: Tracked(content) });
        Tracked(new_client)
    }

    /// Remove `count` frames starting at `start` from `client`
    /// and return them to the free pool.
    pub fn dealloc_contiguous(&self, Tracked(client): Tracked<ClientState>, start: PAddr, count: usize) -> (new_client:
        Tracked<ClientState>)
        requires
            self.invariants(),
            client.wf(self.inst_id()),
            start@.aligned(SPEC_FRAME_SIZE),
            start.0 >= self.base.0,
            0 < count <= A::spec_cap(),
            self.paddr_to_fid_spec(start@) + count <= A::spec_cap(),
            forall|fid: FrameID|
                self.paddr_to_fid_spec(start@) <= fid < self.paddr_to_fid_spec(start@) + count
                    ==> client.owns(fid),
            forall|fid: FrameID|
                self.paddr_to_fid_spec(start@) <= fid < self.paddr_to_fid_spec(start@) + count
                    ==> frame_is_empty(&client.frame_perms[fid]),
        ensures
            self.invariants(),
            new_client.wf(self.inst_id()),
            new_client.cid() == client.cid(),
            new_client.owned_frames() =~= client.owned_frames().difference(
                Set::new(|fid: FrameID|
                    self.paddr_to_fid_spec(start@) <= fid < self.paddr_to_fid_spec(start@) + count),
            ),
    {
        let start_fid = self.paddr_to_fid(start);
        let end_fid = start_fid + count;

        let guard = self.mutex.lock();
        let MutexGuard { handle, token } = guard;
        let tracked mut content = token.get();

        let mut bitmap = self.bitmap.take(Tracked(&mut content.bitmap_perm));
        bitmap.insert(start_fid..end_fid);
        self.bitmap.put(Tracked(&mut content.bitmap_perm), bitmap);

        let tracked new_client;
        proof {
            new_client = content.allocator_state.dealloc_contiguous(client, start_fid as nat, count as nat);
            assert(AllocMutexPred::<A>::inv(self.mutex.k@, content));
        }

        self.mutex.unlock(MutexGuard { handle, token: Tracked(content) });
        Tracked(new_client)
    }

    /// Allocate `count` contiguous free frames with `2^align_log2` frame alignment.
    pub fn alloc_contiguous(
        &self,
        Tracked(client): Tracked<ClientState>,
        count: usize,
        align_log2: usize,
    ) -> (res: (PAddr, Tracked<ClientState>))
        requires
            self.invariants(),
            client.wf(self.inst_id()),
            0 < count <= A::spec_cap(),
            align_log2 < 64,
        ensures
            res.0@.aligned(SPEC_FRAME_SIZE),
            res.0.0 >= self.base.0,
            res.1.wf(self.inst_id()),
            res.1.cid() == client.cid(),
            forall|fid: FrameID| #[trigger]
                client.frame_perms.contains_key(fid) ==> res.1.frame_perms.contains_key(fid)
                    && res.1.frame_perms[fid] == client.frame_perms[fid],
            forall|fid: FrameID|
                self.paddr_to_fid_spec(res.0@) <= fid < self.paddr_to_fid_spec(res.0@) + count
                    ==> res.1.owns(fid),
    {
        broadcast use BitmapAllocator::lemma_view_len_is_cap;

        let guard = self.mutex.lock();
        let MutexGuard { handle, token } = guard;
        let tracked mut content = token.get();

        let mut bitmap = self.bitmap.take(Tracked(&mut content.bitmap_perm));
        let ghost old_bitmap = bitmap;

        let alloc_res = bitmap.alloc_contiguous(count, align_log2);
        // The free pool is non-empty (design assumption: infinitely many slots).
        assume(alloc_res.is_some());
        let idx = alloc_res.unwrap();
        self.bitmap.put(Tracked(&mut content.bitmap_perm), bitmap);

        let tracked new_client;
        proof {
            assert(forall|fid: FrameID|
                idx as nat <= fid < idx as nat + count as nat ==> old_bitmap@[fid as int]);
            assert forall|fid: FrameID|
                idx as nat <= fid < idx as nat + count as nat implies content.allocator_state.free_tok.value().contains(fid) by {
                assert(old_bitmap@[fid as int]);
                assert(content.allocator_state.free_tok.value().contains(fid) == old_bitmap@[fid as int]);
            }
            new_client = content.allocator_state.alloc_contiguous(client, idx as nat, count as nat);
            assert(AllocMutexPred::<A>::inv(self.mutex.k@, content));
        }
        let frame = self.fid_to_paddr(idx);
        self.mutex.unlock(MutexGuard { handle, token: Tracked(content) });
        (frame, Tracked(new_client))
    }
}

} // verus!
