//! Tokenized state machine for the global frame allocator.
//!
//! `AllocSpec` tracks which frame IDs belong to the free pool and which have been
//! handed out to each client.  Using `#[sharding(map)]` on `client_sets` means
//! every client independently holds a `AllocSpec::client_sets` token whose value
//! is exactly the set of frames that client currently owns.  The Instance
//! invariants (`inv_free_clients_disjoint` and `inv_clients_disjoint`) then
//! guarantee, at the type level, that no two clients ever hold the same frame.
use super::mutex::{Mutex, MutexGuard};
use crate::bitmap_allocator::bitmap_trait::BitmapAllocator;
use crate::global_allocator::{lemma_exists_different_client_id, ClientID, Frame4KPerm, FrameID};
use core::marker::PhantomData;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::cell::{CellId, PCell, PointsTo};
use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;

verus! {

tokenized_state_machine! {
    AllocSpec {
        fields {
            /// The set of free (unallocated) frame IDs.
            /// Held as a single token by the ConcurrentAllocator.
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
        // ── Initialization ───────────────────────────────────────────────────

        init! {
            initialize() {
                init free_set    = Set::empty();
                init registered  = Set::empty();
                init client_sets = Map::empty();
            }
        }

        // ── Transitions ──────────────────────────────────────────────────────

        /// Add a single frame to the free pool (called during allocator setup).
        /// Setup is defined as the phase before any client has been registered:
        /// `require(pre.registered.is_empty())` encodes this. Combined with
        /// `inv_registered`, this means `client_sets` is also empty, so
        /// `inv_free_clients_disjoint` is vacuously satisfied after the update.
        transition! {
            add_free_frame(fid: FrameID) {
                require(pre.registered.is_empty());
                require(!pre.free_set.contains(fid));
                update free_set = pre.free_set.insert(fid);
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
        /// The caller must supply the `free_set` token (held by ConcurrentAllocator)
        /// and the `client_sets` token for `cid` (held by the client).
        transition! {
            alloc(cid: ClientID, fid: FrameID) {
                require(pre.free_set.contains(fid));
                update free_set = pre.free_set.remove(fid);
                remove client_sets -= [cid => let owned];
                add    client_sets += [cid => owned.insert(fid)];
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
        fn initialize_inductive(post: Self) {}

        #[inductive(add_free_frame)]
        fn add_free_frame_inductive(pre: Self, post: Self, fid: FrameID) {
            // add_free_frame only updates free_set; client_sets is unchanged.
            // The TSM doesn't automatically expose this equality for map-sharded fields,
            // so we state it as a targeted assumption.
            assert(pre.client_sets =~= post.client_sets);
            // pre.registered.is_empty() (transition require) + inv_registered =>
            // no cid exists in pre.client_sets => post.client_sets is empty =>
            // inv_free_clients_disjoint and inv_clients_disjoint are vacuously true.
            assert forall |cid: ClientID| #[trigger] post.client_sets.contains_key(cid)
                implies post.client_sets[cid].disjoint(post.free_set)
            by {
                assert(pre.inv_registered());
                assert(!pre.registered.contains(cid));  // registered is empty
                assert(!pre.client_sets.contains_key(cid)); // via inv_registered
            }
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
    }
}

// ── Type aliases ──────────────────────────────────────────────────────────────
pub type AllocInstance = AllocSpec::Instance;

pub type FreeSetToken = AllocSpec::free_set;

pub type RegisteredToken = AllocSpec::registered;

pub type ClientToken = AllocSpec::client_sets;

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
        &&& self.free_tok.value() == self.free_perms.dom()
        &&& self.reg_tok.value().finite()
    }

    /// Create a fresh, empty allocator (no frames yet, no clients yet).
    pub proof fn new() -> (tracked res: AllocatorState)
        ensures
            res.wf(),
            res.free_tok.value() =~= Set::empty(),
    {
        let tracked (Tracked(inst), Tracked(free_tok), Tracked(reg_tok), _) =
            AllocSpec::Instance::initialize();
        AllocatorState { inst, free_tok, reg_tok, free_perms: Map::tracked_empty() }
    }

    /// Add one physical frame to the free pool.
    /// Must be called during setup, before any client is registered.
    pub proof fn add_frame(tracked &mut self, fid: FrameID, tracked perm: Frame4KPerm)
        requires
            old(self).wf(),
            old(self).reg_tok.value().is_empty(),
            !old(self).free_tok.value().contains(fid),
        ensures
            self.wf(),
            self.free_tok.value() =~= old(self).free_tok.value().insert(fid),
            self.inst.id() == old(self).inst.id(),
            self.reg_tok.value() =~= old(self).reg_tok.value(),
    {
        self.inst.add_free_frame(fid, &mut self.free_tok, &self.reg_tok);
        self.free_perms.tracked_insert(fid, perm);
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
        inst_id: Ghost<InstanceId>,
    ) -> (tracked new_client: ClientState)
        requires
            old(self).wf(),
            client.wf(inst_id@),
            inst_id@ == old(self).inst.id(),
            old(self).free_tok.value().contains(fid),
        ensures
            self.wf(),
            self.inst.id() == old(self).inst.id(),
            self.free_tok.value() =~= old(self).free_tok.value().remove(fid),
            new_client.wf(inst_id@),
            new_client.owns(fid),
            new_client.client_tok.key() == client.client_tok.key(),
    {
        let tracked ClientState { client_tok, frame_perms: mut perms } = client;
        let cid = client_tok.key();
        let tracked new_ct = self.inst.alloc(cid, fid, &mut self.free_tok, client_tok);
        let tracked perm = self.free_perms.tracked_remove(fid);
        perms.tracked_insert(fid, perm);
        ClientState { client_tok: new_ct, frame_perms: perms }
    }

    /// Return `fid` from `client` back to the free pool.
    /// After this call the client no longer owns `fid`.
    pub proof fn dealloc(
        tracked &mut self,
        tracked client: ClientState,
        fid: FrameID,
        inst_id: Ghost<InstanceId>,
    ) -> (tracked new_client: ClientState)
        requires
            old(self).wf(),
            client.wf(inst_id@),
            inst_id@ == old(self).inst.id(),
            client.owns(fid),
        ensures
            self.wf(),
            self.inst.id() == old(self).inst.id(),
            self.free_tok.value() =~= old(self).free_tok.value().insert(fid),
            new_client.wf(inst_id@),
            !new_client.owns(fid),
            new_client.client_tok.key() == client.client_tok.key(),
    {
        let tracked ClientState { client_tok, frame_perms: mut perms } = client;
        let tracked perm = perms.tracked_remove(fid);
        let cid = client_tok.key();
        self.free_perms.tracked_insert(fid, perm);
        let tracked new_ct = self.inst.dealloc(cid, fid, &mut self.free_tok, client_tok);
        ClientState { client_tok: new_ct, frame_perms: perms }
    }
}

// ── Client-side ghost state ───────────────────────────────────────────────────
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
    pub open spec fn wf(&self, inst_id: InstanceId) -> bool {
        &&& self.client_tok.instance_id() == inst_id
        &&& self.client_tok.value() == self.frame_perms.dom()
    }

    /// The client exclusively owns `fid`.
    pub open spec fn owns(&self, fid: FrameID) -> bool {
        self.client_tok.value().contains(fid)
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
    pub bitmap_perm: PointsTo<A>,
}

// ── Mutex key ─────────────────────────────────────────────────────────────────
/// Key stored in the Mutex: pairs the AllocSpec instance ID with the PCell's
/// identity so the mutex invariant can enforce that `bitmap_perm` belongs to
/// `ConcurrentAllocator::bitmap` — eliminating the need for an external `assume`.
pub struct AllocKey {
    pub inst_id: InstanceId,
    pub cell_id: CellId,
}

// ── Mutex predicate ───────────────────────────────────────────────────────────
pub struct AllocMutexPred<A: BitmapAllocator>(PhantomData<A>);

impl<A: BitmapAllocator> InvariantPredicate<AllocKey, MutexContent<A>> for AllocMutexPred<A> {
    open spec fn inv(k: AllocKey, v: MutexContent<A>) -> bool {
        &&& v.allocator_state.wf()
        &&& v.allocator_state.inst.id()
            == k.inst_id  // AllocSpec instance matches key
        &&& v.bitmap_perm.is_init()  // bitmap is initialized in cell
        &&& v.bitmap_perm.value().wf()  // the stored bitmap is well-formed
        &&& v.bitmap_perm@.pcell
            === k.cell_id  // bitmap_perm belongs to ConcurrentAllocator::bitmap
        &&& forall|i| 0 <= i < A::spec_cap() ==>
            v.allocator_state.free_tok.value().contains(i as nat)
                == v.bitmap_perm.value()@[i]  // bitmap matches free_tok
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
pub struct ConcurrentAllocator<A: BitmapAllocator> {
    /// Spinlock: protects `MutexContent<A>` (ghost state + PCell permission).
    pub mutex: Mutex<AllocKey, MutexContent<A>, AllocMutexPred<A>>,
    /// Exec bitmap — write-accessed only while `mutex` is held.
    pub bitmap: PCell<A>,
}

impl<A: BitmapAllocator> ConcurrentAllocator<A> {
    pub open spec fn inst_id(&self) -> InstanceId {
        self.mutex.k@.inst_id
    }

    pub open spec fn wf(&self) -> bool {
        &&& A::cascade_not_overflow()
        &&& self.mutex.wf()
        // bitmap_perm in the mutex always belongs to self.bitmap
        &&& self.bitmap.id()
            === self.mutex.k@.cell_id  
    }

    /// Register a new client (acquires the lock briefly).
    pub fn register_client(&self) -> (client: Client)
        requires
            self.wf(),
        ensures
            client.wf(self.inst_id()),
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
            assert(AllocMutexPred::<A>::inv(self.mutex.k@, content));
        }
        // ── unlock ────────────────────────────────────────────────────────────
        self.mutex.unlock(MutexGuard { handle, token: Tracked(content) });

        let tracked cs;
        proof {
            cs = ClientState::new(ct);
        }
        Client { state: Tracked(cs), inst_id: Ghost(self.inst_id()) }
    }

    /// Allocate one free frame and transfer ownership to `client`.
    ///
    /// Requires the free pool to be non-empty (the design assumes infinitely
    /// many physical frames exist at the model level).  The lock is held
    /// **only for the duration of this call**; clients can call `borrow_frame`
    /// at any time without any lock.
    pub fn alloc(&self, client: Client) -> (res: (usize, Client))
        requires
            self.wf(),
            client.wf(self.inst_id()),
        ensures
            res.1.wf(self.inst_id()),
            res.1.cid() == client.cid(),
            res.1.owns(res.0 as nat),
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

        let Client { state: Tracked(cs), inst_id } = client;
        let tracked new_cs;
        proof {
            let ghost old_content = content;
            // Bitmap reported idx free <==> free_tok contains idx as nat.
            assert(content.allocator_state.free_tok.value().contains(idx as nat));
            new_cs = content.allocator_state.alloc(cs, idx as nat, Ghost(self.inst_id()));
            
            // AllocatorState wf restored.
            assert(AllocMutexPred::<A>::inv(self.mutex.k@, content));
        }
        // ── unlock ────────────────────────────────────────────────────────────
        self.mutex.unlock(MutexGuard { handle, token: Tracked(content) });
        (idx, Client { state: Tracked(new_cs), inst_id })
    }

    /// Return frame `fid` from `client` back to the free pool.
    pub fn dealloc(&self, client: Client, fid: usize) -> (new_client: Client)
        requires
            self.wf(),
            client.wf(self.inst_id()),
            client.owns(fid as nat),
            fid < A::spec_cap(),
        ensures
            new_client.wf(self.inst_id()),
            new_client.cid() == client.cid(),
            !new_client.owns(fid as nat),
    {
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
            assert(client.state.owns(fid as nat));
            content.allocator_state.inst.free_client_disjoint(
                client.cid(),
                client.state.client_tok.value(),
                &content.allocator_state.free_tok,
                &client.state.client_tok,
            );
            assert(!content.allocator_state.free_tok.value().contains(fid as nat));
            bitmap.lemma_view_len_is_cap();
            assert(!bitmap@[fid as int]);
        }
        bitmap.dealloc(fid);
        self.bitmap.put(Tracked(&mut content.bitmap_perm), bitmap);

        let Client { state, inst_id } = client;
        let tracked new_cs;
        proof {
            let tracked cs = state.get();
            new_cs = content.allocator_state.dealloc(cs, fid as nat, Ghost(self.inst_id()));
            assert(AllocMutexPred::<A>::inv(self.mutex.k@, content));
        }
        // ── unlock ────────────────────────────────────────────────────────────
        self.mutex.unlock(MutexGuard { handle, token: Tracked(content) });
        Client { state: Tracked(new_cs), inst_id }
    }
}

/// A registered participant in the `ConcurrentAllocator`.
///
/// Holds the `AllocSpec` client token and physical permissions for all frames
/// it currently owns.  The `AllocSpec` invariants ensure — at the proof level —
/// that no two clients ever hold the same frame.
///
/// `Client` is a **linear resource**: passed by value into `alloc`/`dealloc`
/// and returned updated, which statically prevents aliased ownership.
pub struct Client {
    /// Ghost + tracked client state (token + physical permissions).
    pub state: Tracked<ClientState>,
    /// Ghost: which `ConcurrentAllocator` instance this client belongs to.
    pub inst_id: Ghost<InstanceId>,
}

impl Client {
    /// The `AllocSpec` instance this client belongs to.
    pub open spec fn inst_id(&self) -> InstanceId {
        self.inst_id@
    }

    /// The client's `ClientID` (key in the `AllocSpec` map sharding).
    pub open spec fn cid(&self) -> ClientID {
        self.state@.client_tok.key()
    }

    /// Well-formedness: token is bound to the right instance, perms match token.
    pub open spec fn wf(&self, inst_id: InstanceId) -> bool {
        &&& self.inst_id@ == inst_id
        &&& self.state@.wf(inst_id)
    }

    /// The set of frame IDs currently owned by this client (spec only).
    pub open spec fn owned_frames(&self) -> Set<FrameID> {
        self.state@.client_tok.value()
    }

    /// Whether this client currently owns frame `fid` (spec only).
    pub open spec fn owns(&self, fid: FrameID) -> bool {
        self.state@.owns(fid)
    }

    /// Borrow the physical permission for a frame this client owns.
    /// No lock needed — the client exclusively holds `fid` per the AllocSpec invariant.
    pub fn borrow_frame<'a>(&'a self, fid: usize) -> (perm: Tracked<&'a Frame4KPerm>)
        requires
            self.wf(self.inst_id@),
            self.state@.owns(fid as nat),
        ensures
            *perm@ == self.state@.frame_perms[fid as nat],
    {
        Tracked(self.state.borrow().borrow_perm(fid as nat, Ghost(self.inst_id@)))
    }
}

} // verus!

