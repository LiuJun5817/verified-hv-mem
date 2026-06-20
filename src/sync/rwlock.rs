use core::marker::PhantomData;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::atomic_ghost::*;
use vstd::cell::CellId;
use vstd::cell::PCell;
use vstd::cell::PointsTo;
use vstd::invariant;
use vstd::invariant::{AtomicInvariant, InvariantPredicate};
use vstd::multiset::*;
use vstd::open_atomic_invariant;
use vstd::prelude::*;
use vstd::rwlock::RwLock as VerusRwLock;

// The tokenized state machine is unchanged.
tokenized_state_machine! {

RwLockToks<K, V, Pred: InvariantPredicate<K, V>> {
    fields {
        /// Ghost key identifying this lock.
        #[sharding(constant)]
        pub k: K,

        /// Phantom marker for the predicate type.
        #[sharding(constant)]
        pub pred: PhantomData<Pred>,

        #[sharding(variable)]
        pub flag_exc: bool,

        #[sharding(variable)]
        pub flag_rc: nat,

        #[sharding(variable)]
        pub flag_real_rc: nat,

        #[sharding(storage_option)]
        pub storage: Option<V>,

        #[sharding(option)]
        pub pending_writer: Option<()>,

        #[sharding(option)]
        pub writer: Option<()>,

        #[sharding(multiset)]
        pub pending_reader: Multiset<()>,

        #[sharding(multiset)]
        pub mock_reader: Multiset<()>,

        #[sharding(multiset)]
        pub reader: Multiset<V>,
    }

    init!{
        initialize(k: K, t: V) {
            require Pred::inv(k, t);
            init k = k;
            init pred = PhantomData;
            init flag_exc = false;
            init flag_rc = 0;
            init flag_real_rc = 0;
            init storage = Some(t);
            init pending_writer = None;
            init writer = None;
            init pending_reader = Multiset::empty();
            init mock_reader = Multiset::empty();
            init reader = Multiset::empty();
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, k: K, t: V) {
        broadcast use group_multiset_axioms;
    }

    /// Increment the 'rc' counter, obtain a pending_reader
    transition!{
        acquire_read_start() {
            update flag_rc = pre.flag_rc + 1;
            add pending_reader += {()};
        }
    }

    /// Exchange the pending_reader for a reader by checking
    /// that the 'exc' bit is 0
    transition!{
        acquire_read_end() {
            require(pre.flag_exc == false);

            remove pending_reader -= {()};
            add mock_reader += {()};
        }
    }

    transition!{
        inc_real_rc() {
            update flag_real_rc = pre.flag_real_rc + 1;

            remove mock_reader -= {()};

            birds_eye let x: V = pre.storage->0;
            add reader += {x};
        }
    }

    /// Decrement the 'rc' counter, abandon the attempt to gain
    /// the 'read' lock.
    transition!{
        acquire_read_abandon() {
            remove pending_reader -= {()};
            assert(pre.flag_rc >= 1);
            update flag_rc = (pre.flag_rc - 1) as nat;
        }
    }

    /// Atomically set 'exc' bit from 'false' to 'true'
    /// Obtain a pending_writer
    transition!{
        acquire_exc_start() {
            require(pre.flag_exc == false);
            update flag_exc = true;
            add pending_writer += Some(());
        }
    }

    /// Finish obtaining the write lock by checking that 'rc' is 0.
    /// Exchange the pending_writer for a writer and withdraw the
    /// stored object.
    transition!{
        acquire_exc_end() {
            require(pre.flag_rc == 0);

            remove pending_writer -= Some(());

            add writer += Some(());

            birds_eye let x = pre.storage->0;
            withdraw storage -= Some(x);
            // Expose the predicate for the withdrawn value as a transition postcondition.
            // Follows from storage_inv: pre.storage is Some (withdraw requires it)
            // => Pred::inv(pre.k, pre.storage->0) = Pred::inv(pre.k, x).
            assert(Pred::inv(pre.k, x)) by {};
        }
    }

    /// Release the write-lock. Update the 'exc' bit back to 'false'.
    /// Return the 'writer' and also deposit an object back into storage.
    /// The caller must prove that `x` satisfies the lock's predicate.
    transition!{
        release_exc(x: V) {
            require Pred::inv(pre.k, x);

            remove writer -= Some(());

            update flag_exc = false;

            deposit storage += Some(x);
        }
    }

    /// Check that the 'reader' is actually a guard for the given object.
    property!{
        read_guard(x: V) {
            have reader >= {x};
            guard storage >= Some(x);
        }
    }

    property!{
        read_match(x: V, y: V) {
            have reader >= {x};
            have reader >= {y};
            assert(equal(x, y)) by {
                assert(equal(pre.storage, Some(x)));
                assert(equal(pre.storage, Some(y)));
            };
        }
    }

    property!{
        reader_element_pred(x: V) {
            have reader >= {x};
            assert(Pred::inv(pre.k, x)) by {
                assert(equal(pre.storage, Some(x)));
            };
        }
    }

    property!{
        write_locked_implies_real_rc_is_zero() {
            have writer >= Some(());
            assert(pre.flag_real_rc == 0) by {
                assert(pre.storage is None);
                assert(pre.reader.count(pre.storage->0) == 0) by {
                    if pre.reader.count(pre.storage->0) > 0 {
                        assert(equal(pre.storage, Some(pre.storage->0)));
                    }
                };
            };
        }
    }

    #[transition]
    transition!{
        dec_real_rc(x: V) {
            remove reader -= {x};
            add mock_reader += {()};

            assert(pre.flag_real_rc >= 1) by {
                assert(equal(pre.storage, Some(x)));
            };
            update flag_real_rc = (pre.flag_real_rc - 1) as nat;
        }
    }

    /// Release the reader-lock. Decrement 'rc' and return the 'reader' object.
    #[transition]
    transition!{
        release_shared() {
            remove mock_reader -= {()};

            assert(pre.flag_rc >= 1) by {
                assert(pre.storage is Some);
            };
            update flag_rc = (pre.flag_rc - 1) as nat;
        }
    }

    #[invariant]
    pub fn exc_bit_matches(&self) -> bool {
        (if self.flag_exc { 1 } else { 0 as int }) ==
            (if self.pending_writer is Some { 1 } else { 0 as int }) as int
            + (if self.writer is Some { 1 } else { 0 as int }) as int
    }

    #[invariant]
    pub fn count_matches(&self) -> bool {
        self.flag_rc == self.pending_reader.count(())
            + self.mock_reader.count(())
            + self.reader.count(self.storage->0)
    }

    #[invariant]
    pub fn real_count_matches(&self) -> bool {
        self.flag_real_rc == self.reader.count(self.storage->0)
    }

    #[invariant]
    pub fn mock_reader_implies_storage_is_some(&self) -> bool {
        self.mock_reader.count(()) > 0 ==> self.storage is Some
    }

    #[invariant]
    pub fn reader_agrees_storage(&self) -> bool {
        forall |t: V| imply(#[trigger] self.reader.count(t) > 0,
            equal(self.storage, Some(t)))
    }

    #[invariant]
    pub fn writer_agrees_storage(&self) -> bool {
        imply(self.writer is Some, self.storage is None)
    }

    #[invariant]
    pub fn writer_agrees_storage_rev(&self) -> bool {
        imply(self.storage is None, self.writer is Some)
    }

    /// The stored value always satisfies the lock's predicate.
    #[invariant]
    pub fn storage_inv(&self) -> bool {
        self.storage is Some ==> Pred::inv(self.k, self.storage->0)
    }

    #[inductive(acquire_read_start)]
    fn acquire_read_start_inductive(pre: Self, post: Self) {
        broadcast use group_multiset_axioms;
    }

    #[inductive(acquire_read_end)]
    fn acquire_read_end_inductive(pre: Self, post: Self) {
        broadcast use group_multiset_axioms;
    }

    #[inductive(inc_real_rc)]
    fn inc_real_rc_inductive(pre: Self, post: Self) {
        broadcast use group_multiset_axioms;
    }

    #[inductive(acquire_read_abandon)]
    fn acquire_read_abandon_inductive(pre: Self, post: Self) {
        broadcast use group_multiset_axioms;
    }

    #[inductive(acquire_exc_start)]
    fn acquire_exc_start_inductive(pre: Self, post: Self) { }

    #[inductive(acquire_exc_end)]
    fn acquire_exc_end_inductive(pre: Self, post: Self) { }

    #[inductive(release_exc)]
    fn release_exc_inductive(pre: Self, post: Self, x: V) {
        // storage_inv: post.storage == Some(x) and require gives Pred::inv(pre.k, x).
        // k is constant so post.k == pre.k, hence Pred::inv(post.k, post.storage->0).
    }

    #[inductive(dec_real_rc)]
    fn dec_real_rc_inductive(pre: Self, post: Self, x: V) { }

    #[inductive(release_shared)]
    fn release_shared_inductive(pre: Self, post: Self) { }
}

}

verus! {

use crate::bitmap_allocator::bitmap_trait::BitmapAllocator;

type RwInstance<K, V, Pred> = RwLockToks::Instance<K, V, Pred>;

type RwExcToken<K, V, Pred> = RwLockToks::flag_exc<K, V, Pred>;

type RwRcToken<K, V, Pred> = RwLockToks::flag_rc<K, V, Pred>;

type RwRealRcToken<K, V, Pred> = RwLockToks::flag_real_rc<K, V, Pred>;

pub type RwWriterToken<K, V, Pred> = RwLockToks::writer<K, V, Pred>;

type RwMockReaderToken<K, V, Pred> = RwLockToks::mock_reader<K, V, Pred>;

pub type RwReaderToken<K, V, Pred> = RwLockToks::reader<K, V, Pred>;

type RwPendingWriterToken<K, V, Pred> = RwLockToks::pending_writer<K, V, Pred>;

type RwPendingReaderToken<K, V, Pred> = RwLockToks::pending_reader<K, V, Pred>;

struct_with_invariants! {
    /// An RwLock parameterised by a ghost key `K` and a predicate `Pred`.
    ///
    /// `Pred::inv(k, v)` must hold whenever `v` is stored inside the lock.
    /// This mirrors the `Mutex<K,V,Pred>` design: whoever releases the write
    /// lock must prove the predicate, and whoever acquires the write lock
    /// receives a value that already satisfies it.
    pub struct RwLock<K, V, Pred: InvariantPredicate<K, V>> {
        pub exc: AtomicBool<_, RwExcToken<K, V, Pred>, _>,
        pub rc: AtomicU64<_, RwRcToken<K, V, Pred>, _>,
        pub real_rc: AtomicU64<_, RwRealRcToken<K, V, Pred>, _>,
        pub inst: Tracked<RwInstance<K, V, Pred>>,
        /// Ghost key; matches `inst@.k()` (enforced by `predicate` below).
        pub k: Ghost<K>,
    }

    pub open spec fn wf(&self) -> bool {
        invariant on exc with (inst) is (v: bool, g: RwExcToken<K, V, Pred>) {
            &&& g.instance_id() == inst@.id()
            &&& g.value() == v
        }

        invariant on rc with (inst) is (v: u64, g: RwRcToken<K, V, Pred>) {
            &&& g.instance_id() == inst@.id()
            &&& g.value() == v
        }

        invariant on real_rc with (inst) is (v: u64, g: RwRealRcToken<K, V, Pred>) {
            &&& g.instance_id() == inst@.id()
            &&& g.value() == v
        }

        predicate {
            self.inst@.k() == self.k@
        }
    }
}

impl<K, V, Pred: InvariantPredicate<K, V>> RwLock<K, V, Pred> {
    /// Create a new `RwLock` protecting value `t` under key `k` with predicate `Pred`.
    ///
    /// Mirrors `Mutex::new`: the caller must prove `Pred::inv(k, t)` up front;
    /// thereafter `storage_inv` in the state machine guarantees the predicate
    /// holds for the stored value at all times.
    pub fn new(Ghost(k): Ghost<K>, Tracked(t): Tracked<V>) -> (s: Self)
        requires
            Pred::inv(k, t),
        ensures
            s.wf(),
            s.k@ == k,
    {
        let tracked (
            Tracked(inst),
            Tracked(exc_tok),
            Tracked(rc_tok),
            Tracked(real_rc_tok),
            _,  // pending_writer: Option::None
            _,  // writer: Option::None
            _,  // pending_reader: Multiset::empty()
            _,  // mock_reader: Multiset::empty()
            _,  // reader: Multiset::empty()
        ) = RwLockToks::Instance::<K, V, Pred>::initialize(k, t, Option::Some(t));
        let inst = Tracked(inst);
        let exc = AtomicBool::new(Ghost(inst), false, Tracked(exc_tok));
        let rc = AtomicU64::new(Ghost(inst), 0u64, Tracked(rc_tok));
        let real_rc = AtomicU64::new(Ghost(inst), 0u64, Tracked(real_rc_tok));
        RwLock { exc, rc, real_rc, inst, k: Ghost(k) }
    }

    /// Returns `true` in the ghost world iff `val` satisfies the lock's predicate.
    pub open spec fn inv(&self, val: V) -> bool {
        Pred::inv(self.k@, val)
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn lock_write(&self) -> (res: RwWriteGuard<K, V, Pred>)
        requires
            self.wf(),
        ensures
            res.wf(self),
            self.inv(res@),
    {
        let mut done = false;
        let tracked mut pending_writer_token: Option<RwPendingWriterToken<K, V, Pred>> = None;
        while !done
            invariant
                done ==> {
                    &&& pending_writer_token.is_some()
                    &&& pending_writer_token->0.instance_id() == self.inst@.id()
                },
                self.wf(),
        {
            let result =
                atomic_with_ghost!(
                &self.exc => compare_exchange(false, true);
                returning res;
                ghost g => {
                    if res is Ok {
                        // `exc` is false, so we can start acquiring the write lock.
                        // Consume exc token and produce pending_writer token.
                        pending_writer_token = Some(self.inst.borrow().acquire_exc_start(&mut g));
                    }
                }
            );
            done = result.is_ok();
        }

        let mut write_handle_opt: Option<RwWriteGuard<K, V, Pred>> = None;
        loop
            invariant_except_break
                pending_writer_token is Some,
                pending_writer_token->0.instance_id() == self.inst@.id(),
                self.wf(),
            ensures
                write_handle_opt is Some,
                write_handle_opt->Some_0.wf(self),
                self.inv(write_handle_opt->Some_0.view()),
        {
            let tracked mut handle_opt: Option<RwWriterToken<K, V, Pred>> = None;
            let tracked mut token_opt: Option<V> = None;
            let result =
                atomic_with_ghost!(
                &self.rc => load();
                returning res;
                ghost g => {
                    if res == 0 {
                        // `rc` is 0, so we can finish acquiring the write lock.
                        let tracked pw_token = match pending_writer_token {
                            Some(t) => t,
                            None => proof_from_false(),
                        };
                        // Consume pending_writer token and produce writer token.
                        // acquire_exc_end asserts Pred::inv(k, x) on the withdrawn value,
                        // so exc_token satisfies the predicate as a transition postcondition.
                        let tracked res = self.inst.borrow().acquire_exc_end(&g, pw_token);
                        let tracked exc_handle = res.2.get();
                        let tracked exc_token = res.1.get();
                        assert(Pred::inv(self.k@, exc_token));
                        pending_writer_token = None;
                        handle_opt = Some(exc_handle);
                        token_opt = Some(exc_token);
                    }
                }
            );

            if result == 0 {
                let tracked handle = match handle_opt {
                    Some(t) => t,
                    None => proof_from_false(),
                };
                let tracked token = match token_opt {
                    Some(t) => t,
                    None => proof_from_false(),
                };
                assert(self.inv(token));

                let _ =
                    atomic_with_ghost!(
                    &self.real_rc => no_op();
                    ghost g => {
                        // Invariants show `real_rc` is 0
                        self.inst.borrow().write_locked_implies_real_rc_is_zero(&g, &handle);
                        assert(g.value() == 0);
                    }
                );

                let write_handle = RwWriteGuard {
                    handle: Tracked(handle),
                    token: Tracked(token),
                };
                write_handle_opt = Some(write_handle);
                break ;
            }
        }

        assert(write_handle_opt is Some);
        let write_handle = write_handle_opt.unwrap();
        write_handle
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn lock_read(&self) -> (res: RwReadGuard<K, V, Pred>)
        requires
            self.wf(),
        ensures
            res.wf(self),
    {
        let mut read_handle_opt: Option<RwReadGuard<K, V, Pred>> = None;
        loop
            invariant_except_break
                read_handle_opt is None,
                self.wf(),
            ensures
                read_handle_opt is Some,
                read_handle_opt->Some_0.wf(self),
        {
            let rc_val = atomic_with_ghost!(
                &self.rc => load();
                returning res;
                ghost g => { }
            );
            if rc_val >= u64::MAX {
                // Too many readers, wait for the next iteration to see if the count goes down.
                continue;
            }

            let tracked mut pending_reader_token: Option<RwPendingReaderToken<K, V, Pred>> = None;
            let result =
                atomic_with_ghost!(
                &self.rc => compare_exchange(rc_val, rc_val + 1);
                returning res;
                ghost g => {
                    if res is Ok {
                        pending_reader_token = Option::Some(
                            self.inst.borrow().acquire_read_start(&mut g)
                        );
                    }
                }
            );
            if result.is_err() {
                // Failed to increment `rc`, likely due to a concurrent writer. Retry.
                continue;
            }

            let tracked mut mock_reader_token_opt: Option<RwMockReaderToken<K, V, Pred>> = None;
            let result =
                atomic_with_ghost!(
                &self.exc => load();
                returning res;
                ghost g => {
                    if res == false {
                        // `exc` is false, so we can finish acquiring the read lock.
                        let tracked pr_token = match pending_reader_token {
                            Some(t) => t,
                            None => proof_from_false(),
                        };
                        // Consume pending_reader token and produce mock_reader token.
                        let tracked mock_handle = self.inst.borrow().acquire_read_end(&mut g, pr_token);
                        pending_reader_token = None;
                        mock_reader_token_opt = Some(mock_handle);
                    }
                }
            );

            if result == false {
                // Update `real_rc` by exchanging the mock reader token for a real reader token.
                let tracked mut handle_opt: Option<RwReaderToken<K, V, Pred>> = None;

                loop
                    invariant_except_break
                        self.wf(),
                        mock_reader_token_opt is Some,
                        mock_reader_token_opt->Some_0.instance_id() == self.inst@.id(),
                    ensures
                        read_handle_opt is Some,
                        read_handle_opt->Some_0.wf(self),
                {
                    let real_rc_val = atomic_with_ghost!(
                        &self.real_rc => load();
                        returning res;
                        ghost g => { }
                    );
                    if real_rc_val >= u64::MAX {
                        // Too many readers, wait for the next iteration to see if the count goes down.
                        continue;
                    }

                    let result = atomic_with_ghost!(
                        &self.real_rc => compare_exchange(real_rc_val, real_rc_val + 1);
                        returning res;
                        ghost g => {
                            if res is Ok {
                                // Consume mock_reader token and produce real reader token.
                                let tracked mock_reader_token = mock_reader_token_opt.tracked_take();
                                let tracked res = self.inst.borrow().inc_real_rc(&mut g, mock_reader_token);
                                let tracked handle = res.1.get();
                                handle_opt = Some(handle);
                            }
                        }
                    );

                    match result {
                        Ok(_) => {
                            let tracked handle = match handle_opt {
                                Some(t) => t,
                                None => proof_from_false(),
                            };
                            proof {
                                self.inst.borrow().reader_element_pred(handle.element(), &handle);
                            }
                            let read_handle = RwReadGuard {
                                handle: Tracked(handle),
                            };
                            read_handle_opt = Some(read_handle);
                            break;
                        },
                        Err(_) => {}
                    }
                }

                // Here we get the read handle, so we can break out of the loop and return it.
                break;
            } else {
                // Failed to acquire the read lock
                let tracked pr_token = match pending_reader_token {
                    Some(t) => t,
                    None => proof_from_false(),
                };

                // Abandon the attempt by removing the pending reader and decrementing `rc`
                let _ = atomic_with_ghost!(
                    &self.rc => fetch_sub(1);
                    returning res;
                    ghost g => {
                        self.inst.borrow().acquire_read_abandon(&mut g, pr_token);
                    }
                );
            }
        }

        read_handle_opt.unwrap()
    }

    /// Release the write lock.  The caller must prove `self.inv(guard.view())`
    /// (i.e. `Pred::inv(self.k@, value)`) so the state machine's `storage_inv`
    /// invariant is maintained — exactly as `Mutex::unlock` does.
    pub fn unlock_write(&self, guard: RwWriteGuard<K, V, Pred>) -> (res: ())
        requires
            self.wf(),
            guard.wf(self),
            self.inv(guard.view()),
    {
        let tracked handle = guard.handle.get();
        let tracked v = guard.token.get();
        atomic_with_ghost!(
            &self.exc => store(false);
            ghost g => {
                self.inst.borrow().release_exc(v, &mut g, v, handle);
            }
        );
    }

    pub fn unlock_read(&self, guard: RwReadGuard<K, V, Pred>) -> (res: ())
        requires
            self.wf(),
            guard.wf(self),
    {
        let tracked handle = guard.handle.get();
        let tracked mut mock_handle_opt: Option<RwMockReaderToken<K, V, Pred>> = Option::None;

        // First update `real_rc` by exchanging the real reader token for a mock reader token.
        let mock_handle = atomic_with_ghost!(
            &self.real_rc => fetch_sub(1);
            returning res;
            ghost g => {
                let tracked mock_handle = self.inst.borrow().dec_real_rc(handle.element(), &mut g, handle);
                mock_handle_opt = Some(mock_handle);
            }
        );

        // Then release the read lock by removing the mock reader token and decrementing `rc`.
        atomic_with_ghost!(
            &self.rc => fetch_sub(1);
            returning res;
            ghost g => {
                let tracked mock_handle = match mock_handle_opt {
                    Some(t) => t,
                    None => proof_from_false(),
                };
                self.inst.borrow().release_shared(&mut g, mock_handle);
            }
        );
    }
}

/// Write-lock guard carrying both the writer token and the withdrawn value.
///
/// `view()` exposes the stored `V`; the caller must prove `rwlock.inv(guard.view())`
/// before calling `unlock_write` (exactly mirroring `MutexGuard` + `Mutex::unlock`).
pub struct RwWriteGuard<K, V, Pred: InvariantPredicate<K, V>> {
    pub handle: Tracked<RwWriterToken<K, V, Pred>>,
    pub token: Tracked<V>,
}

impl<K, V, Pred: InvariantPredicate<K, V>> RwWriteGuard<K, V, Pred> {
    pub open spec fn wf(self, rwlock: &RwLock<K, V, Pred>) -> bool {
        &&& self.handle@.instance_id() == rwlock.inst@.id()
    }

    /// Ghost view of the stored value.
    pub open spec fn view(self) -> V {
        self.token@
    }
}

/// Read-lock guard carrying the reader token (a multiset element of type `V`).
pub struct RwReadGuard<K, V, Pred: InvariantPredicate<K, V>> {
    pub handle: Tracked<RwReaderToken<K, V, Pred>>,
}

impl<K, V, Pred: InvariantPredicate<K, V>> RwReadGuard<K, V, Pred> {
    pub open spec fn wf(self, rwlock: &RwLock<K, V, Pred>) -> bool {
        &&& self.handle@.instance_id() == rwlock.inst@.id()
        &&& rwlock.inv(self.handle@.element())
    }

    pub fn borrow(&self, rwlock: &RwLock<K, V, Pred>) -> (res: Tracked<&V>)
        requires
            self.wf(rwlock),
        ensures
            *res@ =~= self.handle@.element(),
            Pred::inv(rwlock.k@, *res@),
    {
        let tracked val = rwlock.inst.borrow().read_guard(
            self.handle@.element(),
            self.handle.borrow(),
        );
        Tracked(val)
    }
}

}
