use core::marker::PhantomData;
use core::option::Option::{self, None, Some};
use core::result::Result::{Err, Ok};
use core::unimplemented;
use core::unreachable;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::atomic_ghost::*;
use vstd::invariant::InvariantPredicate;
use vstd::multiset::*;
use vstd::prelude::*;

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

    /// Start a read acquisition by incrementing `rc` and minting a pending-reader token.
    transition!{
        acquire_read_start() {
            update flag_rc = pre.flag_rc + 1;
            add pending_reader += {()};
        }
    }

    /// Finish the first read phase when no writer holds or is acquiring `exc`.
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

    /// Abandon a read attempt after `rc` was incremented but `exc` was observed true.
    transition!{
        acquire_read_abandon() {
            remove pending_reader -= {()};
            assert(pre.flag_rc >= 1);
            update flag_rc = (pre.flag_rc - 1) as nat;
        }
    }

    /// Start a write acquisition by setting `exc` and minting a pending-writer token.
    transition!{
        acquire_exc_start() {
            require(pre.flag_exc == false);
            update flag_exc = true;
            add pending_writer += Some(());
        }
    }

    /// Finish write acquisition once `rc` is 0, withdrawing the stored value.
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

    /// Release the write lock by consuming the writer token and depositing `x`.
    transition!{
        release_exc(x: V) {
            require Pred::inv(pre.k, x);

            remove writer -= Some(());

            update flag_exc = false;

            deposit storage += Some(x);
        }
    }

    /// Borrow the stored value witnessed by a reader token.
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

    /// Finish read release by consuming a mock-reader token and decrementing `rc`.
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

    /// Stored values always satisfy the lock predicate.
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
    /// A reader-writer lock protecting a value of type `V` under `Pred`.
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
    /// Create a new reader-writer lock protecting `t`.
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

    /// Predicate required for values stored in this lock.
    pub open spec fn inv(&self, val: V) -> bool {
        Pred::inv(self.k@, val)
    }

    /// Acquire the write lock, spinning until `exc` is set and `rc` reaches 0.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn lock_write(&self) -> (guard: RwWriteGuard<K, V, Pred>)
        requires
            self.wf(),
        ensures
            guard.wf(self),
            self.inv(guard.view()),
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
            let cas_result =
                atomic_with_ghost!(
                &self.exc => compare_exchange(false, true);
                returning cas_res;
                ghost g => {
                    if cas_res is Ok {
                        pending_writer_token = Some(self.inst.borrow().acquire_exc_start(&mut g));
                    }
                }
            );
            done = cas_result.is_ok();
        }

        let mut write_guard_opt: Option<RwWriteGuard<K, V, Pred>> = None;
        loop
            invariant_except_break
                pending_writer_token is Some,
                pending_writer_token->0.instance_id() == self.inst@.id(),
                self.wf(),
            ensures
                write_guard_opt is Some,
                write_guard_opt->Some_0.wf(self),
                self.inv(write_guard_opt->Some_0.view()),
        {
            let tracked mut writer_token_opt: Option<RwWriterToken<K, V, Pred>> = None;
            let tracked mut value_opt: Option<V> = None;
            let rc_value =
                atomic_with_ghost!(
                &self.rc => load();
                returning loaded_rc;
                ghost g => {
                    if loaded_rc == 0 {
                        let tracked pw_token = match pending_writer_token {
                            Some(t) => t,
                            None => proof_from_false(),
                        };
                        let tracked acquire_result = self.inst.borrow().acquire_exc_end(&g, pw_token);
                        let tracked writer_token = acquire_result.2.get();
                        let tracked value = acquire_result.1.get();
                        assert(Pred::inv(self.k@, value));
                        pending_writer_token = None;
                        writer_token_opt = Some(writer_token);
                        value_opt = Some(value);
                    }
                }
            );

            if rc_value == 0 {
                let tracked writer_token = match writer_token_opt {
                    Some(t) => t,
                    None => proof_from_false(),
                };
                let tracked value = match value_opt {
                    Some(t) => t,
                    None => proof_from_false(),
                };
                assert(self.inv(value));

                let _ =
                    atomic_with_ghost!(
                    &self.real_rc => no_op();
                    ghost g => {
                        self.inst.borrow().write_locked_implies_real_rc_is_zero(&g, &writer_token);
                        assert(g.value() == 0);
                    }
                );

                let write_guard = RwWriteGuard {
                    handle: Tracked(writer_token),
                    token: Tracked(value),
                };
                write_guard_opt = Some(write_guard);
                break ;
            }
        }

        assert(write_guard_opt is Some);
        let guard = write_guard_opt.unwrap();
        guard
    }

    /// Acquire the read lock, spinning until the reader has joined both counters.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn lock_read(&self) -> (guard: RwReadGuard<K, V, Pred>)
        requires
            self.wf(),
        ensures
            guard.wf(self),
    {
        let mut read_guard_opt: Option<RwReadGuard<K, V, Pred>> = None;
        loop
            invariant_except_break
                read_guard_opt is None,
                self.wf(),
            ensures
                read_guard_opt is Some,
                read_guard_opt->Some_0.wf(self),
        {
            let rc_val =
                atomic_with_ghost!(
                &self.rc => load();
                returning loaded_rc;
                ghost g => { }
            );
            if rc_val >= u64::MAX {
                continue ;
            }
            let tracked mut pending_reader_token: Option<RwPendingReaderToken<K, V, Pred>> = None;
            let rc_cas_result =
                atomic_with_ghost!(
                &self.rc => compare_exchange(rc_val, rc_val + 1);
                returning cas_res;
                ghost g => {
                    if cas_res is Ok {
                        pending_reader_token = Option::Some(
                            self.inst.borrow().acquire_read_start(&mut g)
                        );
                    }
                }
            );
            if rc_cas_result.is_err() {
                continue ;
            }
            let tracked mut mock_reader_token_opt: Option<RwMockReaderToken<K, V, Pred>> = None;
            let exc_value =
                atomic_with_ghost!(
                &self.exc => load();
                returning loaded_exc;
                ghost g => {
                    if loaded_exc == false {
                        let tracked pr_token = match pending_reader_token {
                            Some(t) => t,
                            None => proof_from_false(),
                        };
                        let tracked mock_reader_token = self.inst.borrow().acquire_read_end(
                            &mut g,
                            pr_token,
                        );
                        pending_reader_token = None;
                        mock_reader_token_opt = Some(mock_reader_token);
                    }
                }
            );

            if exc_value == false {
                let tracked mut reader_token_opt: Option<RwReaderToken<K, V, Pred>> = None;

                loop
                    invariant_except_break
                        self.wf(),
                        mock_reader_token_opt is Some,
                        mock_reader_token_opt->Some_0.instance_id() == self.inst@.id(),
                    ensures
                        read_guard_opt is Some,
                        read_guard_opt->Some_0.wf(self),
                {
                    let real_rc_val =
                        atomic_with_ghost!(
                        &self.real_rc => load();
                        returning loaded_real_rc;
                        ghost g => { }
                    );
                    if real_rc_val >= u64::MAX {
                        continue ;
                    }
                    let real_rc_cas_result =
                        atomic_with_ghost!(
                        &self.real_rc => compare_exchange(real_rc_val, real_rc_val + 1);
                        returning cas_res;
                        ghost g => {
                            if cas_res is Ok {
                                let tracked mock_reader_token = mock_reader_token_opt.tracked_take();
                                let tracked inc_result = self.inst.borrow().inc_real_rc(
                                    &mut g,
                                    mock_reader_token,
                                );
                                let tracked reader_token = inc_result.1.get();
                                reader_token_opt = Some(reader_token);
                            }
                        }
                    );

                    match real_rc_cas_result {
                        Ok(_) => {
                            let tracked reader_token = match reader_token_opt {
                                Some(t) => t,
                                None => proof_from_false(),
                            };
                            proof {
                                self.inst.borrow().reader_element_pred(
                                    reader_token.element(),
                                    &reader_token,
                                );
                            }
                            let read_guard = RwReadGuard { handle: Tracked(reader_token) };
                            read_guard_opt = Some(read_guard);
                            break ;
                        },
                        Err(_) => {},
                    }
                }

                break ;
            } else {
                let tracked pr_token = match pending_reader_token {
                    Some(t) => t,
                    None => proof_from_false(),
                };

                let _ =
                    atomic_with_ghost!(
                    &self.rc => fetch_sub(1);
                    returning old_rc;
                    ghost g => {
                        self.inst.borrow().acquire_read_abandon(&mut g, pr_token);
                    }
                );
            }
        }

        read_guard_opt.unwrap()
    }

    /// Release the write lock by consuming the guard and storing its value back.
    pub fn unlock_write(&self, guard: RwWriteGuard<K, V, Pred>)
        requires
            self.wf(),
            guard.wf(self),
            self.inv(guard.view()),
    {
        let tracked writer_token = guard.handle.get();
        let tracked value = guard.token.get();
        atomic_with_ghost!(
            &self.exc => store(false);
            ghost g => {
                self.inst.borrow().release_exc(value, &mut g, value, writer_token);
            }
        );
    }

    /// Release the read lock by decrementing `real_rc` and then `rc`.
    pub fn unlock_read(&self, guard: RwReadGuard<K, V, Pred>)
        requires
            self.wf(),
            guard.wf(self),
    {
        let tracked reader_token = guard.handle.get();
        let tracked mut mock_reader_token_opt: Option<RwMockReaderToken<K, V, Pred>> = Option::None;

        let _ =
            atomic_with_ghost!(
            &self.real_rc => fetch_sub(1);
            returning old_real_rc;
            ghost g => {
                let tracked mock_reader_token = self.inst.borrow().dec_real_rc(
                    reader_token.element(),
                    &mut g,
                    reader_token,
                );
                mock_reader_token_opt = Some(mock_reader_token);
            }
        );

        atomic_with_ghost!(
            &self.rc => fetch_sub(1);
            returning old_rc;
            ghost g => {
                let tracked mock_reader_token = match mock_reader_token_opt {
                    Some(t) => t,
                    None => proof_from_false(),
                };
                self.inst.borrow().release_shared(&mut g, mock_reader_token);
            }
        );
    }
}

/// Exclusive guard returned by `RwLock::lock_write`.
///
/// `handle` is the ghost writer token. `token` is the protected value withdrawn
/// from the state machine while the write lock is held.
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

/// Shared guard returned by `RwLock::lock_read`.
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

} // verus!
