use core::marker::PhantomData;
use core::unimplemented;
use core::unreachable;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::atomic_ghost::*;
use vstd::invariant::InvariantPredicate;
use vstd::prelude::*;

tokenized_state_machine! {

MutexToks<K, V, Pred: InvariantPredicate<K, V>> {
    fields {
        #[sharding(constant)]
        pub k: K,

        #[sharding(constant)]
        pub pred: PhantomData<Pred>,

        #[sharding(variable)]
        pub locked: bool,

        #[sharding(storage_option)]
        pub storage: Option<V>,

        #[sharding(option)]
        pub owner: Option<()>,
    }

    init! {
        initialize(k: K, t: V) {
            require Pred::inv(k, t);
            init k = k;
            init pred = PhantomData;
            init locked = false;
            init storage = Option::Some(t);
            init owner = Option::None;
        }
    }

    /// Acquire the mutex: set the lock bit, withdraw the protected value, and mint
    /// the owner token.
    transition! {
        acquire() {
            require(!pre.locked);
            update locked = true;
            add owner += Some(());

            birds_eye let x = pre.storage->0;
            withdraw storage -= Some(x);

            assert Pred::inv(pre.k, x);
        }
    }

    /// Release the mutex by consuming the owner token and depositing the value back.
    transition! {
        release(x: V) {
            require Pred::inv(pre.k, x);
            remove owner -= Some(());
            update locked = false;
            deposit storage += Some(x);
        }
    }

    #[invariant]
    pub fn locked_invariant(&self) -> bool {
        self.locked == self.owner is Some
    }

    #[invariant]
    pub fn storage_inv(&self) -> bool {
        self.storage is Some ==> Pred::inv(self.k, self.storage->0)
    }

    #[invariant]
    pub fn owner_implies_no_storage(&self) -> bool {
        (self.owner is Some) ==> (self.storage is None)
    }

    #[invariant]
    pub fn no_owner_implies_storage(&self) -> bool {
        (self.owner is None) ==> (self.storage is Some)
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, k: K, t: V) { }

    #[inductive(acquire)]
    fn acquire_inductive(pre: Self, post: Self) { }

    #[inductive(release)]
    fn release_inductive(pre: Self, post: Self, x: V) { }
}

}

verus! {

type MutexInstance<K, V, Pred> = MutexToks::Instance<K, V, Pred>;

type MutexLockedToken<K, V, Pred> = MutexToks::locked<K, V, Pred>;

type MutexOwnerToken<K, V, Pred> = MutexToks::owner<K, V, Pred>;

pub struct MutexAtomicPred<K, V, Pred> {
    marker: PhantomData<(K, V, Pred)>,
}

impl<K, V, Pred: InvariantPredicate<K, V>> AtomicInvariantPredicate<
    vstd::tokens::InstanceId,
    bool,
    MutexLockedToken<K, V, Pred>,
> for MutexAtomicPred<K, V, Pred> {
    open spec fn atomic_inv(
        inst_id: vstd::tokens::InstanceId,
        value: bool,
        token: MutexLockedToken<K, V, Pred>,
    ) -> bool {
        &&& token.instance_id() == inst_id
        &&& token.value() == value
    }
}

/// A mutex protecting an object of type `V` with invariant `Pred`.
/// The mutex is identified by a key of type `K`.
pub struct Mutex<K, V, Pred: InvariantPredicate<K, V>> {
    pub locked: AtomicBool<
        vstd::tokens::InstanceId,
        MutexLockedToken<K, V, Pred>,
        MutexAtomicPred<K, V, Pred>,
    >,
    pub inst: Tracked<MutexInstance<K, V, Pred>>,
    pub k: Ghost<K>,
}

/// Exclusive guard returned by `Mutex::lock`.
///
/// `handle` is the ghost owner token. `token` is the protected value withdrawn
/// from the state machine while the mutex is locked.
pub struct MutexGuard<K, V, Pred: InvariantPredicate<K, V>> {
    pub handle: Tracked<MutexOwnerToken<K, V, Pred>>,
    pub token: Tracked<V>,
}

impl<K, V, Pred: InvariantPredicate<K, V>> MutexGuard<K, V, Pred> {
    pub open spec fn wf(self, mutex: &Mutex<K, V, Pred>) -> bool {
        &&& self.handle@.instance_id() == mutex.inst@.id()
    }

    /// Ghost view of the protected value.
    pub open spec fn view(self) -> V {
        self.token@
    }
}

impl<K, V, Pred: InvariantPredicate<K, V>> Mutex<K, V, Pred> {
    pub open spec fn wf(&self) -> bool {
        &&& self.locked.well_formed()
        &&& self.locked.constant() == self.inst@.id()
        &&& self.inst@.k() == self.k@
    }

    /// Create a new mutex protecting the value `val` with invariant `Pred`.
    /// The mutex is identified by the key `k`.
    pub fn new(Ghost(k): Ghost<K>, Tracked(val): Tracked<V>) -> (s: Self)
        requires
            Pred::inv(k, val),
        ensures
            s.wf(),
            s.k@ == k,
    {
        let tracked (
            Tracked(inst),
            Tracked(locked_tok),
            _,  // owner: None
        ) = MutexToks::Instance::<K, V, Pred>::initialize(k, val, Option::Some(val));

        let ghost inst_id = inst.id();
        let inst = Tracked(inst);
        let locked = AtomicBool::new(Ghost(inst_id), false, Tracked(locked_tok));
        Mutex { locked, inst, k: Ghost(k) }
    }

    /// Predicate required for values stored in this mutex.
    pub open spec fn inv(&self, val: V) -> bool {
        Pred::inv(self.k@, val)
    }

    /// Acquire the mutex, spinning until the CAS succeeds.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn lock(&self) -> (guard: MutexGuard<K, V, Pred>)
        requires
            self.wf(),
        ensures
            guard.wf(self),
            self.inv(guard.view()),
    {
        let mut guard_opt: Option<MutexGuard<K, V, Pred>> = None;
        loop
            invariant_except_break
                self.wf(),
            ensures
                guard_opt is Some,
                guard_opt->Some_0.wf(self),
                self.inv(guard_opt->Some_0.view()),
        {
            let tracked mut owner_token_opt: Option<MutexOwnerToken<K, V, Pred>> = None;
            let tracked mut value_opt: Option<V> = None;

            assert(self.locked.well_formed());
            let ghost atomic_inst_id = self.locked.constant();
            let ghost inst_id = self.inst@.id();
            assert(atomic_inst_id == inst_id);
            let cas_result =
                atomic_with_ghost!(
                &self.locked => compare_exchange(false, true);
                update prev -> next;
                returning cas_res;
                ghost g => {
                    if cas_res is Ok {
                        assert(prev == false);
                        assert(next == true);
                        assert(MutexAtomicPred::<K, V, Pred>::atomic_inv(
                            atomic_inst_id,
                            prev,
                            g,
                        ));
                        assert(g.instance_id() == atomic_inst_id);
                        assert(g.instance_id() == inst_id);
                        assert(g.value() == prev);
                        let tracked acquire_result = self.inst.borrow().acquire(&mut g);
                        assert(g.value() == true);
                        let tracked value = acquire_result.1.get();
                        let tracked owner_token = acquire_result.2.get();

                        owner_token_opt = Some(owner_token);
                        value_opt = Some(value);
                    }
                }
            );

            if cas_result.is_ok() {
                let tracked owner_token = match owner_token_opt {
                    Some(t) => t,
                    None => proof_from_false(),
                };
                let tracked value = match value_opt {
                    Some(t) => t,
                    None => proof_from_false(),
                };
                let guard = MutexGuard { handle: Tracked(owner_token), token: Tracked(value) };
                guard_opt = Some(guard);
                break;
            }
        }

        assert(guard_opt is Some);
        let guard = guard_opt.unwrap();
        guard
    }

    /// Release the mutex by consuming the guard and storing its value back.
    pub fn unlock(&self, guard: MutexGuard<K, V, Pred>)
        requires
            self.wf(),
            guard.wf(self),
            self.inv(guard.view()),
    {
        let tracked owner_token = guard.handle.get();
        let tracked value = guard.token.get();

        assert(self.locked.well_formed());
        let ghost atomic_inst_id = self.locked.constant();
        let ghost inst_id = self.inst@.id();
        assert(atomic_inst_id == inst_id);
        atomic_with_ghost!(
            &self.locked => store(false);
            update prev -> next;
            ghost g => {
                assert(next == false);
                assert(MutexAtomicPred::<K, V, Pred>::atomic_inv(
                    atomic_inst_id,
                    prev,
                    g,
                ));
                assert(g.instance_id() == atomic_inst_id);
                assert(g.instance_id() == inst_id);
                assert(g.value() == prev);
                self.inst.borrow().release(value, &mut g, value, owner_token);
            }
        );
    }
}

} // verus!
