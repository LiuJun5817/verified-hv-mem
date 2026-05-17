use core::marker::PhantomData;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::atomic_ghost::*;
use vstd::invariant::InvariantPredicate;
use vstd::multiset::*;
use vstd::prelude::*;

tokenized_state_machine! {

MutexToks<K, V, Pred: InvariantPredicate<K, V>> {
    fields {
        #[sharding(constant)]
        pub k: K,

        #[sharding(constant)]
        pub pred: PhantomData<Pred>,

        #[sharding(storage_option)]
        pub storage: Option<V>,

        #[sharding(variable)]
        pub locked: bool,

        #[sharding(option)]
        pub owner: Option<()>,

        #[sharding(multiset)]
        pub pending: Multiset<()>,
    }

    init! {
        initialize(k: K, t: V) {
            require Pred::inv(k, t);
            init k = k;
            init pred = PhantomData;
            init locked = false;
            init storage = Option::Some(t);
            init owner = Option::None;
            init pending = Multiset::empty();
        }
    }

    /// Start acquiring the mutex. The caller is added to the pending set.
    transition! {
        acquire_start() {
            add pending += {()};
        }
    }

    /// Finish acquiring the mutex. The caller is removed from the pending set
    /// and becomes the owner. The stored object is withdrawn.
    transition! {
        acquire_end() {
            require(!pre.locked);
            remove pending -= {()};
            add owner += Some(());
            update locked = true;

            birds_eye let x = pre.storage->0;
            withdraw storage -= Some(x);

            assert Pred::inv(pre.k, x);
        }
    }

    /// Release the mutex. Return the owner token and deposit the object back.
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
        self.locked == (self.owner is Some)
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
        (self.owner is None) && !self.locked ==> (self.storage is Some)
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, k: K, t: V) { }

    #[inductive(acquire_start)]
    fn acquire_start_inductive(pre: Self, post: Self) {
        broadcast use group_multiset_axioms;
    }

    #[inductive(acquire_end)]
    fn acquire_end_inductive(pre: Self, post: Self) { }

    #[inductive(release)]
    fn release_inductive(pre: Self, post: Self, x: V) { }
}

}

verus! {

type MutexInstance<K, V, Pred> = MutexToks::Instance<K, V, Pred>;

type MutexLockedToken<K, V, Pred> = MutexToks::locked<K, V, Pred>;

type MutexOwnerToken<K, V, Pred> = MutexToks::owner<K, V, Pred>;

struct_with_invariants! {
    /// A mutex protecting an object of type `V` with invariant `Pred`.
    /// The mutex is identified by a key of type `K`.
    pub struct Mutex<K, V, Pred: InvariantPredicate<K, V>> {
        pub locked: AtomicBool<_, MutexLockedToken<K, V, Pred>, _>,
        pub inst: Tracked<MutexInstance<K, V, Pred>>,
        pub k: Ghost<K>,
    }

    pub closed spec fn wf(&self) -> bool {
        invariant on locked with (inst) is (v: bool, g: MutexLockedToken<K, V, Pred>) {
            &&& g.instance_id() == inst@.id()
            &&& g.value() == v
        }

        predicate {
            self.inst@.k() == self.k@
        }
    }
}

/// A guard object representing ownership of the mutex. The guard holds the owner token and
/// the protected value.
pub struct MutexGuard<K, V, Pred: InvariantPredicate<K, V>> {
    pub handle: Tracked<MutexOwnerToken<K, V, Pred>>,
    pub token: Tracked<V>,
}

impl<K, V, Pred: InvariantPredicate<K, V>> MutexGuard<K, V, Pred> {
    pub open spec fn wf(self, mutex: &Mutex<K, V, Pred>) -> bool {
        &&& self.handle@.instance_id() == mutex.inst@.id()
    }

    pub open spec fn view(self) -> V {
        self.token@
    }
}

impl<K, V, Pred: InvariantPredicate<K, V>> Mutex<K, V, Pred> {
    /// Create a new mutex protecting the value `val` with invariant `Pred`.
    /// The mutex is identified by the key `k`.
    pub fn new(Ghost(k): Ghost<K>, Tracked(val): Tracked<V>) -> (s: Self)
        requires
            Pred::inv(k, val),
        ensures
            s.wf(),
    {
        let tracked (
            Tracked(inst),
            Tracked(locked_tok),
            _,  // owner: None
            _,  // pending: empty
        ) = MutexToks::Instance::<K, V, Pred>::initialize(k, val, Option::Some(val));

        let inst = Tracked(inst);
        let locked = AtomicBool::new(Ghost(inst), false, Tracked(locked_tok));
        Mutex { locked, inst, k: Ghost(k) }
    }

    /// Check if the mutex invariant holds for a given value.
    pub open spec fn inv(&self, val: V) -> bool {
        Pred::inv(self.k@, val)
    }

    /// Acquire the mutex, returning a guard object that holds the protected value. This method spins
    /// until it can acquire the mutex.
    #[verifier::exec_allows_no_decreases_clause]
    pub fn lock(&self) -> (guard: MutexGuard<K, V, Pred>)
        requires
            self.wf(),
        ensures
            guard.wf(self),
            self.inv(guard.view()),
    {
        let tracked mut pending_token: Option<MutexToks::pending<K, V, Pred>> = None;

        // Step 1: add ourselves to pending (unconditionally)
        atomic_with_ghost!(
            &self.locked => no_op();
            ghost _g => {
                pending_token = Some(self.inst.borrow().acquire_start());
            }
        );

        // Step 2: spin until we can CAS locked from false → true
        loop
            invariant
                self.wf(),
                pending_token is Some,
                pending_token->0.instance_id() == self.inst@.id(),
        {
            let tracked mut owner_opt: Option<MutexOwnerToken<K, V, Pred>> = None;
            let tracked mut val_opt: Option<V> = None;

            let result =
                atomic_with_ghost!(
                &self.locked => compare_exchange(false, true);
                returning res;
                ghost g => {
                    if res is Ok {
                        let tracked pt = match pending_token {
                            Some(t) => t,
                            None => proof_from_false(),
                        };
                        let tracked r = self.inst.borrow().acquire_end(&mut g, pt);
                        let tracked v = r.1.get();
                        let tracked owner_tok = r.2.get();
                        pending_token = None;
                        owner_opt = Some(owner_tok);
                        val_opt = Some(v);
                    }
                }
            );

            if result.is_ok() {
                let tracked owner = match owner_opt {
                    Some(t) => t,
                    None => proof_from_false(),
                };
                let tracked val = match val_opt {
                    Some(t) => t,
                    None => proof_from_false(),
                };
                return MutexGuard { handle: Tracked(owner), token: Tracked(val) };
            }
        }
    }

    /// Release the mutex by consuming the guard. The protected value is returned to the mutex.
    pub fn unlock(&self, guard: MutexGuard<K, V, Pred>)
        requires
            self.wf(),
            guard.wf(self),
            self.inv(guard.view()),
    {
        let tracked owner = guard.handle.get();
        let tracked val = guard.token.get();

        atomic_with_ghost!(
            &self.locked => store(false);
            ghost g => {
                self.inst.borrow().release(val, val, &mut g, owner);
            }
        );
    }
}

} // verus!
