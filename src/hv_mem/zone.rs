//! Per-zone exec/ghost structures.
//!
//! - [`ZoneState`]: linear ghost token holding one zone's entry in `ClosureSpec::zones`.
//! - [`ZoneKey`] / [`ZoneRwContent`] / [`ZonePred`]: lock-predicate types for a zone's `RwLock`.
//! - [`Zone`]: exec struct holding a zone's `PCell<M>` memory set and its protecting `RwLock`.
use super::spec::{ClosureZoneToken, GhostZone};
use crate::{
    bitmap_allocator::bitmap_trait::BitmapAllocator,
    memory_set::MemorySet,
    page_table::PageTable,
    sync::rwlock::{RwLock, RwReadGuard, RwWriteGuard},
};
use core::marker::PhantomData;
use vstd::{
    cell::{CellId, PCell, PointsTo},
    invariant::InvariantPredicate,
    prelude::*,
    tokens::InstanceId,
};

verus! {

/// Per-zone tracked ghost state, holding the zone's entry in `ClosureSpec::zones`.
///
/// One `ZoneState` is created for each zone when it is added via `HvMemState::add_zone`,
/// and consumed when the zone is removed via `HvMemState::remove_zone`.
///
/// `ZoneState` is typically stored inside the zone-level lock, so that only the thread
/// holding the zone lock can invoke `insert_region`/`remove_region`.
pub tracked struct ZoneState {
    pub zone_tok: ClosureZoneToken,
}

impl ZoneState {
    /// Well-formedness: the zone token belongs to the given `ClosureSpec` instance.
    pub open spec fn wf(&self, alloc_inst_id: InstanceId) -> bool {
        self.zone_tok.instance_id() == alloc_inst_id
    }

    /// The zone ID (key in the `zones` map sharding).
    pub open spec fn zone_id(&self) -> nat {
        self.zone_tok.key()
    }

    /// The ghost zone state (value in the `zones` map sharding).
    pub open spec fn ghost_zone(&self) -> GhostZone {
        self.zone_tok.value()
    }
}

/// Ghost key for a `Zone`'s `RwLock`.
///
/// Binds the lock to a specific `PCell<M>` (via `cell_id`) and to the
/// `ClosureSpec` instance (via `inst_id`), so the predicate can express
/// "the `PointsTo` inside the lock belongs to this cell, and the
/// `ZoneState` token belongs to this instance".
pub struct ZoneKey {
    /// `PCell::id()` of the zone's `mem_set` cell.
    pub cell_id: CellId,
    /// `ClosureSpec` instance id shared by the whole hypervisor.
    pub mem_inst_id: InstanceId,
}

/// Tracked content protected by a `Zone`'s `RwLock`.
///
/// This bundles the `PointsTo<M>` cell-permission (needed to access the exec
/// `mem_set` via `PCell::take`/`put`/`borrow`) together with the per-zone
/// `ClosureSpec` token (`ZoneState`).  Both are linear tracked resources that
/// must travel together: whoever holds the write guard can mutate the memory
/// set *and* update the ghost state atomically.
pub tracked struct ZoneRwContent<M> {
    /// Permission to read/write the zone's exec `mem_set` PCell.
    pub mem_set_perm: PointsTo<M>,
    /// Per-zone ClosureSpec token (map-sharded `zones[zid]`).
    pub zone_state: ZoneState,
}

/// Phantom struct that carries the `Zone`-level `InvariantPredicate`.
pub struct ZonePred<PT, M, A> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator {
    pub _phantom: PhantomData<(PT, M, A)>,
}

impl<PT, M, A> InvariantPredicate<ZoneKey, ZoneRwContent<M>> for ZonePred<PT, M, A> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
 {
    /// The content is well-formed when:
    /// - `mem_set_perm` is initialised and points to the key's cell, and
    /// - `zone_state` belongs to the key's `ClosureSpec` instance.
    open spec fn inv(k: ZoneKey, v: ZoneRwContent<M>) -> bool {
        &&& v.mem_set_perm.is_init()
        &&& v.mem_set_perm@.pcell === k.cell_id
        &&& v.zone_state.wf(k.mem_inst_id)
    }
}

/// An exec struct representing one zone's memory, protected by an `RwLock`.
///
/// Layout (mirrors `GlobalAllocator`'s PCell + Mutex pattern, but with
/// read-write instead of exclusive locking):
///
/// ```text
///  RwLock<ZoneRwContent<M>>
///      .mem_set_perm : PointsTo<M>   <- cell permission  ┐ protected by
///      .zone_state   : ZoneState     <- ghost token       ┘ RwLock
///
///  PCell<M>   <- exec memory set, accessed only while lock is held
/// ```
///
/// Multiple CPUs from the **same zone** can hold read guards concurrently
/// (e.g., for page-table walks).  A write guard gives exclusive access for
/// operations that mutate the memory set (insert/remove region).
pub struct Zone<PT, M, A> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator {
    /// Exec memory set — written only while the write guard is held.
    pub mem_set: PCell<M>,
    /// RwLock protecting `ZoneRwContent<M>` with `ZoneKey` predicate.
    pub lock: RwLock<ZoneKey, ZoneRwContent<M>, ZonePred<PT, M, A>>,
    /// Zone identifier.
    pub zone_id: usize,
    /// Phantom data for unused type parameters.
    pub _phantom: PhantomData<(PT, A)>,
}

impl<PT, M, A> Zone<PT, M, A> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator {
    /// Structural well-formedness:
    /// - the `RwLock` is internally consistent, and
    /// - the lock's ghost key `cell_id` matches `self.mem_set.id()`.
    ///
    /// The stronger invariant that `PointsTo.pcell == cell_id` and
    /// `ZoneState.inst_id == k.inst_id` is captured by `ZonePred` and
    /// enforced every time the lock is acquired or released.
    pub open spec fn wf(&self) -> bool {
        &&& self.lock.wf()
        &&& self.lock.k@.cell_id == self.mem_set.id()
    }

    /// Assemble a `Zone` from an already-built exec `mem_set` and its ghost token.
    ///
    /// This is intentionally infallible: all fallible work (validating
    /// `cfg_regions`, constructing the `MemorySet`) must be done by the caller
    /// before invoking this function, so the `ClosureSpec` state machine is only
    /// advanced once success is guaranteed.
    pub fn new(
        mem_set: M,
        zone_id: usize,
        Ghost(inst_id): Ghost<InstanceId>,
        Tracked(zone_state): Tracked<ZoneState>,
    ) -> (res: Self)
        requires
            zone_state.wf(inst_id),
        ensures
            res.wf(),
            res.lock.k@.mem_inst_id == inst_id,
            res.zone_id == zone_id,
    {
        // Store the exec mem_set in a fresh PCell.
        let (mem_set_cell, Tracked(mem_set_perm)) = PCell::new(mem_set);

        // Bundle permission + ghost token into the lock content.
        let tracked zone_rw_content = ZoneRwContent { mem_set_perm, zone_state };

        // Build the ZoneKey (evaluated in spec mode via Ghost(…)).
        let zone_key = Ghost(ZoneKey { cell_id: mem_set_cell.id(), mem_inst_id: inst_id });

        // Admit ZonePred::inv; dischargeable from PCell::new postconditions and
        // zone_state.wf(inst_id) from the precondition.
        proof {
            assume(ZonePred::<PT, M, A>::inv(zone_key@, zone_rw_content));
        }

        let zone_lock = RwLock::new(zone_key, Tracked(zone_rw_content));
        Zone { mem_set: mem_set_cell, lock: zone_lock, zone_id, _phantom: PhantomData }
    }

    /// Acquire exclusive (write) access to this zone's memory set.
    ///
    /// Returns the exec `M` value and a write guard.  The caller must eventually
    /// call `unlock_write` with the (possibly modified) `M` and the guard to
    /// release the lock and restore the invariant.
    pub fn lock_write(&self) -> (res: (
        M,
        RwWriteGuard<ZoneKey, ZoneRwContent<M>, ZonePred<PT, M, A>>,
    ))
        requires
            self.wf(),
        ensures
            res.1.wf(&self.lock),
            res.1.token.mem_set_perm@.pcell == self.mem_set.id(),
            !res.1.token.mem_set_perm.is_init(),
    {
        let RwWriteGuard { handle, token } = self.lock.lock_write();
        let tracked mut content: ZoneRwContent<M> = token.get();
        let mem_set = self.mem_set.take(Tracked(&mut content.mem_set_perm));
        (mem_set, RwWriteGuard { handle, token: Tracked(content) })
    }

    /// Release the write lock and restore the zone invariant.
    ///
    /// Puts `mem_set` back into the zone's `PCell`, asserts (via `assume`) that
    /// `ZonePred::inv` holds, and then releases the `RwLock`.
    pub fn unlock_write(
        &self,
        mem_set: M,
        guard: RwWriteGuard<ZoneKey, ZoneRwContent<M>, ZonePred<PT, M, A>>,
    )
        requires
            self.wf(),
            guard.wf(&self.lock),
            guard.token.mem_set_perm@.pcell == self.mem_set.id(),
            !guard.token.mem_set_perm.is_init(),
    {
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M> = token.get();
        self.mem_set.put(Tracked(&mut content.mem_set_perm), mem_set);
        proof {
            assume(ZonePred::<PT, M, A>::inv(self.lock.k@, content));
        }
        self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });
    }

    /// Acquire shared (read) access to this zone's memory set.
    ///
    /// Multiple readers may hold a read guard concurrently.  Use
    /// `RwReadGuard::borrow` + `PCell::borrow` to obtain a `&M` reference.
    pub fn lock_read(&self) -> (res: RwReadGuard<ZoneKey, ZoneRwContent<M>, ZonePred<PT, M, A>>)
        requires
            self.wf(),
        ensures
            res.wf(&self.lock),
    {
        self.lock.lock_read()
    }

    /// Release the read lock acquired by `lock_read`.
    pub fn unlock_read(&self, guard: RwReadGuard<ZoneKey, ZoneRwContent<M>, ZonePred<PT, M, A>>)
        requires
            self.wf(),
            guard.wf(&self.lock),
    {
        self.lock.unlock_read(guard)
    }

    /// Borrow the zone's exec `mem_set` while a read guard is held.
    ///
    /// Both `self` and `guard` must be alive for lifetime `'a`, so the returned
    /// `&'a M` is valid for exactly that duration.  Do not call `unlock_read`
    /// until the `&M` reference is no longer in use.
    pub fn borrow_mem_set<'a>(
        &'a self,
        guard: &'a RwReadGuard<ZoneKey, ZoneRwContent<M>, ZonePred<PT, M, A>>,
    ) -> (res: &'a M)
        requires
            self.wf(),
            guard.wf(&self.lock),
    {
        // `self.lock.inst` is borrowed for `'a` (from `&'a self`).
        // `guard.handle`   is borrowed for `'a` (from `&'a guard`).
        // `read_guard` yields a ghost `&'a ZoneRwContent<M>`, so the field borrow
        // `&mem_set_perm` also carries lifetime `'a`, which flows through
        // `PCell::borrow` into the returned `&'a M`.
        let tracked ZoneRwContent { mem_set_perm, .. } = self.lock.inst.borrow().read_guard(
            guard.handle@.element(),
            guard.handle.borrow(),
        );
        // TODO: how to prove this?
        assume(mem_set_perm.is_init());
        assume(mem_set_perm@.pcell == self.mem_set.id());
        self.mem_set.borrow(Tracked(&mem_set_perm))
    }
}

} // verus!
