//! Per-zone exec/ghost structures.
//!
//! - [`ZoneState`]: linear ghost token holding one zone's entry in `ClosureSpec::zones`.
//! - [`BudgetZoneState`]: linear ghost token for `BudgetSpec::zones`.
//! - [`ZoneKey`] / [`ZoneRwContent`] / [`ZonePred`]: lock-predicate types for a zone's `RwLock`.
//! - [`Zone`]: exec struct holding a zone's `PCell<M>` memory set and its protecting `RwLock`.
//!   Generic over `P: HvMemProtocol` — use `Zone<PT, M, A, ClosureProtocol>` or
//!   `Zone<PT, M, A, BudgetProtocol>` for the two concrete assumptions.
use super::protocol::{
    BudgetGlobalState, BudgetProtocol, BudgetZoneState, ClosureGlobalState, ClosureProtocol,
    ClosureZoneState, HvMemProtocol,
};
use super::spec::budget::zone_budget;
use super::spec::closure::all_regions;
use super::spec::{BudgetZoneToken, ClosureZoneToken, GhostZone, ZoneStateOps};
use crate::{
    address::region::MemoryRegion,
    bitmap_allocator::bitmap_trait::BitmapAllocator,
    global_allocator::GlobalAllocator,
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

/// Ghost key for a `Zone`'s `RwLock`.
///
/// Binds the lock to a specific `PCell<M>` (via `cell_id`), to the
/// spec instance (via `mem_inst_id`), and to the allocator instance
/// (via `alloc_inst_id`), so the predicate can express
/// "the `PointsTo` inside the lock belongs to this cell, the
/// `ZoneState` token belongs to this spec instance, and the memory
/// set was built for this allocator instance".
pub struct ZoneKey {
    /// `PCell::id()` of the zone's `mem_set` cell.
    pub cell_id: CellId,
    /// Spec (ClosureSpec / BudgetSpec) instance id shared by the whole hypervisor.
    pub mem_inst_id: InstanceId,
    /// Global allocator instance id — must match `M::inst_id()` of the stored memory set.
    pub alloc_inst_id: InstanceId,
}

/// Tracked content protected by a `Zone`'s `RwLock`.
///
/// Generic over `P: HvMemProtocol`: the concrete `ZoneToken` type depends on
/// which spec assumption is in use (`ZoneState` for ClosureProtocol,
/// `BudgetZoneState` for BudgetProtocol).
pub tracked struct ZoneRwContent<M, P> where P: HvMemProtocol {
    /// Permission to read/write the zone's exec `mem_set` PCell.
    pub mem_set_perm: PointsTo<M>,
    /// Per-zone ghost token (map-sharded `zones[zid]` for the active spec).
    pub zone_state: P::ZoneToken,
}

/// Phantom struct that carries the `Zone`-level `InvariantPredicate`.
pub struct ZonePred<PT, M, A, P> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
    P: HvMemProtocol,
 {
    pub _phantom: PhantomData<(PT, M, A, P)>,
}

impl<PT, M, A, P> InvariantPredicate<ZoneKey, ZoneRwContent<M, P>> for ZonePred<PT, M, A, P> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
    P: HvMemProtocol,
 {
    /// The content is well-formed when:
    /// - `mem_set_perm` is initialised and points to the key's cell,
    /// - the wrapped memory set satisfies its own invariant,
    /// - the memory set's allocator instance matches the key's `alloc_inst_id`, and
    /// - `zone_state` belongs to the key's spec instance.
    open spec fn inv(k: ZoneKey, v: ZoneRwContent<M, P>) -> bool {
        &&& v.mem_set_perm.is_init()
        &&& v.mem_set_perm@.pcell === k.cell_id
        &&& v.mem_set_perm@.mem_contents->Init_0.invariants()
        &&& v.mem_set_perm@.mem_contents->Init_0.inst_id() == k.alloc_inst_id
        &&& v.zone_state.wf(k.mem_inst_id)
    }
}

/// An exec struct representing one zone's memory, protected by an `RwLock`.
///
/// Layout (mirrors `GlobalAllocator`'s PCell + Mutex pattern, but with
/// read-write instead of exclusive locking):
///
/// ```text
///  RwLock<ZoneRwContent<M, P>>
///      .mem_set_perm : PointsTo<M>   <- cell permission  ┐ protected by
///      .zone_state   : P::ZoneToken  <- ghost token       ┘ RwLock
///
///  PCell<M>   <- exec memory set, accessed only while lock is held
/// ```
///
/// Multiple CPUs from the **same zone** can hold read guards concurrently
/// (e.g., for page-table walks).  A write guard gives exclusive access for
/// operations that mutate the memory set (insert/remove region).
pub struct Zone<PT, M, A, P> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
    P: HvMemProtocol,
 {
    /// Exec memory set — written only while the write guard is held.
    pub mem_set: PCell<M>,
    /// RwLock protecting `ZoneRwContent<M, P>` with `ZoneKey` predicate.
    pub lock: RwLock<ZoneKey, ZoneRwContent<M, P>, ZonePred<PT, M, A, P>>,
    /// Zone identifier.
    pub zone_id: usize,
    /// Phantom data for unused type parameters.
    pub _phantom: PhantomData<(PT, A, P)>,
}

impl<PT, M, A, P> Zone<PT, M, A, P> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
    P: HvMemProtocol,
 {
    /// Structural well-formedness:
    /// - the `RwLock` is internally consistent, and
    /// - the lock's ghost key `cell_id` matches `self.mem_set.id()`.
    ///
    /// The stronger invariant that `PointsTo.pcell == cell_id` and
    /// `ZoneState.mem_inst_id == k.mem_inst_id` is captured by `ZonePred` and
    /// enforced every time the lock is acquired or released.
    pub open spec fn wf(&self) -> bool {
        &&& self.lock.wf()
        &&& self.lock.k@.cell_id == self.mem_set.id()
    }

    /// The HvMemSpec-instance ID of this zone, obtained from the lock's ghost key.
    pub open spec fn mem_inst_id(&self) -> InstanceId {
        self.lock.k@.mem_inst_id
    }

    /// The allocator instance ID of this zone, obtained from the lock's ghost key.
    pub open spec fn alloc_inst_id(&self) -> InstanceId {
        self.lock.k@.alloc_inst_id
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
        Ghost(mem_inst_id): Ghost<InstanceId>,
        Ghost(alloc_inst_id): Ghost<InstanceId>,
        Tracked(zone_state): Tracked<P::ZoneToken>,
    ) -> (res: Self)
        requires
            zone_state.wf(mem_inst_id),
            mem_set.inst_id() == alloc_inst_id,
        ensures
            res.wf(),
            res.lock.k@.mem_inst_id == mem_inst_id,
            res.lock.k@.alloc_inst_id == alloc_inst_id,
            res.zone_id == zone_id,
    {
        // Store the exec mem_set in a fresh PCell.
        let (mem_set_cell, Tracked(mem_set_perm)) = PCell::new(mem_set);

        // Bundle permission + ghost token into the lock content.
        let tracked zone_rw_content = ZoneRwContent::<M, P> { mem_set_perm, zone_state };

        // Build the ZoneKey (evaluated in spec mode via Ghost(…)).
        let zone_key = Ghost(
            ZoneKey { cell_id: mem_set_cell.id(), mem_inst_id, alloc_inst_id },
        );

        // Admit ZonePred::inv; dischargeable from PCell::new postconditions,
        // zone_state.wf(mem_inst_id) from the precondition, and the caller's
        // responsibility to supply a mem_set satisfying M::invariants().
        proof {
            assume(ZonePred::<PT, M, A, P>::inv(zone_key@, zone_rw_content));
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
        RwWriteGuard<ZoneKey, ZoneRwContent<M, P>, ZonePred<PT, M, A, P>>,
    ))
        requires
            self.wf(),
        ensures
            res.0.invariants(),
            res.0.inst_id() == self.lock.k@.alloc_inst_id,
            res.1.wf(&self.lock),
            res.1.token.mem_set_perm@.pcell == self.mem_set.id(),
            !res.1.token.mem_set_perm.is_init(),
    {
        let RwWriteGuard { handle, token } = self.lock.lock_write();
        let tracked mut content: ZoneRwContent<M, P> = token.get();
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
        guard: RwWriteGuard<ZoneKey, ZoneRwContent<M, P>, ZonePred<PT, M, A, P>>,
    )
        requires
            self.wf(),
            guard.wf(&self.lock),
            guard.token.mem_set_perm@.pcell == self.mem_set.id(),
            !guard.token.mem_set_perm.is_init(),
    {
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, P> = token.get();
        self.mem_set.put(Tracked(&mut content.mem_set_perm), mem_set);
        proof {
            assume(ZonePred::<PT, M, A, P>::inv(self.lock.k@, content));
        }
        self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });
    }

    /// Acquire shared (read) access to this zone's memory set.
    ///
    /// Multiple readers may hold a read guard concurrently.  Use
    /// `RwReadGuard::borrow` + `PCell::borrow` to obtain a `&M` reference.
    pub fn lock_read(&self) -> (res: RwReadGuard<
        ZoneKey,
        ZoneRwContent<M, P>,
        ZonePred<PT, M, A, P>,
    >)
        requires
            self.wf(),
        ensures
            res.wf(&self.lock),
    {
        self.lock.lock_read()
    }

    /// Release the read lock acquired by `lock_read`.
    pub fn unlock_read(
        &self,
        guard: RwReadGuard<ZoneKey, ZoneRwContent<M, P>, ZonePred<PT, M, A, P>>,
    )
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
        guard: &'a RwReadGuard<ZoneKey, ZoneRwContent<M, P>, ZonePred<PT, M, A, P>>,
    ) -> (res: &'a M)
        requires
            self.wf(),
            guard.wf(&self.lock),
    {
        // `self.lock.inst` is borrowed for `'a` (from `&'a self`).
        // `guard.handle`   is borrowed for `'a` (from `&'a guard`).
        // `read_guard` yields a ghost `&'a ZoneRwContent<M, P>`, so the field borrow
        // `&mem_set_perm` also carries lifetime `'a`, which flows through
        // `PCell::borrow` into the returned `&'a M`.
        let tracked ZoneRwContent::<M, P> { mem_set_perm, .. } = self.lock.inst.borrow().read_guard(
            guard.handle@.element(),
            guard.handle.borrow(),
        );
        // TODO: how to prove this?
        assume(mem_set_perm.is_init());
        assume(mem_set_perm@.pcell == self.mem_set.id());
        self.mem_set.borrow(Tracked(&mem_set_perm))
    }
}

/// Concrete `BudgetProtocol` implementation for `Zone`.
///
/// These methods take a shared `Tracked<&BudgetGlobalState>` instead of
/// `Tracked<&mut P::GlobalState>`, because `BudgetSpec::insert_region` /
/// `remove_region` are zone-local transitions: they only consume/produce the
/// per-zone `zones[zid]` map-sharded token and access `BudgetSpecInstance`
/// (constant-sharded) as a shared reference.
///
/// This lets callers hold only the HvMem **read** lock rather than the write lock.
impl<PT, M, A> Zone<PT, M, A, BudgetProtocol> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
 {
    /// Insert `region` into this zone using only a shared borrow of the global state.
    ///
    /// Returns `Err(())` if `region` is invalid or overlaps an existing mapping.
    pub fn insert_region(
        &self,
        allocator: &GlobalAllocator<A>,
        Tracked(gs): Tracked<&BudgetGlobalState>,
        region: MemoryRegion,
    ) -> (res: Result<(), ()>)
        requires
            self.wf(),
            self.lock.k@.alloc_inst_id == allocator.inst_id(),
            allocator.invariants(),
        ensures
            res is Ok ==> self.wf(),
    {
        if !region.valid() {
            return Err(());
        }
        let (mut mem_set, guard) = self.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, BudgetProtocol> = token.get();

        if mem_set.overlaps_vmem(&region) {
            self.unlock_write(mem_set, RwWriteGuard { handle, token: Tracked(content) });
            return Err(());
        }
        mem_set.insert(allocator, region);

        proof {
            let tracked ZoneRwContent::<M, BudgetProtocol> { mem_set_perm, zone_state } = content;
            let tracked BudgetZoneState { zone_tok } = zone_state;
            // Targeted assumptions for BudgetSpec::insert_region preconditions.
            // Budget membership is trusted configuration; !contains_region and
            // !overlaps_vmem are confirmed (exec-side) before reaching this point.
            assume(zone_budget(zone_tok.key()).contains(region));
            assume(!zone_tok.value().contains_region(region));
            assume(!zone_tok.value().mem_set.overlaps_vmem(region));
            let tracked new_zone_tok = gs.inst.insert_region(zone_tok.key(), region, zone_tok);
            content =
            ZoneRwContent::<M, BudgetProtocol> {
                mem_set_perm,
                zone_state: BudgetZoneState { zone_tok: new_zone_tok },
            };
        }

        self.unlock_write(mem_set, RwWriteGuard { handle, token: Tracked(content) });
        Ok(())
    }

    /// Remove `region` from this zone using only a shared borrow of the global state.
    ///
    /// Returns `Err(())` if `region` is invalid or no region starts at `region.start`.
    pub fn remove_region(
        &self,
        allocator: &GlobalAllocator<A>,
        Tracked(gs): Tracked<&BudgetGlobalState>,
        region: MemoryRegion,
    ) -> (res: Result<(), ()>)
        requires
            self.wf(),
            self.lock.k@.alloc_inst_id == allocator.inst_id(),
            allocator.invariants(),
        ensures
            res is Ok ==> self.wf(),
    {
        if !region.valid() {
            return Err(());
        }
        let (mut mem_set, guard) = self.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, BudgetProtocol> = token.get();

        if !mem_set.has_region_starting_at(region.start) {
            self.unlock_write(mem_set, RwWriteGuard { handle, token: Tracked(content) });
            return Err(());
        }
        mem_set.remove(allocator, region.start);

        proof {
            let tracked ZoneRwContent::<M, BudgetProtocol> { mem_set_perm, zone_state } = content;
            let tracked BudgetZoneState { zone_tok } = zone_state;
            let tracked new_zone_tok = gs.inst.remove_region(zone_tok.key(), region, zone_tok);
            content =
            ZoneRwContent::<M, BudgetProtocol> {
                mem_set_perm,
                zone_state: BudgetZoneState { zone_tok: new_zone_tok },
            };
        }

        self.unlock_write(mem_set, RwWriteGuard { handle, token: Tracked(content) });
        Ok(())
    }
}

/// `ClosureProtocol` implementation for `Zone`: `insert_region` and `remove_region`.
///
/// `ClosureProtocol::insert_region` modifies `gs.region_closure_tok` globally, so
/// callers need an exclusive `&mut ClosureGlobalState` — which requires holding the
/// HvMem **write** lock.
impl<PT, M, A> Zone<PT, M, A, ClosureProtocol> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
 {
    /// Insert `region` into this zone under `ClosureProtocol`.
    ///
    /// The caller must hold the HvMem write lock to supply `&mut ClosureGlobalState`.
    ///
    /// Returns `Err(())` if `region` is invalid or overlaps an existing mapping.
    pub fn insert_region(
        &self,
        allocator: &GlobalAllocator<A>,
        Tracked(gs): Tracked<&mut ClosureGlobalState>,
        region: MemoryRegion,
    ) -> (res: Result<(), ()>)
        requires
            self.wf(),
            self.lock.k@.alloc_inst_id == allocator.inst_id(),
            allocator.invariants(),
        ensures
            res is Ok ==> self.wf(),
    {
        if !region.valid() {
            return Err(());
        }
        let (mut mem_set, guard) = self.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, ClosureProtocol> = token.get();
        if mem_set.overlaps_vmem(&region) {
            self.unlock_write(mem_set, RwWriteGuard { handle, token: Tracked(content) });
            return Err(());
        }
        mem_set.insert(allocator, region);
        proof {
            let tracked ZoneRwContent::<M, ClosureProtocol> { mem_set_perm, zone_state } = content;
            // Targeted assumptions for the new ClosureProtocol::insert_region preconditions.
            // These conditions are checked exec-side (valid/overlaps) or are trusted
            // configuration properties (all_regions membership, !region_closure).
            assume(!zone_state.ghost_zone().contains_region(region));
            assume(!zone_state.ghost_zone().mem_set.overlaps_vmem(region));
            assume(region.spec_valid());
            assume(all_regions().contains(region));
            assume(!gs.region_closure().contains(region));
            let tracked new_zone_state = ClosureProtocol::insert_region(gs, zone_state, region);
            content =
            ZoneRwContent::<M, ClosureProtocol> { mem_set_perm, zone_state: new_zone_state };
        }
        self.unlock_write(mem_set, RwWriteGuard { handle, token: Tracked(content) });
        Ok(())
    }

    /// Remove `region` from this zone under `ClosureProtocol`.
    ///
    /// Returns `Err(())` if `region` is invalid or no region starts at `region.start`.
    pub fn remove_region(
        &self,
        allocator: &GlobalAllocator<A>,
        Tracked(gs): Tracked<&mut ClosureGlobalState>,
        region: MemoryRegion,
    ) -> (res: Result<(), ()>)
        requires
            self.wf(),
            self.lock.k@.alloc_inst_id == allocator.inst_id(),
            allocator.invariants(),
        ensures
            res is Ok ==> self.wf(),
    {
        if !region.valid() {
            return Err(());
        }
        let (mut mem_set, guard) = self.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, ClosureProtocol> = token.get();
        if !mem_set.has_region_starting_at(region.start) {
            self.unlock_write(mem_set, RwWriteGuard { handle, token: Tracked(content) });
            return Err(());
        }
        mem_set.remove(allocator, region.start);
        proof {
            let tracked ZoneRwContent::<M, ClosureProtocol> { mem_set_perm, zone_state } = content;
            let tracked new_zone_state = ClosureProtocol::remove_region(gs, zone_state, region);
            content =
            ZoneRwContent::<M, ClosureProtocol> { mem_set_perm, zone_state: new_zone_state };
        }
        self.unlock_write(mem_set, RwWriteGuard { handle, token: Tracked(content) });
        Ok(())
    }
}

} // verus!
