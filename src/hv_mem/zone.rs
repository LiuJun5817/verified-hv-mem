//! Single-zone memory abstractions.
//!
//! This module defines:
//! - `SpecZoneMem`: spec-level zone view used by top-level invariants.
//! - `ZoneMemInner`: mutable zone state (currently `mem_set`).
//! - `ZoneMem`: lock-protected wrapper (`RwLock<ZoneMemInner, ...>`) with `read`/`write` accessors.
//!
//! `hv_mem::mod` composes multiple `ZoneMem` values into the system-level memory model.
use crate::{
    bitmap_allocator::bitmap_trait::BitmapAllocator,
    memory_set::{MemorySet, SpecMemorySet},
    page_table::PageTable,
};
use core::marker::PhantomData;
use vstd::prelude::*;
use vstd::rwlock::{ReadHandle, RwLock, RwLockPredicate, WriteHandle};

verus! {

/// A spec-mode view for one zone.
pub struct SpecZoneMem {
    pub zone_id: nat,
    pub inst_id: InstanceId,
    pub mem_set: SpecMemorySet,
}

impl SpecZoneMem {
    /// Well-formedness
    pub open spec fn wf(&self) -> bool {
        self.mem_set.wf()
    }
}

/// The lock-protected mutable data of one zone.
pub struct ZoneMemInner<PT, M, A> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator {
    pub mem_set: M,
    pub _phantom: PhantomData<(PT, A)>,
}

impl<PT, M, A> ZoneMemInner<PT, M, A> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
 {
    pub open spec fn invariants(&self) -> bool {
        self.mem_set.invariants()
    }
}

/// Key shared with the lock predicate.
pub ghost struct ZoneMemLockKey {
    pub zone_inst_id: InstanceId,
    pub mem_set_view: SpecMemorySet,
}

/// Predicate used by `ZoneMem`'s reader-writer lock.
pub struct ZoneMemRwLockPred<PT, M, A> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
 {
    pub lock_key: ZoneMemLockKey,
    pub _phantom: PhantomData<(PT, M, A)>,
}

impl<PT, M, A> RwLockPredicate<ZoneMemInner<PT, M, A>> for ZoneMemRwLockPred<PT, M, A> where
    PT: PageTable<A>,
    M: MemorySet<PT, A>,
    A: BitmapAllocator,
 {
    open spec fn inv(self, inner: ZoneMemInner<PT, M, A>) -> bool {
        &&& inner.invariants()
        &&& inner.mem_set.inst_id() == self.lock_key.zone_inst_id
        &&& inner.mem_set.view() == self.lock_key.mem_set_view
    }
}

/// A concrete struct for one zone's memory, containing the zone id and a lock-protected inner state.
///
/// Note: Here we don't use the `PCell + Lock` pattern (as in `GlobalAllocator`) because the `RwLock` in
/// `vstd` already includes a `PCell`. We can directly wrap an exec type (`ZoneMemInner`) with the `RwLock`.
pub struct ZoneMem<PT, M, A> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator {
    pub zone_id: usize,
    pub zone_lock: RwLock<ZoneMemInner<PT, M, A>, ZoneMemRwLockPred<PT, M, A>>,
}

impl<PT, M, A> ZoneMem<PT, M, A> where PT: PageTable<A>, M: MemorySet<PT, A>, A: BitmapAllocator {
    /// View as an abstract `SpecZoneMem` for use in system-level invariants.
    pub open spec fn view(&self) -> SpecZoneMem {
        SpecZoneMem {
            zone_id: self.zone_id as nat,
            inst_id: self.zone_lock.pred().lock_key.zone_inst_id,
            mem_set: self.zone_lock.pred().lock_key.mem_set_view,
        }
    }

    /// Zone-level invariants that must be preserved across all operations.
    pub open spec fn invariants(&self) -> bool {
        &&& self.view().wf()
    }
    
    /// Construct one zone memory object from an already-initialized memory set.
    pub fn new(zone_id: usize, mem_set: M) -> (res: Self)
        requires
            mem_set.invariants(),
        ensures
            res.zone_id == zone_id,
            res.view().inst_id == mem_set.inst_id(),
            res.view().mem_set == mem_set@,
            res.invariants(),
    {
        let ghost mem_set_view = mem_set@;
        let ghost inst_id = mem_set.inst_id();
        proof {
            mem_set.lemma_invariants_implies_wf();
        }
        let zone_lock = RwLock::<ZoneMemInner<PT, M, A>, ZoneMemRwLockPred<PT, M, A>>::new(
            ZoneMemInner { mem_set, _phantom: PhantomData },
            Ghost(
                ZoneMemRwLockPred {
                    lock_key: ZoneMemLockKey { zone_inst_id: inst_id, mem_set_view },
                    _phantom: PhantomData,
                },
            ),
        );
        let zone_mem = Self { zone_id, zone_lock };
        proof {
            assert(zone_mem.view().wf());
            assert(zone_mem.invariants());
        }
        zone_mem
    }

    /// Acquire read access to the zone lock content.
    pub fn read(&self) -> (res: ReadHandle<
        '_,
        ZoneMemInner<PT, M, A>,
        ZoneMemRwLockPred<PT, M, A>,
    >)
        requires
            self.invariants(),
       ensures
            res.rwlock() == self.zone_lock,
            res.view().invariants(),
            res.view().mem_set.inst_id() == self.view().inst_id,
            res.view().mem_set.view() == self.view().mem_set,
            self.invariants(),
    {
        self.zone_lock.acquire_read()
    }

    /// Acquire write access to the zone lock content.
    pub fn write(&self) -> (res: (
        ZoneMemInner<PT, M, A>,
        WriteHandle<'_, ZoneMemInner<PT, M, A>, ZoneMemRwLockPred<PT, M, A>>,
    ))
        requires
            self.invariants(),
        ensures
            res.1.rwlock() == self.zone_lock,
            res.0.invariants(),
            res.0.mem_set.inst_id() == self.view().inst_id,
            res.0.mem_set.view() == self.view().mem_set,
            self.invariants(),
    {
        self.zone_lock.acquire_write()
    }
}

} // verus!
