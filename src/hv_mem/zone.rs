//! Per-zone exec/ghost structures.
//!
//! - [`ZoneRwContent`] / [`ZoneKey`] / [`ZonePred`]: lock-predicate types for a zone's `RwLock`.
//! - [`Zone`]: exec struct holding a zone's CPU/IOMMU `PCell<M>` memory sets and its
//!   protecting `RwLock`.
//!   Generic over `P: ZoneGhostProtocol` — use `Zone<PT, M, A, BudgetProtocol, I>`.
//!
//! The CPU and IOMMU memory sets are kept in sync with slice tokens from separate
//! tokenized MMU instances.
use super::protocol::{BudgetGlobalState, BudgetProtocol, ZoneGhostProtocol, ZoneStateOps};
use super::spec::budget::{gic_region, zone_regions};
use crate::{
    address::region::MemoryRegion,
    bitmap_allocator::bitmap_trait::BitmapAllocator,
    global_allocator::GlobalAllocator,
    hardware::spec::MmuS2MapToken,
    hardware::{HardwareInstr, MmuHardware},
    model::convert::pt_s2map_inner,
    model::types::VmId,
    memory_set::MemorySet,
    page_table::{PageTable, SpecPTConstants},
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
/// Binds the lock to specific CPU/IOMMU `PCell<M>`s, to the
/// spec instance (via `mem_inst_id`), to the allocator instance
/// (via `alloc_inst_id`), and to the CPU and IOMMU MMU instances.
pub struct ZoneKey {
    /// Zone ID,
    pub zone_id: usize,
    /// `PCell::id()` of the zone's CPU `mem_set` cell.
    pub cpu_cell_id: CellId,
    /// `PCell::id()` of the zone's IOMMU `mem_set` cell.
    pub iommu_cell_id: CellId,
    /// Spec (ClosureSpec / BudgetSpec) instance id shared by the whole hypervisor.
    pub mem_inst_id: InstanceId,
    /// Global allocator instance id — must match `M::inst_id()` of the stored memory set.
    pub alloc_inst_id: InstanceId,
    /// `MmuSpec` instance id — the CPU `s2map` slice token in this lock belongs to it.
    pub mmu_inst_id: InstanceId,
    /// IOMMU `MmuSpec` instance id — the IOMMU `s2map` slice token belongs to it
    /// (a separate `MmuHardware` instance from the CPU one).
    pub iommu_mmu_inst_id: InstanceId,
    /// Shared page-table architecture used by the CPU/IOMMU memory sets.
    pub pt_constants: SpecPTConstants,
}

/// Tracked content protected by a `Zone`'s `RwLock`.
///
/// Generic over `P: ZoneGhostProtocol`: the concrete `ZoneToken` type depends on
/// which spec assumption is in use (`BudgetZoneState` for BudgetProtocol).
pub tracked struct ZoneRwContent<M, P> where P: ZoneGhostProtocol {
    /// Permission to read/write the zone's exec CPU `mem_set` PCell.
    pub cpu_mem_set_perm: PointsTo<M>,
    /// Permission to read/write the zone's exec IOMMU `mem_set` PCell.
    pub iommu_mem_set_perm: PointsTo<M>,
    /// Per-zone ghost token (map-sharded `zones[zid]` for the active spec).
    pub zone_state: P::ZoneToken,
    /// This zone's CPU MMU `s2map` slice token, kept in sync with the CPU
    /// `mem_set`'s mappings by [`ZonePred::inv`] — the lock-resident half of the
    /// per-vm sync point.
    pub s2map_tok: MmuS2MapToken,
    /// This zone's IOMMU `s2map` slice token (separate MMU instance), kept in sync
    /// with the IOMMU `mem_set`'s mappings by [`ZonePred::inv`].
    pub iommu_s2map_tok: MmuS2MapToken,
}

/// Phantom struct that carries the `Zone`-level `InvariantPredicate`.
pub struct ZonePred<PT, M, A, P, I> where
    PT: PageTable<A>,
    M: MemorySet<PT, A, I>,
    A: BitmapAllocator,
    P: ZoneGhostProtocol,
    I: HardwareInstr,
 {
    pub _phantom: PhantomData<(PT, M, A, P, I)>,
}

impl<PT, M, A, P, I> InvariantPredicate<ZoneKey, ZoneRwContent<M, P>> for ZonePred<
    PT,
    M,
    A,
    P,
    I,
> where
    PT: PageTable<A>,
    M: MemorySet<PT, A, I>,
    A: BitmapAllocator,
    P: ZoneGhostProtocol,
    I: HardwareInstr,
 {
    /// The content is well-formed when:
    /// - both `PointsTo`s are initialised and point to the key's cells,
    /// - the wrapped memory sets satisfy their own invariants,
    /// - the memory sets' allocator instance matches the key's `alloc_inst_id`,
    /// - `zone_state` belongs to the key's spec instance,
    /// - the ghost zone's CPU/IOMMU views mirror the exec memory sets' views, and
    /// - the CPU and IOMMU `s2map` slice tokens are synced with their memory sets.
    open spec fn inv(k: ZoneKey, v: ZoneRwContent<M, P>) -> bool {
        &&& v.cpu_mem_set_perm.is_init()
        &&& v.cpu_mem_set_perm@.pcell === k.cpu_cell_id
        &&& v.cpu_mem_set_perm@.mem_contents->Init_0.invariants()
        &&& v.cpu_mem_set_perm@.mem_contents->Init_0.inst_id() == k.alloc_inst_id
        &&& v.cpu_mem_set_perm@.mem_contents->Init_0.pt_constants() == k.pt_constants
        &&& v.iommu_mem_set_perm.is_init()
        &&& v.iommu_mem_set_perm@.pcell === k.iommu_cell_id
        &&& v.iommu_mem_set_perm@.mem_contents->Init_0.invariants()
        &&& v.iommu_mem_set_perm@.mem_contents->Init_0.inst_id() == k.alloc_inst_id
        &&& v.iommu_mem_set_perm@.mem_contents->Init_0.pt_constants() == k.pt_constants
        &&& v.zone_state.zone_id() == k.zone_id
        &&& v.zone_state.wf(k.mem_inst_id)
        &&& v.zone_state.ghost_zone().cpu_mem_set == v.cpu_mem_set_perm@.mem_contents->Init_0@
        &&& v.zone_state.ghost_zone().iommu_mem_set
            == v.iommu_mem_set_perm@.mem_contents->Init_0@
        // The CPU MMU `s2map` slice token belongs to the MMU instance, is keyed by this
        // zone's vm, and equals the projection of the stored CPU memory set's mappings —
        // i.e. the MMU is *synced* for this zone (the hv-controlled `s2map` half).
        &&& v.s2map_tok.instance_id() == k.mmu_inst_id
        &&& v.s2map_tok.key() == VmId(k.zone_id as nat)
        &&& v.s2map_tok.value() == pt_s2map_inner(
            v.cpu_mem_set_perm@.mem_contents->Init_0@.mappings,
        )
        // The IOMMU `s2map` slice token is *synced* with the IOMMU memory set.
        &&& v.iommu_s2map_tok.instance_id() == k.iommu_mmu_inst_id
        &&& v.iommu_s2map_tok.key() == VmId(k.zone_id as nat)
        &&& v.iommu_s2map_tok.value() == pt_s2map_inner(
            v.iommu_mem_set_perm@.mem_contents->Init_0@.mappings,
        )
    }
}

/// An exec struct representing one zone's memory, protected by an `RwLock`.
///
/// Multiple CPUs from the **same zone** can hold read guards concurrently
/// (e.g., for page-table walks).  A write guard gives exclusive access for
/// operations that mutate either visible memory set.
pub struct Zone<PT, M, A, P, I> where
    PT: PageTable<A>,
    M: MemorySet<PT, A, I>,
    A: BitmapAllocator,
    P: ZoneGhostProtocol,
    I: HardwareInstr,
 {
    /// Exec CPU memory set — written only while the write guard is held.
    pub cpu_mem_set: PCell<M>,
    /// Exec IOMMU memory set — written only while the write guard is held.
    pub iommu_mem_set: PCell<M>,
    /// RwLock protecting `ZoneRwContent<M, P>` with `ZoneKey` predicate.
    pub lock: RwLock<ZoneKey, ZoneRwContent<M, P>, ZonePred<PT, M, A, P, I>>,
    /// Zone identifier.
    pub zone_id: usize,
    /// Phantom data for unused type parameters.
    pub _phantom: PhantomData<(PT, A, P, I)>,
}

impl<PT, M, A, P, I> Zone<PT, M, A, P, I> where
    PT: PageTable<A>,
    M: MemorySet<PT, A, I>,
    A: BitmapAllocator,
    P: ZoneGhostProtocol,
    I: HardwareInstr,
 {
    /// Structural well-formedness:
    /// - the `RwLock` is internally consistent, and
    /// - the lock's ghost key matches the CPU/IOMMU `PCell` IDs.
    pub open spec fn wf(&self) -> bool {
        &&& self.lock.wf()
        &&& self.lock.k@.cpu_cell_id == self.cpu_mem_set.id()
        &&& self.lock.k@.iommu_cell_id == self.iommu_mem_set.id()
        &&& self.lock.k@.zone_id == self.zone_id
    }

    /// The HvMemSpec-instance ID of this zone, obtained from the lock's ghost key.
    pub open spec fn mem_inst_id(&self) -> InstanceId {
        self.lock.k@.mem_inst_id
    }

    /// The allocator instance ID of this zone, obtained from the lock's ghost key.
    pub open spec fn alloc_inst_id(&self) -> InstanceId {
        self.lock.k@.alloc_inst_id
    }

    /// The MMU instance ID of this zone, obtained from the lock's ghost key.
    pub open spec fn mmu_inst_id(&self) -> InstanceId {
        self.lock.k@.mmu_inst_id
    }

    /// The IOMMU MMU instance ID of this zone, obtained from the lock's ghost key.
    pub open spec fn iommu_mmu_inst_id(&self) -> InstanceId {
        self.lock.k@.iommu_mmu_inst_id
    }

    /// The page-table virtual-space bound of this zone's memory sets.
    pub open spec fn vspace_size(&self) -> nat {
        self.lock.k@.pt_constants.arch.vspace_size()
    }

    /// The page-table constants of this zone's memory sets.
    pub open spec fn pt_constants(&self) -> SpecPTConstants {
        self.lock.k@.pt_constants
    }

    /// Assemble a `Zone` from already-built exec CPU/IOMMU `mem_set`s and its ghost token.
    pub fn new(
        cpu_mem_set: M,
        iommu_mem_set: M,
        zone_id: usize,
        Ghost(mem_inst_id): Ghost<InstanceId>,
        Ghost(alloc_inst_id): Ghost<InstanceId>,
        Ghost(mmu_inst_id): Ghost<InstanceId>,
        Ghost(iommu_mmu_inst_id): Ghost<InstanceId>,
        Tracked(zone_state): Tracked<P::ZoneToken>,
        Tracked(s2map_tok): Tracked<MmuS2MapToken>,
        Tracked(iommu_s2map_tok): Tracked<MmuS2MapToken>,
    ) -> (res: Self)
        requires
            zone_state.wf(mem_inst_id),
            // The exec memory sets satisfy their own invariants and belong to the
            // shared allocator instance.
            cpu_mem_set.invariants(),
            iommu_mem_set.invariants(),
            cpu_mem_set.inst_id() == alloc_inst_id,
            iommu_mem_set.inst_id() == alloc_inst_id,
            cpu_mem_set.pt_constants() == iommu_mem_set.pt_constants(),
            // The ghost zone token is keyed by this zone and mirrors both exec
            // memory sets — the ghost/exec sync point `ZonePred::inv` pins.
            zone_state.zone_id() == zone_id as nat,
            zone_state.ghost_zone().cpu_mem_set == cpu_mem_set@,
            zone_state.ghost_zone().iommu_mem_set == iommu_mem_set@,
            // The freshly minted CPU slice token (from `MmuHardware::add_vm`) is keyed by
            // this zone's vm, belongs to the MMU instance, and projects the CPU mem_set.
            s2map_tok.instance_id() == mmu_inst_id,
            s2map_tok.key() == VmId(zone_id as nat),
            s2map_tok.value() == pt_s2map_inner(cpu_mem_set@.mappings),
            // Likewise for the IOMMU slice token (separate MMU instance).
            iommu_s2map_tok.instance_id() == iommu_mmu_inst_id,
            iommu_s2map_tok.key() == VmId(zone_id as nat),
            iommu_s2map_tok.value() == pt_s2map_inner(iommu_mem_set@.mappings),
        ensures
            res.wf(),
            res.lock.k@.mem_inst_id == mem_inst_id,
            res.lock.k@.alloc_inst_id == alloc_inst_id,
            res.lock.k@.mmu_inst_id == mmu_inst_id,
            res.lock.k@.iommu_mmu_inst_id == iommu_mmu_inst_id,
            res.lock.k@.pt_constants == cpu_mem_set.pt_constants(),
            res.zone_id == zone_id,
    {
        // Store the exec CPU/IOMMU mem_sets in fresh PCells.
        let (cpu_mem_set_cell, Tracked(cpu_mem_set_perm)) = PCell::new(cpu_mem_set);
        let (iommu_mem_set_cell, Tracked(iommu_mem_set_perm)) = PCell::new(iommu_mem_set);

        // Bundle permission + ghost tokens into the lock content.
        let tracked zone_rw_content = ZoneRwContent::<M, P> {
            cpu_mem_set_perm,
            iommu_mem_set_perm,
            zone_state,
            s2map_tok,
            iommu_s2map_tok,
        };

        // Build the ZoneKey (evaluated in spec mode via Ghost(…)).
        let zone_key = Ghost(
            ZoneKey {
                zone_id,
                cpu_cell_id: cpu_mem_set_cell.id(),
                iommu_cell_id: iommu_mem_set_cell.id(),
                mem_inst_id,
                alloc_inst_id,
                mmu_inst_id,
                iommu_mmu_inst_id,
                pt_constants: cpu_mem_set.pt_constants(),
            },
        );

        // ZonePred::inv holds at birth: the PointsTo clauses come from `PCell::new`,
        // and every remaining clause (mem-set invariants, ghost-zone mirror, synced
        // slice tokens) is a `Zone::new` precondition.
        proof {
            assert(ZonePred::<PT, M, A, P, I>::inv(zone_key@, zone_rw_content));
        }

        let zone_lock = RwLock::new(zone_key, Tracked(zone_rw_content));
        Zone {
            cpu_mem_set: cpu_mem_set_cell,
            iommu_mem_set: iommu_mem_set_cell,
            lock: zone_lock,
            zone_id,
            _phantom: PhantomData,
        }
    }

    /// Acquire exclusive (write) access to this zone's CPU memory set.
    pub fn lock_write(&self) -> (res: (
        M,
        RwWriteGuard<ZoneKey, ZoneRwContent<M, P>, ZonePred<PT, M, A, P, I>>,
    ))
        requires
            self.wf(),
        ensures
            res.0.invariants(),
            res.0.inst_id() == self.lock.k@.alloc_inst_id,
            res.0.pt_constants() == self.lock.k@.pt_constants,
            res.1.wf(&self.lock),
            res.1.token.cpu_mem_set_perm@.pcell == self.cpu_mem_set.id(),
            !res.1.token.cpu_mem_set_perm.is_init(),
            res.1.token.iommu_mem_set_perm@.pcell == self.iommu_mem_set.id(),
            res.1.token.iommu_mem_set_perm.is_init(),
            res.1.token.iommu_mem_set_perm@.mem_contents->Init_0.invariants(),
            res.1.token.iommu_mem_set_perm@.mem_contents->Init_0.inst_id()
                == self.lock.k@.alloc_inst_id,
            res.1.token.iommu_mem_set_perm@.mem_contents->Init_0.pt_constants()
                == self.lock.k@.pt_constants,
            res.1.token@.zone_state.zone_id() == self.lock.k@.zone_id,
            res.1.token@.zone_state.wf(self.lock.k@.mem_inst_id),
            res.1.token@.zone_state.ghost_zone().cpu_mem_set == res.0@,
            res.1.token@.zone_state.ghost_zone().iommu_mem_set
                == res.1.token.iommu_mem_set_perm@.mem_contents->Init_0@,
            // Surface the CPU MMU slice token kept in the lock so the caller can thread
            // it through `mem_set.insert`/`remove` (forcing the maintenance instrs).
            res.1.token@.s2map_tok.instance_id() == self.lock.k@.mmu_inst_id,
            res.1.token@.s2map_tok.key() == VmId(self.lock.k@.zone_id as nat),
            res.1.token@.s2map_tok.value() == pt_s2map_inner(res.0@.mappings),
            // The IOMMU slice token is untouched by the CPU path; surface its synced
            // facts so the CPU `unlock_write` can re-establish the invariant.
            res.1.token@.iommu_s2map_tok.instance_id() == self.lock.k@.iommu_mmu_inst_id,
            res.1.token@.iommu_s2map_tok.key() == VmId(self.lock.k@.zone_id as nat),
            res.1.token@.iommu_s2map_tok.value() == pt_s2map_inner(
                res.1.token.iommu_mem_set_perm@.mem_contents->Init_0@.mappings,
            ),
    {
        let RwWriteGuard { handle, token } = self.lock.lock_write();
        let tracked mut content: ZoneRwContent<M, P> = token.get();
        let mem_set = self.cpu_mem_set.take(Tracked(&mut content.cpu_mem_set_perm));
        (mem_set, RwWriteGuard { handle, token: Tracked(content) })
    }

    /// Acquire exclusive (write) access to this zone's IOMMU memory set.
    pub fn lock_write_iommu(&self) -> (res: (
        M,
        RwWriteGuard<ZoneKey, ZoneRwContent<M, P>, ZonePred<PT, M, A, P, I>>,
    ))
        requires
            self.wf(),
        ensures
            res.0.invariants(),
            res.0.inst_id() == self.lock.k@.alloc_inst_id,
            res.0.pt_constants() == self.lock.k@.pt_constants,
            res.1.wf(&self.lock),
            res.1.token.cpu_mem_set_perm@.pcell == self.cpu_mem_set.id(),
            res.1.token.cpu_mem_set_perm.is_init(),
            res.1.token.cpu_mem_set_perm@.mem_contents->Init_0.invariants(),
            res.1.token.cpu_mem_set_perm@.mem_contents->Init_0.inst_id()
                == self.lock.k@.alloc_inst_id,
            res.1.token.cpu_mem_set_perm@.mem_contents->Init_0.pt_constants()
                == self.lock.k@.pt_constants,
            res.1.token.iommu_mem_set_perm@.pcell == self.iommu_mem_set.id(),
            !res.1.token.iommu_mem_set_perm.is_init(),
            res.1.token@.zone_state.zone_id() == self.lock.k@.zone_id,
            res.1.token@.zone_state.wf(self.lock.k@.mem_inst_id),
            res.1.token@.zone_state.ghost_zone().cpu_mem_set
                == res.1.token.cpu_mem_set_perm@.mem_contents->Init_0@,
            res.1.token@.zone_state.ghost_zone().iommu_mem_set == res.0@,
            // CPU MMU slice token (untouched by the IOMMU path) stays synced.
            res.1.token@.s2map_tok.instance_id() == self.lock.k@.mmu_inst_id,
            res.1.token@.s2map_tok.key() == VmId(self.lock.k@.zone_id as nat),
            res.1.token@.s2map_tok.value() == pt_s2map_inner(
                res.1.token.cpu_mem_set_perm@.mem_contents->Init_0@.mappings,
            ),
            // Surface the IOMMU slice token so the caller can thread it through
            // `mem_set.insert`/`remove` (with `iommu = true`), forcing the SMMU instrs.
            res.1.token@.iommu_s2map_tok.instance_id() == self.lock.k@.iommu_mmu_inst_id,
            res.1.token@.iommu_s2map_tok.key() == VmId(self.lock.k@.zone_id as nat),
            res.1.token@.iommu_s2map_tok.value() == pt_s2map_inner(res.0@.mappings),
    {
        let RwWriteGuard { handle, token } = self.lock.lock_write();
        let tracked mut content: ZoneRwContent<M, P> = token.get();
        let mem_set = self.iommu_mem_set.take(Tracked(&mut content.iommu_mem_set_perm));
        (mem_set, RwWriteGuard { handle, token: Tracked(content) })
    }

    /// Release the CPU write lock and restore the zone invariant.
    pub fn unlock_write(
        &self,
        mem_set: M,
        guard: RwWriteGuard<ZoneKey, ZoneRwContent<M, P>, ZonePred<PT, M, A, P, I>>,
    )
        requires
            self.wf(),
            guard.wf(&self.lock),
            guard.token.cpu_mem_set_perm@.pcell == self.cpu_mem_set.id(),
            !guard.token.cpu_mem_set_perm.is_init(),
            guard.token.iommu_mem_set_perm@.pcell == self.iommu_mem_set.id(),
            guard.token.iommu_mem_set_perm.is_init(),
            guard.token.iommu_mem_set_perm@.mem_contents->Init_0.invariants(),
            guard.token.iommu_mem_set_perm@.mem_contents->Init_0.inst_id()
                == self.lock.k@.alloc_inst_id,
            guard.token.iommu_mem_set_perm@.mem_contents->Init_0.pt_constants()
                == self.lock.k@.pt_constants,
            // Linking invariant: the mem_set being stored back satisfies M's own wf.
            mem_set.invariants(),
            mem_set.inst_id() == self.lock.k@.alloc_inst_id,
            mem_set.pt_constants() == self.lock.k@.pt_constants,
            // Ghost-token invariant: the zone_state in the guard is consistent with
            // the CPU mem_set being stored back and with this zone's lock key.
            guard.token@.zone_state.zone_id() == self.lock.k@.zone_id,
            guard.token@.zone_state.wf(self.lock.k@.mem_inst_id),
            guard.token@.zone_state.ghost_zone().cpu_mem_set == mem_set@,
            guard.token@.zone_state.ghost_zone().iommu_mem_set
                == guard.token.iommu_mem_set_perm@.mem_contents->Init_0@,
            // The CPU MMU slice token being stored back is keyed by this zone's vm and
            // projects the mem_set being stored back — restores the sync clause.
            guard.token@.s2map_tok.instance_id() == self.lock.k@.mmu_inst_id,
            guard.token@.s2map_tok.key() == VmId(self.lock.k@.zone_id as nat),
            guard.token@.s2map_tok.value() == pt_s2map_inner(mem_set@.mappings),
            // The IOMMU slice token (untouched by the CPU path) stays synced.
            guard.token@.iommu_s2map_tok.instance_id() == self.lock.k@.iommu_mmu_inst_id,
            guard.token@.iommu_s2map_tok.key() == VmId(self.lock.k@.zone_id as nat),
            guard.token@.iommu_s2map_tok.value() == pt_s2map_inner(
                guard.token.iommu_mem_set_perm@.mem_contents->Init_0@.mappings,
            ),
    {
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, P> = token.get();
        self.cpu_mem_set.put(Tracked(&mut content.cpu_mem_set_perm), mem_set);
        proof {
            assert(ZonePred::<PT, M, A, P, I>::inv(self.lock.k@, content)) by {
                assert(content.cpu_mem_set_perm.is_init());
                assert(content.cpu_mem_set_perm@.pcell === self.lock.k@.cpu_cell_id);
                assert(content.cpu_mem_set_perm@.mem_contents->Init_0.invariants());
                assert(content.cpu_mem_set_perm@.mem_contents->Init_0.inst_id()
                    == self.lock.k@.alloc_inst_id);
                assert(content.cpu_mem_set_perm@.mem_contents->Init_0.pt_constants()
                    == self.lock.k@.pt_constants);
                assert(content.iommu_mem_set_perm.is_init());
                assert(content.iommu_mem_set_perm@.pcell === self.lock.k@.iommu_cell_id);
                assert(content.iommu_mem_set_perm@.mem_contents->Init_0.invariants());
                assert(content.iommu_mem_set_perm@.mem_contents->Init_0.inst_id()
                    == self.lock.k@.alloc_inst_id);
                assert(content.iommu_mem_set_perm@.mem_contents->Init_0.pt_constants()
                    == self.lock.k@.pt_constants);
                assert(content.zone_state.zone_id() == self.lock.k@.zone_id);
                assert(content.zone_state.wf(self.lock.k@.mem_inst_id));
                assert(content.zone_state.ghost_zone().cpu_mem_set
                    == content.cpu_mem_set_perm@.mem_contents->Init_0@);
                assert(content.zone_state.ghost_zone().iommu_mem_set
                    == content.iommu_mem_set_perm@.mem_contents->Init_0@);
                // MMU sync clause: the slice token (unchanged by put) still projects
                // the CPU mem_set just stored back.
                assert(content.s2map_tok.instance_id() == self.lock.k@.mmu_inst_id);
                assert(content.s2map_tok.key() == VmId(self.lock.k@.zone_id as nat));
                assert(content.s2map_tok.value() == pt_s2map_inner(
                    content.cpu_mem_set_perm@.mem_contents->Init_0@.mappings,
                ));
                // IOMMU sync clause: untouched by the CPU path.
                assert(content.iommu_s2map_tok.instance_id() == self.lock.k@.iommu_mmu_inst_id);
                assert(content.iommu_s2map_tok.key() == VmId(self.lock.k@.zone_id as nat));
                assert(content.iommu_s2map_tok.value() == pt_s2map_inner(
                    content.iommu_mem_set_perm@.mem_contents->Init_0@.mappings,
                ));
            };
        }
        self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });
    }

    /// Release the IOMMU write lock and restore the zone invariant.
    pub fn unlock_write_iommu(
        &self,
        mem_set: M,
        guard: RwWriteGuard<ZoneKey, ZoneRwContent<M, P>, ZonePred<PT, M, A, P, I>>,
    )
        requires
            self.wf(),
            guard.wf(&self.lock),
            guard.token.cpu_mem_set_perm@.pcell == self.cpu_mem_set.id(),
            guard.token.cpu_mem_set_perm.is_init(),
            guard.token.cpu_mem_set_perm@.mem_contents->Init_0.invariants(),
            guard.token.cpu_mem_set_perm@.mem_contents->Init_0.inst_id()
                == self.lock.k@.alloc_inst_id,
            guard.token.cpu_mem_set_perm@.mem_contents->Init_0.pt_constants()
                == self.lock.k@.pt_constants,
            guard.token.iommu_mem_set_perm@.pcell == self.iommu_mem_set.id(),
            !guard.token.iommu_mem_set_perm.is_init(),
            mem_set.invariants(),
            mem_set.inst_id() == self.lock.k@.alloc_inst_id,
            mem_set.pt_constants() == self.lock.k@.pt_constants,
            guard.token@.zone_state.zone_id() == self.lock.k@.zone_id,
            guard.token@.zone_state.wf(self.lock.k@.mem_inst_id),
            guard.token@.zone_state.ghost_zone().cpu_mem_set
                == guard.token.cpu_mem_set_perm@.mem_contents->Init_0@,
            guard.token@.zone_state.ghost_zone().iommu_mem_set == mem_set@,
            // CPU MMU slice token stays synced with the (untouched) CPU mem_set.
            guard.token@.s2map_tok.instance_id() == self.lock.k@.mmu_inst_id,
            guard.token@.s2map_tok.key() == VmId(self.lock.k@.zone_id as nat),
            guard.token@.s2map_tok.value() == pt_s2map_inner(
                guard.token.cpu_mem_set_perm@.mem_contents->Init_0@.mappings,
            ),
            // The IOMMU slice token being stored back projects the IOMMU mem_set just
            // stored back — restores the IOMMU sync clause.
            guard.token@.iommu_s2map_tok.instance_id() == self.lock.k@.iommu_mmu_inst_id,
            guard.token@.iommu_s2map_tok.key() == VmId(self.lock.k@.zone_id as nat),
            guard.token@.iommu_s2map_tok.value() == pt_s2map_inner(mem_set@.mappings),
    {
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, P> = token.get();
        self.iommu_mem_set.put(Tracked(&mut content.iommu_mem_set_perm), mem_set);
        proof {
            assert(ZonePred::<PT, M, A, P, I>::inv(self.lock.k@, content)) by {
                assert(content.cpu_mem_set_perm.is_init());
                assert(content.cpu_mem_set_perm@.pcell === self.lock.k@.cpu_cell_id);
                assert(content.cpu_mem_set_perm@.mem_contents->Init_0.invariants());
                assert(content.cpu_mem_set_perm@.mem_contents->Init_0.inst_id()
                    == self.lock.k@.alloc_inst_id);
                assert(content.cpu_mem_set_perm@.mem_contents->Init_0.pt_constants()
                    == self.lock.k@.pt_constants);
                assert(content.iommu_mem_set_perm.is_init());
                assert(content.iommu_mem_set_perm@.pcell === self.lock.k@.iommu_cell_id);
                assert(content.iommu_mem_set_perm@.mem_contents->Init_0.invariants());
                assert(content.iommu_mem_set_perm@.mem_contents->Init_0.inst_id()
                    == self.lock.k@.alloc_inst_id);
                assert(content.iommu_mem_set_perm@.mem_contents->Init_0.pt_constants()
                    == self.lock.k@.pt_constants);
                assert(content.zone_state.zone_id() == self.lock.k@.zone_id);
                assert(content.zone_state.wf(self.lock.k@.mem_inst_id));
                assert(content.zone_state.ghost_zone().cpu_mem_set
                    == content.cpu_mem_set_perm@.mem_contents->Init_0@);
                assert(content.zone_state.ghost_zone().iommu_mem_set
                    == content.iommu_mem_set_perm@.mem_contents->Init_0@);
                assert(content.s2map_tok.instance_id() == self.lock.k@.mmu_inst_id);
                assert(content.s2map_tok.key() == VmId(self.lock.k@.zone_id as nat));
                assert(content.s2map_tok.value() == pt_s2map_inner(
                    content.cpu_mem_set_perm@.mem_contents->Init_0@.mappings,
                ));
                // IOMMU sync clause: the slice token projects the IOMMU mem_set put back.
                assert(content.iommu_s2map_tok.instance_id() == self.lock.k@.iommu_mmu_inst_id);
                assert(content.iommu_s2map_tok.key() == VmId(self.lock.k@.zone_id as nat));
                assert(content.iommu_s2map_tok.value() == pt_s2map_inner(
                    content.iommu_mem_set_perm@.mem_contents->Init_0@.mappings,
                ));
            };
        }
        self.lock.unlock_write(RwWriteGuard { handle, token: Tracked(content) });
    }

    /// Acquire shared (read) access to this zone's state.
    pub fn lock_read(&self) -> (res: RwReadGuard<
        ZoneKey,
        ZoneRwContent<M, P>,
        ZonePred<PT, M, A, P, I>,
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
        guard: RwReadGuard<ZoneKey, ZoneRwContent<M, P>, ZonePred<PT, M, A, P, I>>,
    )
        requires
            self.wf(),
            guard.wf(&self.lock),
    {
        self.lock.unlock_read(guard)
    }
}

/// Concrete `BudgetProtocol` implementation for `Zone`.
///
/// These methods take a shared `Tracked<&BudgetGlobalState>` because the
/// `BudgetSpec` region transitions are zone-local: they only consume/produce the
/// per-zone `zones[zid]` map-sharded token and access `BudgetSpecInstance`
/// (constant-sharded) as a shared reference.
impl<PT, M, A, I> Zone<PT, M, A, BudgetProtocol, I> where
    PT: PageTable<A>,
    M: MemorySet<PT, A, I>,
    A: BitmapAllocator,
    I: HardwareInstr,
 {
    /// Insert `region` into this zone's CPU set using only a shared borrow of the global state.
    ///
    /// Returns `Err(())` if `region` is invalid or overlaps an existing mapping.
    pub fn insert_region(
        &self,
        allocator: &GlobalAllocator<A>,
        Tracked(gs): Tracked<&BudgetGlobalState>,
        region: MemoryRegion,
        mmu: &mut MmuHardware<I>,
    ) -> (res: Result<(), ()>)
        requires
            self.wf(),
            self.lock.k@.mem_inst_id == BudgetProtocol::mem_inst_id(gs),
            self.lock.k@.alloc_inst_id == allocator.inst_id(),
            self.lock.k@.mmu_inst_id == old(mmu).inst_id(),
            allocator.invariants(),
            old(mmu).wf(),
            zone_regions(self.zone_id as nat).contains(region),
            region.spec_within_vspace(self.vspace_size()),
        ensures
            mmu.wf(),
            mmu.inst_id() == old(mmu).inst_id(),
            mmu.live_vms() == old(mmu).live_vms(),
    {
        if !region.valid() {
            return Err(());
        }
        let (mut mem_set, guard) = self.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, BudgetProtocol> = token.get();

        if mem_set.overlaps_vmem(&region) || mem_set.has_region_starting_at(region.vstart) {
            self.unlock_write(mem_set, RwWriteGuard { handle, token: Tracked(content) });
            return Err(());
        }
        let ghost old_mem_set = mem_set@;
        // Pull this zone's CPU MMU slice token out of the lock content so it can be
        // threaded through `mem_set.insert` (which fires `map`/`map_dsb` per page).
        let tracked ZoneRwContent::<M, BudgetProtocol> {
            cpu_mem_set_perm,
            iommu_mem_set_perm,
            zone_state,
            s2map_tok,
            iommu_s2map_tok,
        } = content;
        let s2_out = mem_set.insert(
            allocator,
            region,
            Ghost(VmId(self.lock.k@.zone_id as nat)),
            mmu,
            Tracked(s2map_tok),
            false,
        );
        let tracked new_s2map_tok = s2_out.get();

        proof {
            // Targeted facts for BudgetProtocol::cpu_insert_region preconditions.
            assert(zone_state.wf(gs.mem_inst_id()));
            assert(zone_state.ghost_zone().cpu_mem_set == old_mem_set);
            assert(!zone_state.ghost_zone().cpu_mem_set.regions.contains(region));
            assert(!zone_state.ghost_zone().cpu_mem_set.overlaps_vmem(region));
            let tracked new_zone_state = BudgetProtocol::cpu_insert_region(gs, zone_state, region);
            content =
            ZoneRwContent::<M, BudgetProtocol> {
                cpu_mem_set_perm,
                iommu_mem_set_perm,
                zone_state: new_zone_state,
                s2map_tok: new_s2map_tok,
                iommu_s2map_tok,
            };
            // Linking invariant: new ghost_zone mirrors the updated exec mem_set.
            assert(content.zone_state.ghost_zone().cpu_mem_set == mem_set@);
            // MMU sync clause restored: `mem_set.insert` returned the slice token driven
            // to `pt_s2map_inner(mem_set@.mappings)` (one `map_dsb` per inserted page).
        }

        self.unlock_write(mem_set, RwWriteGuard { handle, token: Tracked(content) });
        Ok(())
    }

    /// Remove `region` from this zone's CPU set using only a shared borrow of the global state.
    ///
    /// Returns `Err(())` if `region` is invalid or no region starts at `region.vstart`.
    pub fn remove_region(
        &self,
        allocator: &GlobalAllocator<A>,
        Tracked(gs): Tracked<&BudgetGlobalState>,
        region: MemoryRegion,
        mmu: &mut MmuHardware<I>,
    ) -> (res: Result<(), ()>)
        requires
            self.wf(),
            self.lock.k@.mem_inst_id == BudgetProtocol::mem_inst_id(gs),
            self.lock.k@.alloc_inst_id == allocator.inst_id(),
            self.lock.k@.mmu_inst_id == old(mmu).inst_id(),
            allocator.invariants(),
            old(mmu).wf(),
        ensures
            mmu.wf(),
            mmu.inst_id() == old(mmu).inst_id(),
            mmu.live_vms() == old(mmu).live_vms(),
    {
        if !region.valid() {
            return Err(());
        }
        let (mut mem_set, guard) = self.lock_write();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, BudgetProtocol> = token.get();

        if !mem_set.has_region_starting_at(region.vstart) {
            self.unlock_write(mem_set, RwWriteGuard { handle, token: Tracked(content) });
            return Err(());
        }
        let ghost old_mem_set = mem_set@;
        // Pull this zone's CPU MMU slice token out of the lock content.  Its lock
        // invariant `s2map_tok.value() == pt_s2map_inner(mem_set@.mappings)` is the
        // sync point, threaded through `mem_set.remove`, which fires
        // `unmap_invalidate` (forced `DSB`+`TLBI`) per page.
        let tracked ZoneRwContent::<M, BudgetProtocol> {
            cpu_mem_set_perm,
            iommu_mem_set_perm,
            zone_state,
            s2map_tok,
            iommu_s2map_tok,
        } = content;
        let s2_out = mem_set.remove(
            allocator,
            region.vstart,
            Ghost(VmId(self.lock.k@.zone_id as nat)),
            mmu,
            Tracked(s2map_tok),
            false,
        );
        let tracked new_s2map_tok = s2_out.get();

        proof {
            assert(zone_state.wf(gs.mem_inst_id()));
            // The linking invariant connects the ghost zone's CPU region set to the
            // exec mem_set at the point the lock was acquired.
            assert(zone_state.ghost_zone().cpu_mem_set == old_mem_set);
            // The exec check guarantees a region starts at region.vstart, so the ghost
            // zone also has one — they are in sync by the linking invariant.
            assert(zone_state.ghost_zone().cpu_mem_set.has_region_starting_at(region.vstart@));
            // Derive the ghost region over `old_mem_set` so it is the *same* witness
            // that `M::remove`'s `remove_region(region.vstart@)` chooses internally.
            let ghost ghost_region = choose|r: MemoryRegion| #[trigger]
                old_mem_set.regions.contains(r) && r.vstart@ == region.vstart@;
            assert(zone_state.ghost_zone().cpu_mem_set.regions.contains(ghost_region));
            let tracked new_zone_state = BudgetProtocol::cpu_remove_region(
                gs,
                zone_state,
                ghost_region,
            );
            content =
            ZoneRwContent::<M, BudgetProtocol> {
                cpu_mem_set_perm,
                iommu_mem_set_perm,
                zone_state: new_zone_state,
                s2map_tok: new_s2map_tok,
                iommu_s2map_tok,
            };
            // Linking invariant: new ghost_zone mirrors the updated exec mem_set.
            // `M::remove` ensures mem_set@ == old_mem_set.remove_region(region.vstart@),
            // which equals old_mem_set.remove_region_exact(ghost_region).
            assert(content.zone_state.ghost_zone().cpu_mem_set == mem_set@);
        }

        self.unlock_write(mem_set, RwWriteGuard { handle, token: Tracked(content) });
        Ok(())
    }

    /// Insert `region` into this zone's IOMMU-visible set, forcing the SMMU stage-2
    /// maintenance instructions per page via the IOMMU `MmuHardware` instance.
    pub fn insert_iommu_region(
        &self,
        allocator: &GlobalAllocator<A>,
        Tracked(gs): Tracked<&BudgetGlobalState>,
        region: MemoryRegion,
        iommu_mmu: &mut MmuHardware<I>,
    ) -> (res: Result<(), ()>)
        requires
            self.wf(),
            self.lock.k@.mem_inst_id == BudgetProtocol::mem_inst_id(gs),
            self.lock.k@.alloc_inst_id == allocator.inst_id(),
            self.lock.k@.iommu_mmu_inst_id == old(iommu_mmu).inst_id(),
            allocator.invariants(),
            old(iommu_mmu).wf(),
            zone_regions(self.zone_id as nat).contains(region) || region == gic_region(),
            region.spec_within_vspace(self.vspace_size()),
        ensures
            iommu_mmu.wf(),
            iommu_mmu.inst_id() == old(iommu_mmu).inst_id(),
            iommu_mmu.live_vms() == old(iommu_mmu).live_vms(),
    {
        if !region.valid() {
            return Err(());
        }
        let (mut mem_set, guard) = self.lock_write_iommu();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, BudgetProtocol> = token.get();

        if mem_set.overlaps_vmem(&region) || mem_set.has_region_starting_at(region.vstart) {
            self.unlock_write_iommu(mem_set, RwWriteGuard { handle, token: Tracked(content) });
            return Err(());
        }
        let ghost old_mem_set = mem_set@;
        // Pull the IOMMU slice token out and thread it through `mem_set.insert` with
        // `iommu = true`, which fires the SMMU `iommu_map_sync` per inserted page.
        let tracked ZoneRwContent::<M, BudgetProtocol> {
            cpu_mem_set_perm,
            iommu_mem_set_perm,
            zone_state,
            s2map_tok,
            iommu_s2map_tok,
        } = content;
        let s2_out = mem_set.insert(
            allocator,
            region,
            Ghost(VmId(self.lock.k@.zone_id as nat)),
            iommu_mmu,
            Tracked(iommu_s2map_tok),
            true,
        );
        let tracked new_iommu_s2map_tok = s2_out.get();

        proof {
            // Targeted facts for BudgetProtocol::iommu_insert_region preconditions.
            assert(zone_state.wf(gs.mem_inst_id()));
            assert(zone_state.ghost_zone().iommu_mem_set == old_mem_set);
            assert(!zone_state.ghost_zone().iommu_mem_set.overlaps_vmem(region));
            assert(!zone_state.ghost_zone().iommu_mem_set.regions.contains(region)) by {
                if zone_state.ghost_zone().iommu_mem_set.regions.contains(region) {
                    assert(old_mem_set.has_region_starting_at(region.vstart@));
                }
            }
            let tracked new_zone_state = BudgetProtocol::iommu_insert_region(
                gs,
                zone_state,
                region,
            );
            content =
            ZoneRwContent::<M, BudgetProtocol> {
                cpu_mem_set_perm,
                iommu_mem_set_perm,
                zone_state: new_zone_state,
                s2map_tok,
                iommu_s2map_tok: new_iommu_s2map_tok,
            };
            // Linking invariant: new ghost_zone mirrors the updated exec IOMMU mem_set;
            // the IOMMU slice token was driven to `pt_s2map_inner(mem_set@.mappings)`.
            assert(content.zone_state.ghost_zone().iommu_mem_set == mem_set@);
        }

        self.unlock_write_iommu(mem_set, RwWriteGuard { handle, token: Tracked(content) });
        Ok(())
    }

    /// Remove `region` from this zone's IOMMU-visible set, forcing the SMMU stage-2
    /// invalidation per page via the IOMMU `MmuHardware` instance.
    pub fn remove_iommu_region(
        &self,
        allocator: &GlobalAllocator<A>,
        Tracked(gs): Tracked<&BudgetGlobalState>,
        region: MemoryRegion,
        iommu_mmu: &mut MmuHardware<I>,
    ) -> (res: Result<(), ()>)
        requires
            self.wf(),
            self.lock.k@.mem_inst_id == BudgetProtocol::mem_inst_id(gs),
            self.lock.k@.alloc_inst_id == allocator.inst_id(),
            self.lock.k@.iommu_mmu_inst_id == old(iommu_mmu).inst_id(),
            allocator.invariants(),
            old(iommu_mmu).wf(),
        ensures
            iommu_mmu.wf(),
            iommu_mmu.inst_id() == old(iommu_mmu).inst_id(),
            iommu_mmu.live_vms() == old(iommu_mmu).live_vms(),
    {
        if !region.valid() {
            return Err(());
        }
        let (mut mem_set, guard) = self.lock_write_iommu();
        let RwWriteGuard { handle, token } = guard;
        let tracked mut content: ZoneRwContent<M, BudgetProtocol> = token.get();

        if !mem_set.has_region_starting_at(region.vstart) {
            self.unlock_write_iommu(mem_set, RwWriteGuard { handle, token: Tracked(content) });
            return Err(());
        }
        let ghost old_mem_set = mem_set@;
        let tracked ZoneRwContent::<M, BudgetProtocol> {
            cpu_mem_set_perm,
            iommu_mem_set_perm,
            zone_state,
            s2map_tok,
            iommu_s2map_tok,
        } = content;
        let s2_out = mem_set.remove(
            allocator,
            region.vstart,
            Ghost(VmId(self.lock.k@.zone_id as nat)),
            iommu_mmu,
            Tracked(iommu_s2map_tok),
            true,
        );
        let tracked new_iommu_s2map_tok = s2_out.get();

        proof {
            assert(zone_state.wf(gs.mem_inst_id()));
            assert(zone_state.ghost_zone().iommu_mem_set == old_mem_set);
            assert(zone_state.ghost_zone().iommu_mem_set.has_region_starting_at(region.vstart@));
            let ghost ghost_region = choose|r: MemoryRegion| #[trigger]
                old_mem_set.regions.contains(r) && r.vstart@ == region.vstart@;
            assert(zone_state.ghost_zone().iommu_mem_set.regions.contains(ghost_region));
            let tracked new_zone_state = BudgetProtocol::iommu_remove_region(
                gs,
                zone_state,
                ghost_region,
            );
            content =
            ZoneRwContent::<M, BudgetProtocol> {
                cpu_mem_set_perm,
                iommu_mem_set_perm,
                zone_state: new_zone_state,
                s2map_tok,
                iommu_s2map_tok: new_iommu_s2map_tok,
            };
            assert(content.zone_state.ghost_zone().iommu_mem_set == mem_set@);
        }

        self.unlock_write_iommu(mem_set, RwWriteGuard { handle, token: Tracked(content) });
        Ok(())
    }
}

} // verus!
