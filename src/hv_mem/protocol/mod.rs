//! Region-assignment protocol abstraction.
//!
//! Abstracts over the two safety assumptions (`ClosureSpec` / `BudgetSpec`) so that
//! `Zone` and `HvMem` are generic over `P: ZoneGhostProtocol` rather than hard-wired.
//!
//! Submodules:
//! - [`closure`]: assumption-1 ghost state (`ClosureGlobalState`) and `ClosureProtocol`.
//! - [`budget`]:  assumption-2 ghost state (`BudgetGlobalState`) and `BudgetProtocol`.
pub mod budget;
pub mod closure;

use super::spec::GhostZone;
use crate::memory_set::SpecMemorySet;
pub use budget::{BudgetGlobalState, BudgetProtocol, BudgetZoneState};
pub use closure::{ClosureGlobalState, ClosureProtocol, ClosureZoneState};

use vstd::prelude::*;

verus! {

/// Minimal spec interface shared by `ZoneState` (ClosureSpec) and `BudgetZoneState`
/// (BudgetSpec). Defined here in the `spec` layer so that `zone.rs` can implement
/// it without depending on the `protocol` module, avoiding a circular dependency.
///
/// Used as the bound `P::ZoneToken: ZoneStateOps` in the `ZoneGhostProtocol` trait.
pub trait ZoneStateOps {
    /// The zone ID (key in the `zones` map sharding).
    spec fn zone_id(&self) -> nat;

    /// The ghost zone state (value in the `zones` map sharding).
    spec fn ghost_zone(&self) -> GhostZone;

    /// Well-formedness relative to a spec-instance ID.
    spec fn wf(&self, mem_inst_id: InstanceId) -> bool;
}

/// Ghost-state trait for **zone lifecycle** operations (add / remove a zone).
///
/// `Zone<PT, M, A, P, I>` and `HvMem<PT, M, A, P, I>` are parameterized by `P: ZoneGhostProtocol`.
/// Swapping `P` switches the entire ghost-state bookkeeping strategy without changing
/// any exec code.
///
/// ## Scope
/// This trait abstracts only the *globally-serialized* zone add/remove operations,
/// because both `ClosureProtocol` and `BudgetProtocol` require `&mut GlobalState`
/// for these (they both update `zone_ids_tok`).
///
/// Region insert/remove are **not** in this trait because their required borrow of
/// `GlobalState` differs by protocol and cannot be unified in a Rust trait:
///
/// | Protocol          | region insert/remove borrow | Why                              |
/// |-------------------|-----------------------------|----------------------------------|
/// | `ClosureProtocol` | `&mut ClosureGlobalState`   | must update the prototype `zones_view` token |
/// | `BudgetProtocol`  | `&BudgetGlobalState`        | zone-local only; `gs` unchanged  |
///
/// Region operations live in protocol-specific `impl Zone<..., P>` blocks and are
/// called from protocol-specific `impl HvMem<..., P>` blocks.
pub trait ZoneGhostProtocol: Sized {
    /// Per-zone tracked ghost state (map-sharded token from `zones[zid]`).
    type ZoneToken: ZoneStateOps;

    /// Global tracked ghost state stored inside `HvMem`'s write-lock content.
    ///
    /// `ClosureProtocol`: `ClosureGlobalState` (holds the prototype `zones_view` token).
    /// `BudgetProtocol`:  `BudgetGlobalState` (zone-local insert).
    type GlobalState;

    // ─── Spec predicates ─────────────────────────────────────────────────────
    /// Well-formedness: all internal tokens are consistent with each other.
    spec fn global_wf(gs: &Self::GlobalState) -> bool;

    /// The spec-instance ID embedded in the global state.
    spec fn mem_inst_id(gs: &Self::GlobalState) -> InstanceId;

    /// The current set of registered zone IDs.
    spec fn zone_ids(gs: &Self::GlobalState) -> Set<nat>;

    // ─── Proof transitions ────────────────────────────────────────────────────
    /// Register a new empty zone; returns a fresh zone token.
    ///
    /// The zone starts with no regions; use `insert_region` to populate it.
    proof fn add_zone(tracked gs: &mut Self::GlobalState, zid: nat) -> (tracked zt: Self::ZoneToken)
        requires
            Self::global_wf(old(gs)),
            !Self::zone_ids(old(gs)).contains(zid),
        ensures
            Self::global_wf(gs),
            Self::mem_inst_id(gs) == Self::mem_inst_id(old(gs)),
            zt.zone_id() == zid,
            zt.ghost_zone().regions() =~= Set::empty(),
            // The new zone is *fully* empty (regions and mappings, CPU and IOMMU) —
            // exactly the literal both spec SMs' `add_zone` transitions construct.
            // `Zone::new` needs this to establish `ZonePred::inv` at birth.
            zt.ghost_zone() == (GhostZone {
                cpu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
                iommu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
            }),
            zt.wf(Self::mem_inst_id(gs)),
            Self::zone_ids(gs) =~= Self::zone_ids(old(gs)).insert(zid),
    ;

    /// Deregister an empty zone; consumes its zone token.
    proof fn remove_zone(tracked gs: &mut Self::GlobalState, tracked zt: Self::ZoneToken)
        requires
            Self::global_wf(old(gs)),
            zt.wf(Self::mem_inst_id(old(gs))),
            zt.ghost_zone().cpu_mem_set.empty(),
            zt.ghost_zone().iommu_mem_set.empty(),
        ensures
            Self::global_wf(gs),
            Self::mem_inst_id(gs) == Self::mem_inst_id(old(gs)),
            Self::zone_ids(gs) =~= Self::zone_ids(old(gs)).remove(zt.zone_id()),
    ;
}

} // verus!
