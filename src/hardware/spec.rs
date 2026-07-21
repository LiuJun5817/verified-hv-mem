//! The **standalone tokenized stage-2 state machine** (`MmuSpec`): the hardware-side
//! analog of `BudgetSpec`, whose tokens are *unforgeable* so the implementation
//! cannot fabricate a favourable hardware state in ghost code.
//!
//! `MmuSpec` is **regime-neutral** — it captures the law obeyed by *any* stage-2
//! translation unit (a walker-reachable map + a TLB filled autonomously) — and is
//! **instantiated twice**: once for the CPU **MMU** and once for the **SMMU**
//! (IOMMU).  The two instances have disjoint tokens (a CPU `TLBI` advances only the
//! CPU instance's `tlb`; an SMMU `CMD_TLBI_S2_IPA` only the SMMU's), so they model
//! the two physically separate TLBs without any cross-talk.  Only the real
//! instructions differ, and those are split into [`MmuInstr`](crate::hardware::MmuInstr)
//! / [`SmmuInstr`](crate::hardware::SmmuInstr).
//!
//! It models the two stateful pieces of a stage-2 unit, both `#[sharding(variable)]`:
//!
//! * [`s2map`](MmuSpec::State::s2map) — the **MMU-reachable** stage-2 mappings
//!   (what a page-table walk currently resolves);
//! * [`tlb`](MmuSpec::State::tlb) — the **nondeterministic** TLB cache, filled
//!   autonomously by the MMU (the `fill` transition models the environment).
//!
//! The two tokens and the `Instance` are encapsulated inside the
//! [`HardwareInstr`](crate::hardware::HardwareInstr)-backed `MmuHardware` handle
//! (`crate::hardware::mmu`), so only its asm-bearing methods can fire transitions —
//! that is what makes the forcing airtight, and where the per-vm sync-point
//! contracts live.
//!
//! # `s2map` lags the page-table bytes; the divergence is the unmap window
//!
//! `s2map` here is the *walker-reachable* view, which catches up to the page-table
//! bytes only at a `DSB` (the `unmap` transition is what a `DSB` fires).
//! `PageTable::view()` — a pure function of the bytes — is the *byte-view*, which
//! moves at the PTE write.  Between a `pt.unmap` and the following `DSB` the two
//! diverge: that "written-but-not-yet-walker-visible" window is what makes
//! break-before-make a theorem rather than a documented obligation.
//!
//! # Inductive invariant vs. sync point
//!
//! Full coherence ("every cached entry agrees with `s2map` *and* its page is still
//! mapped" — `MmuHardware::tlb_coherent`, = `MachineState::tlb_safe`) is **not**
//! preserved by `unmap`: removing a page from `s2map` while a stale TLB entry
//! survives is the post-`DSB`/pre-`TLBI` window where MMU wf is broken on purpose.
//! So the genuinely inductive invariant *here* is the weaker
//! [`inv_coherent`](State::inv_coherent): *where `s2map` has the page, the TLB
//! agrees* (tolerating orphaned stale entries).  Full coherence is re-established
//! by `invalidate` and holds at **sync points**; the per-page
//! `MmuHardware::unmap_dsb_tlbi` (sync → sync) is what forces the `DSB`+`TLBI`.
use crate::model::types::{CpuId, GuestPage, S2Entry, TlbEntry, TlbKey, VmId};
use verus_state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;

verus! {

/// The set of TLB keys a per-IPA broadcast invalidation of `(vm, gpa)` targets —
/// every CPU's cached entry for that page.  Mirrors `tlbi_ipa_broadcast_step`.
pub open spec fn invalidation_targets(vm: VmId, gpa: GuestPage) -> Set<TlbKey> {
    Set::new(|k: TlbKey| k.vm == vm && k.gpa == gpa)
}

tokenized_state_machine! {
    MmuSpec {
        fields {
            /// MMU-reachable stage-2 mappings, **per-vm sharded** (one token per vm,
            /// value = that vm's `gpa -> S2Entry` submap).  Each zone owns its vm's
            /// token, held in its lock; modifying it (`map`/`unmap_invalidate`) is the
            /// seam that forces the maintenance instructions.
            #[sharding(map)]
            pub s2map: Map<VmId, Map<GuestPage, S2Entry>>,

            /// Mirror of `s2map.dom()` (the live vms), used to enforce fresh
            /// registration and track deregistration.
            #[sharding(variable)]
            pub vm_ids: Set<VmId>,

            /// Nondeterministic TLB cache; a single token for the one global TLB,
            /// encapsulated in `MmuHardware` (see module docs).
            #[sharding(variable)]
            pub tlb: Map<TlbKey, TlbEntry>,
        }

        // ── Invariants ─────────────────────────────────────────────────────────

        /// `vm_ids` is exactly the set of vms present in `s2map`.
        #[invariant]
        pub fn inv_vm_ids(&self) -> bool {
            self.s2map.dom() == self.vm_ids
        }

        /// **Full TLB coherence — the load-bearing invariant.** Every cached entry's
        /// page is still in `s2map` *and* the entry agrees with it (= the body of
        /// `MachineState::tlb_safe`).  Inductive because the only page-removal,
        /// `unmap_invalidate`, clears that page's TLB entries in the *same* step.
        #[invariant]
        pub fn inv_coherent(&self) -> bool {
            forall|key: TlbKey| #[trigger] self.tlb.contains_key(key) ==> {
                &&& self.s2map.contains_key(key.vm)
                &&& self.s2map[key.vm].contains_key(key.gpa)
                &&& self.tlb[key].as_s2_entry() == self.s2map[key.vm][key.gpa]
            }
        }

        // ── Transitions ──────────────────────────────────────────────────────────

        /// Boot: no vms, empty TLB.
        init! {
            initialize() {
                init s2map = Map::empty();
                init vm_ids = Set::empty();
                init tlb = Map::empty();
            }
        }

        /// Register a fresh vm with an empty mapping slice (fired when a zone is
        /// created; yields the zone's `s2map` slice token).
        transition! {
            add_vm(vm: VmId) {
                require !pre.vm_ids.contains(vm);
                update vm_ids = pre.vm_ids.insert(vm);
                add s2map += [vm => Map::empty()];
            }
        }

        /// Deregister a vm after its walker-reachable mapping slice is empty.
        transition! {
            remove_vm(vm: VmId) {
                remove s2map -= [vm => let inner];
                require inner == Map::<GuestPage, S2Entry>::empty();
                update vm_ids = pre.vm_ids.remove(vm);
            }
        }

        /// The hardware MMU autonomously caches a walker-reachable translation.
        /// Modeled as an *environment* transition; guarded by `s2map[vm].contains`
        /// so it can never cache a mapping the walker cannot reach (blocking a
        /// re-fill once `unmap_invalidate` has removed the page).
        transition! {
            fill(cpu: CpuId, vm: VmId, gpa: GuestPage) {
                have s2map >= [vm => let inner];
                require inner.contains_key(gpa);
                update tlb = pre.tlb.insert(
                    TlbKey::new(cpu, vm, gpa),
                    TlbEntry { page: inner[gpa].page, access: inner[gpa].access, generation: inner[gpa].generation },
                );
            }
        }

        /// One atomic break-before-make step: a `DSB` drops `(vm, gpa)` from `s2map`
        /// and the `TLBI IPAS2E1IS` broadcast clears that page's cached entries —
        /// together, so coherence is never broken at this granularity.
        transition! {
            unmap_invalidate(vm: VmId, gpa: GuestPage) {
                remove s2map -= [vm => let inner];
                add s2map += [vm => inner.remove(gpa)];
                update tlb = pre.tlb.remove_keys(invalidation_targets(vm, gpa));
            }
        }

        /// A `DSB` after writing a *fresh* PTE makes the new mapping walker-
        /// reachable.  Break-before-make for the map side: the page must be absent
        /// from the vm's slice, which by `inv_coherent` means it has **no** cached
        /// TLB entry — so no `TLBI` is needed.  (Used by the insert path.)
        transition! {
            map(vm: VmId, gpa: GuestPage, entry: S2Entry) {
                remove s2map -= [vm => let inner];
                require !inner.contains_key(gpa);
                add s2map += [vm => inner.insert(gpa, entry)];
            }
        }

        // ── Inductive proofs ──────────────────────────────────────────────────────

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) {
            assert(post.tlb =~= Map::empty());
            assert(post.s2map.dom() =~= post.vm_ids);
        }

        #[inductive(add_vm)]
        fn add_vm_inductive(pre: Self, post: Self, vm: VmId) {
            assert(post.s2map.dom() =~= post.vm_ids);
            assert forall|key: TlbKey| #[trigger] post.tlb.contains_key(key) implies {
                &&& post.s2map.contains_key(key.vm)
                &&& post.s2map[key.vm].contains_key(key.gpa)
                &&& post.tlb[key].as_s2_entry() == post.s2map[key.vm][key.gpa]
            } by {
                assert(pre.s2map.contains_key(key.vm));
                assert(key.vm != vm);
            };
        }

        #[inductive(remove_vm)]
        fn remove_vm_inductive(pre: Self, post: Self, vm: VmId) {
            assert(post.s2map.dom() =~= post.vm_ids);
            assert forall|key: TlbKey| #[trigger] post.tlb.contains_key(key) implies {
                &&& post.s2map.contains_key(key.vm)
                &&& post.s2map[key.vm].contains_key(key.gpa)
                &&& post.tlb[key].as_s2_entry() == post.s2map[key.vm][key.gpa]
            } by {
                assert(pre.tlb.contains_key(key));
                assert(pre.s2map.contains_key(key.vm));
                assert(key.vm != vm) by {
                    if key.vm == vm {
                        assert(pre.s2map[vm].contains_key(key.gpa));
                    }
                }
            };
        }

        #[inductive(fill)]
        fn fill_inductive(pre: Self, post: Self, cpu: CpuId, vm: VmId, gpa: GuestPage) {
            let inner = pre.s2map[vm];
            let tkey0 = TlbKey::new(cpu, vm, gpa);
            assert forall|key: TlbKey| #[trigger] post.tlb.contains_key(key) implies {
                &&& post.s2map.contains_key(key.vm)
                &&& post.s2map[key.vm].contains_key(key.gpa)
                &&& post.tlb[key].as_s2_entry() == post.s2map[key.vm][key.gpa]
            } by {
                if key == tkey0 {
                    assert(post.tlb[tkey0].as_s2_entry() == inner[gpa]);
                } else {
                    assert(post.tlb[key] == pre.tlb[key]);
                }
            };
        }

        #[inductive(unmap_invalidate)]
        fn unmap_invalidate_inductive(pre: Self, post: Self, vm: VmId, gpa: GuestPage) {
            assert(post.s2map.dom() =~= post.vm_ids);
            assert forall|key: TlbKey| #[trigger] post.tlb.contains_key(key) implies {
                &&& post.s2map.contains_key(key.vm)
                &&& post.s2map[key.vm].contains_key(key.gpa)
                &&& post.tlb[key].as_s2_entry() == post.s2map[key.vm][key.gpa]
            } by {
                assert(!invalidation_targets(vm, gpa).contains(key));
                assert(pre.tlb.contains_key(key) && post.tlb[key] == pre.tlb[key]);
                if key.vm == vm {
                    assert(key.gpa != gpa);
                }
            };
        }

        #[inductive(map)]
        fn map_inductive(pre: Self, post: Self, vm: VmId, gpa: GuestPage, entry: S2Entry) {
            assert(post.s2map.dom() =~= post.vm_ids);
            assert forall|key: TlbKey| #[trigger] post.tlb.contains_key(key) implies {
                &&& post.s2map.contains_key(key.vm)
                &&& post.s2map[key.vm].contains_key(key.gpa)
                &&& post.tlb[key].as_s2_entry() == post.s2map[key.vm][key.gpa]
            } by {
                assert(pre.s2map.contains_key(key.vm));
                if key.vm == vm {
                    assert(pre.s2map[vm].contains_key(key.gpa));
                    assert(key.gpa != gpa);
                }
            };
        }
    }
}
// ── Token type aliases ─────────────────────────────────────────────────────────


/// `MmuSpec` instance token (shared by reference).
pub type MmuInstance = MmuSpec::Instance;

/// One vm's MMU-reachable stage-2 slice token (map-sharded; held in that zone's lock).
pub type MmuS2MapToken = MmuSpec::s2map;

/// The live-vm mirror token (variable-sharded; held by `MmuHardware` for VM lifecycle).
pub type MmuVmIdsToken = MmuSpec::vm_ids;

/// The global TLB token (variable-sharded; held by `MmuHardware`).
pub type MmuTlbToken = MmuSpec::tlb;

} // verus!
