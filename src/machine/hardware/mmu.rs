//! The **standalone tokenized MMU state machine** (`MmuSpec`): the hardware-side
//! analog of `BudgetSpec`, whose tokens are *unforgeable* so the implementation
//! cannot fabricate a favourable MMU state in ghost code.  It models the two
//! stateful pieces of an MMU, both `#[sharding(variable)]`:
//!
//! * [`s2map`](MmuSpec::State::s2map) — the **MMU-reachable** stage-2 mappings
//!   (what a page-table walk currently resolves);
//! * [`tlb`](MmuSpec::State::tlb) — the **nondeterministic** TLB cache, filled
//!   autonomously by the MMU (the `fill` transition models the environment).
//!
//! The two tokens and the `Instance` are encapsulated inside the
//! [`HardwareInstr`](crate::hardware::HardwareInstr)-backed `MmuHardware` handle
//! (`crate::hardware::mmu`), so only its asm-bearing methods can fire transitions —
//! that is what makes the forcing airtight, and where the per-vm `synced` sync
//! point and the `unmap_dsb_tlbi` contract live.
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
use crate::machine::types::*;
use verus_state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;

verus! {

/// The set of TLB keys a per-IPA broadcast invalidation of `(vm, gpa)` targets —
/// every CPU's cached entry for that page.  Mirrors `tlbi_ipa_broadcast_step`.
pub open spec fn invalidation_targets(vm: VmId, gpa: GuestPage) -> Set<TlbKey> {
    Set::new(|k: TlbKey| k.vm == vm && k.gpa == gpa)
}

/// Full TLB coherence — every cached entry's page is still mapped *and* the entry
/// agrees.  This is the body of `MachineState::tlb_safe`, and the **pre/post
/// contract of a region unmap** (the *sync-point* predicate).  It is deliberately
/// stronger than `MmuSpec::State::inv_coherent` and is NOT a machine invariant:
/// `unmap` breaks it (design step (b)); `invalidate` restores it.
pub open spec fn synced(s2map: Map<VmPageKey, S2Entry>, tlb: Map<TlbKey, TlbEntry>) -> bool {
    forall|key: TlbKey| #[trigger]
        tlb.contains_key(key) ==> {
            let sk = VmPageKey::new(key.vm, key.gpa);
            &&& s2map.contains_key(sk)
            &&& tlb[key].as_s2_entry() == s2map[sk]
        }
}

tokenized_state_machine! {
    MmuSpec {
        fields {
            /// MMU-reachable stage-2 mappings (the walker's current view); a single
            /// token, encapsulated in `MmuHardware`.  The `unmap` transition that
            /// drops a page from it is the seam that forces the unmap instructions.
            #[sharding(variable)]
            pub s2map: Map<VmPageKey, S2Entry>,

            /// Nondeterministic TLB cache; a single token for the one global TLB,
            /// encapsulated in `MmuHardware` (see module docs).
            #[sharding(variable)]
            pub tlb: Map<TlbKey, TlbEntry>,
        }

        // ── Invariant ──────────────────────────────────────────────────────────

        /// **Full TLB coherence — the sole invariant.** Every cached entry's page
        /// is still in `s2map` *and* the entry agrees with it.  This is exactly
        /// `MachineState::tlb_safe`.  It is inductive because the only way a page
        /// leaves `s2map` is the bundled [`unmap_invalidate`], which clears the
        /// page's TLB entries in the *same* step — so no orphan is ever exposed.
        #[invariant]
        pub fn inv_coherent(&self) -> bool {
            forall|key: TlbKey| #[trigger] self.tlb.contains_key(key) ==> {
                let sk = VmPageKey::new(key.vm, key.gpa);
                &&& self.s2map.contains_key(sk)
                &&& self.tlb[key].as_s2_entry() == self.s2map[sk]
            }
        }

        // ── Transitions ──────────────────────────────────────────────────────────

        /// Start from a given set of established mappings with an empty TLB.
        init! {
            initialize(s2map0: Map<VmPageKey, S2Entry>) {
                init s2map = s2map0;
                init tlb = Map::empty();
            }
        }

        /// The hardware MMU autonomously caches a walker-reachable translation.
        /// Modeled as an *environment* transition; guarded by `s2map.contains` so
        /// it can never cache a mapping the walker cannot reach (which is what
        /// blocks a re-fill once `unmap_invalidate` has removed the page).
        transition! {
            fill(cpu: CpuId, vm: VmId, gpa: GuestPage) {
                require pre.s2map.contains_key(VmPageKey::new(vm, gpa));
                birds_eye let entry = pre.s2map[VmPageKey::new(vm, gpa)];
                update tlb = pre.tlb.insert(
                    TlbKey::new(cpu, vm, gpa),
                    TlbEntry { page: entry.page, access: entry.access, generation: entry.generation },
                );
            }
        }

        /// One atomic break-before-make step: a `DSB` makes the (already-written-
        /// invalid) PTE walker-invisible (drops `(vm, gpa)` from `s2map`) and the
        /// `TLBI IPAS2E1IS` broadcast clears that page's cached entries — together,
        /// so coherence is never broken (no orphan window at this granularity).
        transition! {
            unmap_invalidate(vm: VmId, gpa: GuestPage) {
                update s2map = pre.s2map.remove(VmPageKey::new(vm, gpa));
                update tlb = pre.tlb.remove_keys(invalidation_targets(vm, gpa));
            }
        }

        /// A `DSB` after writing a *fresh* PTE makes the new mapping walker-
        /// reachable.  Break-before-make for the map side: the page must be absent
        /// from `s2map`, which by the `inv_coherent` invariant means it has **no**
        /// cached TLB entry — so adding it cannot disagree with a stale entry, and
        /// no `TLBI` is needed.  (Used by the insert path.)
        transition! {
            map(vm: VmId, gpa: GuestPage, entry: S2Entry) {
                require !pre.s2map.contains_key(VmPageKey::new(vm, gpa));
                update s2map = pre.s2map.insert(VmPageKey::new(vm, gpa), entry);
            }
        }

        // ── Inductive proofs ──────────────────────────────────────────────────────

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, s2map0: Map<VmPageKey, S2Entry>) {
            assert(post.tlb =~= Map::empty());
        }

        #[inductive(fill)]
        fn fill_inductive(pre: Self, post: Self, cpu: CpuId, vm: VmId, gpa: GuestPage) {
            let sk0 = VmPageKey::new(vm, gpa);
            let tkey0 = TlbKey::new(cpu, vm, gpa);
            let entry = pre.s2map[sk0];
            assert forall|key: TlbKey| #[trigger] post.tlb.contains_key(key) implies {
                let sk = VmPageKey::new(key.vm, key.gpa);
                &&& post.s2map.contains_key(sk)
                &&& post.tlb[key].as_s2_entry() == post.s2map[sk]
            } by {
                let sk = VmPageKey::new(key.vm, key.gpa);
                if key == tkey0 {
                    // The freshly-cached entry is built from s2map[sk0] (which the
                    // `require` guarantees is present), so it agrees.
                    assert(sk == sk0);
                    assert(post.tlb[tkey0].as_s2_entry() == entry);
                } else {
                    assert(post.tlb[key] == pre.tlb[key]);
                }
            };
        }

        #[inductive(unmap_invalidate)]
        fn unmap_invalidate_inductive(pre: Self, post: Self, vm: VmId, gpa: GuestPage) {
            let sk0 = VmPageKey::new(vm, gpa);
            assert forall|key: TlbKey| #[trigger] post.tlb.contains_key(key) implies {
                let sk = VmPageKey::new(key.vm, key.gpa);
                &&& post.s2map.contains_key(sk)
                &&& post.tlb[key].as_s2_entry() == post.s2map[sk]
            } by {
                let sk = VmPageKey::new(key.vm, key.gpa);
                // A surviving key escaped `invalidation_targets`, so its page differs
                // from `(vm, gpa)`, hence `sk != sk0` and it stays in `s2map`.
                assert(!invalidation_targets(vm, gpa).contains(key));
                assert(sk != sk0);
                assert(pre.tlb.contains_key(key) && post.tlb[key] == pre.tlb[key]);
            };
        }

        #[inductive(map)]
        fn map_inductive(pre: Self, post: Self, vm: VmId, gpa: GuestPage, entry: S2Entry) {
            let sk0 = VmPageKey::new(vm, gpa);
            assert forall|key: TlbKey| #[trigger] post.tlb.contains_key(key) implies {
                let sk = VmPageKey::new(key.vm, key.gpa);
                &&& post.s2map.contains_key(sk)
                &&& post.tlb[key].as_s2_entry() == post.s2map[sk]
            } by {
                let sk = VmPageKey::new(key.vm, key.gpa);
                // `key` is cached, so by the pre-invariant its page is in `pre.s2map`;
                // the `require` says `sk0` is not — so `sk != sk0`, and `insert` leaves
                // `sk`'s entry untouched.
                assert(pre.s2map.contains_key(sk));
                assert(sk != sk0);
            };
        }
    }
}
// ── Token type aliases ─────────────────────────────────────────────────────────


/// `MmuSpec` instance token (shared by reference).
pub type MmuInstance = MmuSpec::Instance;

/// The MMU-reachable stage-2 map token (variable-sharded; held by `MmuHardware`).
pub type MmuS2MapToken = MmuSpec::s2map;

/// The global TLB token (variable-sharded; held by `MmuHardware`).
pub type MmuTlbToken = MmuSpec::tlb;

} // verus!
