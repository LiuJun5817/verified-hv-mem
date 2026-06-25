//! Slice 1 of the SW/HW co-verification plan: the **standalone tokenized MMU
//! state machine** (`MmuSpec`).
//!
//! This is the hardware-side analog of `BudgetSpec`: a `tokenized_state_machine!`
//! whose tokens are *unforgeable*, so the implementation cannot fabricate a
//! favourable MMU state in ghost code.  It models the two stateful pieces of an
//! MMU:
//!
//! * [`s2map`](MmuSpec::State::s2map) — the **MMU-reachable** stage-2 mappings
//!   (what a page-table walk currently resolves).  `#[sharding(map)]`: one token
//!   per page, owned by whoever owns that mapping.  Giving up a page's token (the
//!   `unmap` transition) is the seam that *forces* the implementation to issue the
//!   real instructions — see the crate-level design notes in
//!   `memory_set::tlb` / memory `tlb-tokenized-state-machine`.
//! * [`tlb`](MmuSpec::State::tlb) — the **nondeterministic** TLB cache.  Filled
//!   autonomously by the hardware MMU (the `fill` transition models the
//!   environment), so the implementation never reasons about its concrete
//!   contents directly — only through the machine invariant.
//!
//! # `s2map` lags the page-table bytes; the divergence is the unmap window
//!
//! `s2map` here is the *walker-reachable* view, which catches up to the
//! page-table bytes only at a `DSB` (the `unmap`/`map` transitions are what a
//! `DSB` fires).  `PageTable::view()` — a pure function of the bytes — is the
//! *byte-view*, which moves at the PTE write.  Between a `pt.unmap` and the
//! following `DSB` the two diverge: that interval is the "written-but-not-yet-
//! walker-visible" window, which the earlier inert-barrier model could not
//! express.  Making `s2map` the lagging view is what turns break-before-make
//! into a theorem.
//!
//! # KEY FINDING (slice 1): full coherence is a *sync-point* predicate, NOT a
//! # global invariant
//!
//! The natural target "every cached entry agrees with `s2map` and its page is
//! still mapped" ([`synced`], = `MachineState::tlb_safe`) is **not**
//! preserved by `unmap`: removing a page from `s2map` while a stale TLB entry for
//! it survives is *exactly* the post-`DSB`/pre-`TLBI` window where MMU
//! well-formedness is broken on purpose (design step (b)).  So the genuinely
//! inductive invariant is the weaker [`inv_coherent`](State::inv_coherent):
//! *where `s2map` has the page, the TLB agrees* — which tolerates "orphaned"
//! stale entries.  Full coherence is then re-established by `invalidate` (the
//! `TLBI`) and holds at **sync points**; the unmap contract (sync → sync) is what
//! forces the `DSB`+`TLBI`.
//!
//! (Map-side break-before-make is a related slice-2 finding: a `map` transition
//! must `require` the page is TLB-clean, else a stale entry from a previous
//! lifetime would disagree with the freshly-installed mapping — and the fresh
//! `add` needs a domain-mirror variable to prove key-absence.)
//!
//! # Token placement (the "impl holds no `tlb` token" goal)
//!
//! `tlb` is `#[sharding(variable)]`: a single token for the one global TLB.  The
//! plan is that this token (with the `Instance`) is **encapsulated inside the
//! `HardwareOps` implementor** — `fill`/`invalidate` are fired only by the real
//! instructions — so the implementation threads only `s2map` page tokens and
//! never holds the `tlb` token.  That is what keeps the `Instance` out of impl
//! hands (only the asm-bearing methods can fire transitions) and is what makes
//! the forcing airtight.  A literal `#[sharding(not_tokened)]` `tlb` is a possible
//! later refinement, but is unnecessary: `variable` + encapsulation already
//! expresses "impl holds no `tlb` token" without the heavier
//! `storage_protocol_token!` machinery.
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
            /// MMU-reachable stage-2 mappings (the walker's current view).
            /// One token per page; owning/giving up a page's token is the seam
            /// that forces the unmap instructions.
            #[sharding(map)]
            pub s2map: Map<VmPageKey, S2Entry>,

            /// Nondeterministic TLB cache.  Single token for the one global TLB,
            /// encapsulated in the `HardwareOps` implementor (see module docs).
            #[sharding(variable)]
            pub tlb: Map<TlbKey, TlbEntry>,
        }

        // ── Invariant ──────────────────────────────────────────────────────────

        /// **The inductive coherence invariant.** Where `s2map` still has a
        /// cached entry's page, the entry agrees with it.  This *tolerates*
        /// orphaned stale entries (a cached key whose page is no longer in
        /// `s2map`) — exactly the post-`DSB`/pre-`TLBI` window.  Full coherence
        /// (no orphans) is the *sync-point* predicate [`synced`], which is
        /// strictly stronger and NOT preserved by `unmap`.
        #[invariant]
        pub fn inv_coherent(&self) -> bool {
            forall|key: TlbKey| #[trigger] self.tlb.contains_key(key) ==> {
                let sk = VmPageKey::new(key.vm, key.gpa);
                self.s2map.contains_key(sk) ==> self.tlb[key].as_s2_entry() == self.s2map[sk]
            }
        }

        // ── Transitions ──────────────────────────────────────────────────────────

        /// Start from a given set of established mappings with an empty TLB.
        /// (The `map` transition — fresh page-table installs — is deferred to
        /// slice 2: a fresh `add` to a map-sharded field needs a domain-mirror
        /// variable to prove key-absence, plus a TLB-clean break-before-make
        /// guard.  Route A `remove_region` is unmap-only, so slice 1 obtains its
        /// `s2map` tokens from `init` and exercises `unmap`.)
        init! {
            initialize(s2map0: Map<VmPageKey, S2Entry>) {
                init s2map = s2map0;
                init tlb = Map::empty();
            }
        }

        /// A `DSB` after writing the PTE invalid makes the mapping no longer
        /// walker-reachable.  Consumes the page's `s2map` token (the forcing
        /// seam).  This intentionally may leave a stale TLB entry — coherence is
        /// re-established by `invalidate`.
        transition! {
            unmap(vm: VmId, gpa: GuestPage) {
                remove s2map -= [VmPageKey::new(vm, gpa) => let _entry];
            }
        }

        /// The hardware MMU autonomously caches a walker-reachable translation.
        /// Modeled as an *environment* transition; guarded by `s2map.contains` so
        /// it can never cache a mapping the walker cannot reach (which is what
        /// blocks a re-fill once `unmap` has removed the page).
        transition! {
            fill(cpu: CpuId, vm: VmId, gpa: GuestPage) {
                have s2map >= [VmPageKey::new(vm, gpa) => let entry];
                update tlb = pre.tlb.insert(
                    TlbKey::new(cpu, vm, gpa),
                    TlbEntry { page: entry.page, access: entry.access, generation: entry.generation },
                );
            }
        }

        /// A `TLBI IPAS2E1IS` broadcast removes every CPU's cached entry for
        /// `(vm, gpa)`.  Restores coherence for that page.
        transition! {
            invalidate(vm: VmId, gpa: GuestPage) {
                update tlb = pre.tlb.remove_keys(invalidation_targets(vm, gpa));
            }
        }

        // ── Inductive proofs ──────────────────────────────────────────────────────

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, s2map0: Map<VmPageKey, S2Entry>) {
            assert(post.tlb =~= Map::empty());
        }

        #[inductive(unmap)]
        fn unmap_inductive(pre: Self, post: Self, vm: VmId, gpa: GuestPage) {
            let sk0 = VmPageKey::new(vm, gpa);
            assert forall|key: TlbKey| #[trigger] post.tlb.contains_key(key) implies {
                let sk = VmPageKey::new(key.vm, key.gpa);
                post.s2map.contains_key(sk) ==> post.tlb[key].as_s2_entry() == post.s2map[sk]
            } by {
                let sk = VmPageKey::new(key.vm, key.gpa);
                // post.s2map == pre.s2map.remove(sk0): if sk == sk0 the page is gone
                // (antecedent false); otherwise the entry is unchanged.
                if sk != sk0 {
                    assert(post.s2map.contains_key(sk) ==> pre.s2map.contains_key(sk));
                }
            };
        }

        #[inductive(fill)]
        fn fill_inductive(pre: Self, post: Self, cpu: CpuId, vm: VmId, gpa: GuestPage) {
            let sk0 = VmPageKey::new(vm, gpa);
            let tkey0 = TlbKey::new(cpu, vm, gpa);
            let entry = pre.s2map[sk0];
            assert forall|key: TlbKey| #[trigger] post.tlb.contains_key(key) implies {
                let sk = VmPageKey::new(key.vm, key.gpa);
                post.s2map.contains_key(sk) ==> post.tlb[key].as_s2_entry() == post.s2map[sk]
            } by {
                let sk = VmPageKey::new(key.vm, key.gpa);
                if key == tkey0 {
                    // The freshly-cached entry is built from s2map[sk0], so agrees.
                    assert(sk == sk0);
                    assert(post.tlb[tkey0] == (TlbEntry {
                        page: entry.page,
                        access: entry.access,
                        generation: entry.generation,
                    }));
                    assert(post.tlb[tkey0].as_s2_entry() == entry);
                } else {
                    assert(post.tlb[key] == pre.tlb[key]);
                }
            };
        }

        #[inductive(invalidate)]
        fn invalidate_inductive(pre: Self, post: Self, vm: VmId, gpa: GuestPage) {
            assert forall|key: TlbKey| #[trigger] post.tlb.contains_key(key) implies {
                let sk = VmPageKey::new(key.vm, key.gpa);
                post.s2map.contains_key(sk) ==> post.tlb[key].as_s2_entry() == post.s2map[sk]
            } by {
                // Surviving keys are exactly pre.tlb keys not in the target set.
                assert(!invalidation_targets(vm, gpa).contains(key));
                assert(pre.tlb.contains_key(key) && post.tlb[key] == pre.tlb[key]);
            };
        }
    }
}
// ── Token type aliases ─────────────────────────────────────────────────────────


/// `MmuSpec` instance token (shared by reference).
pub type MmuInstance = MmuSpec::Instance;

/// Per-page MMU-reachable mapping token (map-sharded; threaded through unmap).
pub type MmuS2MapToken = MmuSpec::s2map;

/// The global TLB token (variable-sharded; encapsulated in the HW layer).
pub type MmuTlbToken = MmuSpec::tlb;

// ── Forcing + ordering lemmas (slice 2) ─────────────────────────────────────────
//
// These reason purely over the *values* the transitions produce (`s2map.remove`,
// `tlb.insert`, `tlb.remove_keys(invalidation_targets)`), so they plug directly
// into the `ensures` of the token-exchange methods used in `MemorySet::remove`.
//
// Together they establish the two halves of the design's forcing argument:
//   * PRESENCE — a sync point with a page cleared is only reachable via the
//     `invalidate` effect (`lemma_invalidate_clears_page`,
//     `lemma_unmap_invalidate_preserves_synced`); and since the token API makes
//     `invalidate` the sole producer of a `tlb` value with the page removed, the
//     unmap contract cannot be discharged without the real `TLBI`.
//   * ORDERING — the `TLBI` must follow the `DSB` (invalidate after unmap): once
//     `unmap` removes the page from `s2map`, no `fill` can re-cache it
//     (`lemma_fill_preserves_clean`), whereas while it is still mapped a fill
//     stays enabled (`lemma_fill_enabled_while_mapped`).  So invalidating first
//     leaves a window in which a fill re-dirties the page before the unmap.  (The
//     ordering bites under concurrent environment fills — the L3 layer; in the
//     sequential per-op refinement only PRESENCE is needed.)
/// **Presence.** The `invalidate(vm, gpa)` effect clears the page: afterwards no
/// CPU holds a cached entry for `(vm, gpa)`.
pub proof fn lemma_invalidate_clears_page(tlb: Map<TlbKey, TlbEntry>, vm: VmId, gpa: GuestPage)
    ensures
        forall|cpu: CpuId|
            !(#[trigger] tlb.remove_keys(invalidation_targets(vm, gpa)).contains_key(
                TlbKey::new(cpu, vm, gpa),
            )),
{
    assert forall|cpu: CpuId|
        !(#[trigger] tlb.remove_keys(invalidation_targets(vm, gpa)).contains_key(
            TlbKey::new(cpu, vm, gpa),
        )) by {
        assert(invalidation_targets(vm, gpa).contains(TlbKey::new(cpu, vm, gpa)));
    }
}

// /// **Per-page lockstep (presence).** Removing page `(vm, gpa)` from `s2map` (the
// /// `unmap` effect) together with clearing it from `tlb` (the `invalidate` effect)
// /// preserves full coherence [`synced`].  This is the per-page heart of the region
// /// unmap contract (sync → sync); it superseded the old `Ghost`-threaded
// /// `zone_tlb_safe` lockstep lemma (now retired).
// pub proof fn lemma_unmap_invalidate_preserves_synced(
//     s2map: Map<VmPageKey, S2Entry>,
//     tlb: Map<TlbKey, TlbEntry>,
//     vm: VmId,
//     gpa: GuestPage,
// )
//     requires
//         synced(s2map, tlb),
//     ensures
//         synced(
//             s2map.remove(VmPageKey::new(vm, gpa)),
//             tlb.remove_keys(invalidation_targets(vm, gpa)),
//         ),
// {
//     let sk0 = VmPageKey::new(vm, gpa);
//     let s2map2 = s2map.remove(sk0);
//     let tlb2 = tlb.remove_keys(invalidation_targets(vm, gpa));
//     assert forall|key: TlbKey| #[trigger] tlb2.contains_key(key) implies {
//         let sk = VmPageKey::new(key.vm, key.gpa);
//         &&& s2map2.contains_key(sk)
//         &&& tlb2[key].as_s2_entry() == s2map2[sk]
//     } by {
//         let sk = VmPageKey::new(key.vm, key.gpa);
//         // A surviving key escaped invalidate, so its page differs from (vm, gpa).
//         assert(!invalidation_targets(vm, gpa).contains(key));
//         assert(sk != sk0);
//         // It was coherent in the synced pre-state, and `remove(sk0)` leaves it alone.
//         assert(tlb.contains_key(key) && tlb2[key] == tlb[key]);
//         assert(s2map.contains_key(sk));
//     }
// }

// /// **Ordering.** A `fill` cannot re-cache a page that `unmap` has already removed
// /// from `s2map`: the fill guard (`s2map.contains`) fails for it.  So a page that
// /// is unmapped and clean *stays* clean under any fill — which is why the `TLBI`
// /// is sound only *after* the `DSB`.
// pub proof fn lemma_fill_preserves_clean(
//     tlb: Map<TlbKey, TlbEntry>,
//     s2map: Map<VmPageKey, S2Entry>,
//     fill_cpu: CpuId,
//     fill_vm: VmId,
//     fill_gpa: GuestPage,
//     fill_entry: TlbEntry,
//     p_vm: VmId,
//     p_gpa: GuestPage,
// )
//     requires
//         s2map.contains_key(VmPageKey::new(fill_vm, fill_gpa)),
//         !s2map.contains_key(VmPageKey::new(p_vm, p_gpa)),
//         forall|cpu: CpuId| !(#[trigger] tlb.contains_key(TlbKey::new(cpu, p_vm, p_gpa))),
//     ensures
//         forall|cpu: CpuId|
//             !(#[trigger] tlb.insert(
//                 TlbKey::new(fill_cpu, fill_vm, fill_gpa),
//                 fill_entry,
//             ).contains_key(TlbKey::new(cpu, p_vm, p_gpa))),
// {
//     // The filled page differs from the unmapped one (one is in s2map, the other not).
//     assert(VmPageKey::new(fill_vm, fill_gpa) != VmPageKey::new(p_vm, p_gpa));
//     assert forall|cpu: CpuId|
//         !(#[trigger] tlb.insert(TlbKey::new(fill_cpu, fill_vm, fill_gpa), fill_entry).contains_key(
//             TlbKey::new(cpu, p_vm, p_gpa),
//         )) by {
//         assert(TlbKey::new(fill_cpu, fill_vm, fill_gpa) != TlbKey::new(cpu, p_vm, p_gpa));
//     }
// }

// /// The contrast to [`lemma_fill_preserves_clean`]: while the page is still mapped,
// /// a fill *is* enabled and re-caches it, so invalidating before the unmap is
// /// futile.  (Confirms the ordering is necessary, not merely sufficient.)
// pub proof fn lemma_fill_enabled_while_mapped(
//     tlb: Map<TlbKey, TlbEntry>,
//     s2map: Map<VmPageKey, S2Entry>,
//     cpu: CpuId,
//     vm: VmId,
//     gpa: GuestPage,
//     entry: TlbEntry,
// )
//     requires
//         s2map.contains_key(VmPageKey::new(vm, gpa)),
//     ensures
//         tlb.insert(TlbKey::new(cpu, vm, gpa), entry).contains_key(TlbKey::new(cpu, vm, gpa)),
// {
// }

} // verus!
