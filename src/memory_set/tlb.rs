//! TLB-coherence representation bridge between the per-zone software view and the
//! model's `MachineState::tlb_safe`.
//!
//! The per-page unmap *flushing* is now forced by the tokenized MMU
//! (`crate::machine::hardware::mmu` + `crate::hardware::mmu`, wired into
//! `VecMemorySet::remove` via `super::mmu_unmap`); the old `Ghost`-threaded
//! `zone_tlb_safe` lockstep/insert lemmas have been retired with it.
//!
//! What remains here is the **existential ↔ functional** coherence bridge, kept
//! for the point-5 `sync ⇒ wf MachineState` step:
//!
//! * [`zone_tlb_safe`] — the *existential* form (a cached key is backed by *some*
//!   mapping whose gpa matches; arithmetic-free, robust);
//! * [`tlb_coherent`] — the *functional* form (the body of
//!   `MachineState::tlb_safe`, keyed by `VmPageKey`);
//! * [`lemma_zone_tlb_safe_implies_tlb_coherent`] — the existential form over
//!   page-aligned mappings implies the functional one.
//!
//! [`gpa_of_vaddr`] is also used live by the forced unmap path.
use vstd::prelude::*;

use crate::address::{addr::SpecVAddr, frame::SpecFrame, region::SPEC_PAGE_SIZE};
use crate::machine::types::*;

verus! {

/// The guest page (IPA page number) of a page-aligned virtual address.
pub open spec fn gpa_of_vaddr(v: SpecVAddr) -> GuestPage {
    GuestPage(v.0 / SPEC_PAGE_SIZE)
}

/// The TLB entry a page-table frame is expected to produce once cached.
pub open spec fn frame_to_tlb_entry(f: SpecFrame) -> TlbEntry {
    TlbEntry {
        page: PhysPage(f.base.0 / SPEC_PAGE_SIZE),
        access: AccessPerms {
            read: f.attr.readable,
            write: f.attr.writable,
            execute: f.attr.executable,
        },
        generation: 0,
    }
}

/// Per-zone TLB coherence: every cached entry belongs to `vm` and agrees with the
/// page-table mapping for its gpa.  (Existential bridge: backed by *some* mapping
/// whose gpa matches — no `vaddr ↔ gpa` arithmetic needed.)
pub open spec fn zone_tlb_safe(
    mappings: Map<SpecVAddr, SpecFrame>,
    vm: VmId,
    tlb: Map<TlbKey, TlbEntry>,
) -> bool {
    forall|key: TlbKey| #[trigger]
        tlb.contains_key(key) ==> {
            &&& key.vm == vm
            &&& exists|v: SpecVAddr|
                #![trigger mappings.contains_key(v)]
                mappings.contains_key(v) && gpa_of_vaddr(v) == key.gpa && tlb[key]
                    == frame_to_tlb_entry(mappings[v])
        }
}

// ───────────────────────── functional bridge to the model ────────────────────
// `zone_tlb_safe` uses an *existential* correspondence (robust, arithmetic-free).
// The model's `MachineState::tlb_safe` is *functional*: it looks up
// `s2_map[VmPageKey(vm, gpa)]`.  These lemmas connect the two by projecting the
// page-table mappings to a stage-2 map and showing the existential coherence
// implies the functional one.
/// The page-aligned virtual address of a guest page (inverse of [`gpa_of_vaddr`]
/// on aligned addresses).
pub open spec fn vaddr_of_gpa(gpa: GuestPage) -> SpecVAddr {
    SpecVAddr(gpa.0 * SPEC_PAGE_SIZE)
}

/// The stage-2 entry a page-table frame projects to — the model's `S2Entry` form
/// of [`frame_to_tlb_entry`].
pub open spec fn frame_to_s2(f: SpecFrame) -> S2Entry {
    S2Entry {
        page: PhysPage(f.base.0 / SPEC_PAGE_SIZE),
        access: AccessPerms {
            read: f.attr.readable,
            write: f.attr.writable,
            execute: f.attr.executable,
        },
        generation: 0,
    }
}

/// The stage-2 map a single zone's page-table mappings induce (keyed like the
/// model's `s2_map`).
pub open spec fn pt_s2_map(mappings: Map<SpecVAddr, SpecFrame>, vm: VmId) -> Map<
    VmPageKey,
    S2Entry,
> {
    Map::new(
        |k: VmPageKey| k.vm == vm && mappings.contains_key(vaddr_of_gpa(k.gpa)),
        |k: VmPageKey| frame_to_s2(mappings[vaddr_of_gpa(k.gpa)]),
    )
}

/// The model's TLB-coherence predicate (the body of `MachineState::tlb_safe`),
/// stated over a bare `(s2_map, tlb)` pair so it can be discharged here.
pub open spec fn tlb_coherent(s2_map: Map<VmPageKey, S2Entry>, tlb: Map<TlbKey, TlbEntry>) -> bool {
    forall|key: TlbKey| #[trigger]
        tlb.contains_key(key) ==> {
            let sk = VmPageKey::new(key.vm, key.gpa);
            &&& s2_map.contains_key(sk)
            &&& tlb[key].as_s2_entry() == s2_map[sk]
        }
}

/// Round-trip on page-aligned addresses: `vaddr_of_gpa ∘ gpa_of_vaddr = id`.
pub proof fn lemma_vaddr_gpa_roundtrip(v: SpecVAddr)
    requires
        v.0 % SPEC_PAGE_SIZE == 0,
    ensures
        vaddr_of_gpa(gpa_of_vaddr(v)) == v,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(v.0 as int, SPEC_PAGE_SIZE as int);
    assert((v.0 / SPEC_PAGE_SIZE) * SPEC_PAGE_SIZE == v.0) by (nonlinear_arith)
        requires
            v.0 % SPEC_PAGE_SIZE == 0,
            v.0 as int == (SPEC_PAGE_SIZE as int) * (v.0 as int / SPEC_PAGE_SIZE as int)
                + v.0 as int % SPEC_PAGE_SIZE as int,
            SPEC_PAGE_SIZE == 0x1000nat,
    ;
}

/// `frame_to_tlb_entry` and `frame_to_s2` agree under `as_s2_entry`.
pub proof fn lemma_frame_to_tlb_entry_as_s2(f: SpecFrame)
    ensures
        frame_to_tlb_entry(f).as_s2_entry() == frame_to_s2(f),
{
}

/// **Functional bridge.** With page-aligned mapping keys, the existential
/// [`zone_tlb_safe`] implies the model-shaped [`tlb_coherent`] over the projected
/// stage-2 map — i.e. every cached entry matches `pt_s2_map[VmPageKey(vm, gpa)]`.
pub proof fn lemma_zone_tlb_safe_implies_tlb_coherent(
    mappings: Map<SpecVAddr, SpecFrame>,
    vm: VmId,
    tlb: Map<TlbKey, TlbEntry>,
)
    requires
        zone_tlb_safe(mappings, vm, tlb),
        forall|v: SpecVAddr| #[trigger] mappings.contains_key(v) ==> v.0 % SPEC_PAGE_SIZE == 0,
    ensures
        tlb_coherent(pt_s2_map(mappings, vm), tlb),
{
    let s2 = pt_s2_map(mappings, vm);
    assert forall|key: TlbKey| tlb.contains_key(key) implies {
        let sk = VmPageKey::new(key.vm, key.gpa);
        &&& s2.contains_key(sk)
        &&& tlb[key].as_s2_entry() == s2[sk]
    } by {
        let sk = VmPageKey::new(key.vm, key.gpa);
        // From `zone_tlb_safe`: `key` is for `vm` and backed by some mapping `v`.
        assert(key.vm == vm);
        let v = choose|v: SpecVAddr| #[trigger]
            mappings.contains_key(v) && gpa_of_vaddr(v) == key.gpa && tlb[key]
                == frame_to_tlb_entry(mappings[v]);
        // `v` is page-aligned, so `vaddr_of_gpa(key.gpa) == v`.
        lemma_vaddr_gpa_roundtrip(v);
        assert(vaddr_of_gpa(key.gpa) == v);
        // Hence `sk` is in the projection and its value comes from `mappings[v]`.
        assert(s2.contains_key(sk));
        assert(s2[sk] == frame_to_s2(mappings[v]));
        lemma_frame_to_tlb_entry_as_s2(mappings[v]);
    }
}

} // verus!
