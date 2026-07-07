//! Geometry and conversion between **implementation types** (the byte-level
//! page-table view: [`SpecVAddr`], [`SpecFrame`] from [`crate::address`]) and
//! **model types** (the abstract stage-2 view: [`GuestPage`], [`S2Entry`],
//! [`PhysPage`], [`VmPageKey`] from [`crate::model::types`]).
//!
//! This is the single place those two worlds meet.  Everything here is a pure
//! function (plus the arithmetic lemmas characterizing it); no state, no
//! refinement-specific predicates.
use crate::address::addr::{SpecPAddr, SpecVAddr};
use crate::address::frame::{MemAttr, SpecFrame};
use crate::model::types::{AccessPerms, GuestPage, PhysPage, S2Entry, VmId, VmPageKey};
use vstd::prelude::*;

verus! {
    
use crate::address::region::SPEC_PAGE_SIZE;

// ─────────────────────────── page-number extraction ───────────────────────────
// The two primitives that turn a byte address into its (model) page number — the
// single home of the `addr / page_size` arithmetic.
/// The guest page (IPA page number) of a page-aligned virtual address.
pub open spec fn gpa_of_vaddr(v: SpecVAddr) -> GuestPage {
    GuestPage(v.0 / SPEC_PAGE_SIZE)
}

/// The page-aligned virtual address of a guest page (inverse of [`gpa_of_vaddr`]
/// on aligned addresses).
pub open spec fn vaddr_of_gpa(gpa: GuestPage) -> SpecVAddr {
    SpecVAddr(gpa.0 * SPEC_PAGE_SIZE)
}

/// The physical page (frame number) of a page-aligned physical address.
pub open spec fn phys_page_of_paddr(pa: SpecPAddr) -> PhysPage {
    PhysPage(pa.0 / SPEC_PAGE_SIZE)
}

/// The machine physical page a page-table frame backs.
pub open spec fn frame_phys_page(f: SpecFrame) -> PhysPage {
    phys_page_of_paddr(f.base)
}

/// The model access permissions of a page-table memory attribute.
pub open spec fn attr_to_perms(attr: MemAttr) -> AccessPerms {
    AccessPerms { read: attr.readable, write: attr.writable, execute: attr.executable }
}

// ─────────────────── byte-view ↔ stage-2 (`s2_map`) projection ───────────────────
// These connect the page-table's `Map<SpecVAddr, SpecFrame>` (the software byte
// view) to the model's `Map<GuestPage, S2Entry>` (the MMU-reachable stage-2 map).
/// The stage-2 entry a page-table frame projects to.
pub open spec fn frame_to_s2(f: SpecFrame) -> S2Entry {
    S2Entry { page: frame_phys_page(f), access: attr_to_perms(f.attr), generation: 0 }
}

/// `vaddr_of_gpa` is injective (multiplication by the constant page size).
pub proof fn lemma_vaddr_of_gpa_injective(g1: GuestPage, g2: GuestPage)
    requires
        vaddr_of_gpa(g1) == vaddr_of_gpa(g2),
    ensures
        g1 == g2,
{
}

/// One zone's MMU-reachable stage-2 slice (`gpa -> S2Entry`) induced by its
/// page-table mappings — the value a zone's per-vm `s2map` token must equal at a
/// sync point.
pub open spec fn pt_s2map_inner(mappings: Map<SpecVAddr, SpecFrame>) -> Map<GuestPage, S2Entry> {
    Map::new(
        |g: GuestPage| mappings.contains_key(vaddr_of_gpa(g)),
        |g: GuestPage| frame_to_s2(mappings[vaddr_of_gpa(g)]),
    )
}

/// Flatten the per-vm reachable map into the machine-keyed reachable map:
/// `(vm, gpa) ↦ s2map[vm][gpa]`.  This is the `HardwareView::s2map` the MMU governs.
pub open spec fn flatten_s2map(m: Map<VmId, Map<GuestPage, S2Entry>>) -> Map<VmPageKey, S2Entry> {
    Map::new(
        |k: VmPageKey| m.contains_key(k.vm) && m[k.vm].contains_key(k.gpa),
        |k: VmPageKey| m[k.vm][k.gpa],
    )
}

// ───────────────────────────── arithmetic facts ─────────────────────────────
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

/// Removing a page-aligned `vaddr` from the byte map removes exactly its guest
/// page from the projected slice — so after `pt.unmap(vaddr)` the slice loses
/// precisely `gpa_of_vaddr(vaddr)`, matching the `unmap_dsb_tlbi` token effect.
pub proof fn lemma_pt_s2map_inner_remove(mappings: Map<SpecVAddr, SpecFrame>, vaddr: SpecVAddr)
    requires
        vaddr.0 % SPEC_PAGE_SIZE == 0,
    ensures
        pt_s2map_inner(mappings.remove(vaddr)) == pt_s2map_inner(mappings).remove(
            gpa_of_vaddr(vaddr),
        ),
{
    let g0 = gpa_of_vaddr(vaddr);
    let lhs = pt_s2map_inner(mappings.remove(vaddr));
    let rhs = pt_s2map_inner(mappings).remove(g0);
    lemma_vaddr_gpa_roundtrip(vaddr);
    assert forall|g: GuestPage| #[trigger] lhs.contains_key(g) <==> rhs.contains_key(g) by {
        if vaddr_of_gpa(g) == vaddr {
            assert(vaddr_of_gpa(g) == vaddr_of_gpa(g0));
            assert(g == g0) by (nonlinear_arith)
                requires
                    g.0 * SPEC_PAGE_SIZE == g0.0 * SPEC_PAGE_SIZE,
                    SPEC_PAGE_SIZE == 0x1000nat,
            ;
        }
    }
    assert forall|g: GuestPage| #[trigger] lhs.contains_key(g) implies lhs[g] == rhs[g] by {}
    assert(lhs =~= rhs);
}

/// Inserting a page-aligned `vaddr => frame` into the byte map inserts exactly its
/// guest page into the projected slice — matching the `map_dsb` token effect.
pub proof fn lemma_pt_s2map_inner_insert(
    mappings: Map<SpecVAddr, SpecFrame>,
    vaddr: SpecVAddr,
    frame: SpecFrame,
)
    requires
        vaddr.0 % SPEC_PAGE_SIZE == 0,
    ensures
        pt_s2map_inner(mappings.insert(vaddr, frame)) == pt_s2map_inner(mappings).insert(
            gpa_of_vaddr(vaddr),
            frame_to_s2(frame),
        ),
{
    let g0 = gpa_of_vaddr(vaddr);
    let lhs = pt_s2map_inner(mappings.insert(vaddr, frame));
    let rhs = pt_s2map_inner(mappings).insert(g0, frame_to_s2(frame));
    lemma_vaddr_gpa_roundtrip(vaddr);
    assert forall|g: GuestPage| #[trigger] lhs.contains_key(g) <==> rhs.contains_key(g) by {
        if vaddr_of_gpa(g) == vaddr {
            assert(vaddr_of_gpa(g) == vaddr_of_gpa(g0));
            assert(g == g0) by (nonlinear_arith)
                requires
                    g.0 * SPEC_PAGE_SIZE == g0.0 * SPEC_PAGE_SIZE,
                    SPEC_PAGE_SIZE == 0x1000nat,
            ;
        }
    }
    assert forall|g: GuestPage| #[trigger] lhs.contains_key(g) implies lhs[g] == rhs[g] by {
        if g != g0 {
            assert(vaddr_of_gpa(g) != vaddr) by {
                if vaddr_of_gpa(g) == vaddr {
                    assert(g == g0) by (nonlinear_arith)
                        requires
                            g.0 * SPEC_PAGE_SIZE == g0.0 * SPEC_PAGE_SIZE,
                            SPEC_PAGE_SIZE == 0x1000nat,
                    ;
                }
            }
        }
    }
    assert(lhs =~= rhs);
}

} // verus!
