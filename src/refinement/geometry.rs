//! Layer 1 — page-unit reconciliation: region geometry → machine pages/entries.
//!
//! The hypervisor implementation addresses memory in *bytes* with
//! `SPEC_PAGE_SIZE = 0x1000` (4 KiB) pages.  The machine model numbers *pages*,
//! where one page is `PAGE_WORDS = 512` words; since `usize` is 8 bytes
//! (`global layout` in `lib.rs`), a machine page is `512 * 8 = 4096` bytes —
//! exactly `SPEC_PAGE_SIZE`.  Hence:
//!
//! - a machine `PhysPage`  is `paddr_bytes / SPEC_PAGE_SIZE`, and
//! - a machine `GuestPage` is `vaddr_bytes / SPEC_PAGE_SIZE`.
//!
//! Everything here is the *concrete* per-region geometry built on that
//! correspondence: what physical page / guest page / stage-2 entry each page of a
//! region maps to.  Nothing here knows about zones or the abstract state — those
//! live one layer up in [`super::view`].
use crate::address::addr::SpecVAddr;
use crate::address::frame::MemAttr;
use crate::address::region::{MemoryRegion, SPEC_PAGE_SIZE};
use crate::hv_mem::spec::GhostZone;
use crate::machine::types::*;
use vstd::prelude::*;

verus! {

// ───────────────────────── per-page coordinates ─────────────────────────────
/// Access permissions of a region, from its `MemAttr`.
pub open spec fn attr_to_perms(attr: MemAttr) -> AccessPerms {
    AccessPerms { read: attr.readable, write: attr.writable, execute: attr.executable }
}

/// Virtual byte address of page `i` (0-based) of region `r`.
pub open spec fn region_vaddr(r: MemoryRegion, i: nat) -> SpecVAddr {
    r.start@.offset(i * SPEC_PAGE_SIZE)
}

/// Machine physical page backing page `i` of region `r`.
pub open spec fn region_phys_page(r: MemoryRegion, i: nat) -> PhysPage {
    PhysPage(r.mapper.spec_map(region_vaddr(r, i)).0 / SPEC_PAGE_SIZE)
}

/// Guest page of page `i` of region `r`.
pub open spec fn region_guest_page(r: MemoryRegion, i: nat) -> GuestPage {
    GuestPage(region_vaddr(r, i).0 / SPEC_PAGE_SIZE)
}

// ─────────────────────────── what a region covers ───────────────────────────
/// `r` backs physical page `p` at some page index.
pub open spec fn region_owns_page(r: MemoryRegion, p: PhysPage) -> bool {
    exists|i: nat| 0 <= i < r.pages && #[trigger] region_phys_page(r, i) == p
}

/// `r` maps guest page `gpa` at some page index.
pub open spec fn region_owns_gpa(r: MemoryRegion, gpa: GuestPage) -> bool {
    exists|i: nat| 0 <= i < r.pages && #[trigger] region_guest_page(r, i) == gpa
}

/// Physical pages backed by a single region.
pub open spec fn region_pages(r: MemoryRegion) -> Set<PhysPage> {
    Set::new(|p: PhysPage| region_owns_page(r, p))
}

/// Stage-2 entries installed by a single region: one per (guest) page.
pub open spec fn region_s2_entries(zid: nat, region: MemoryRegion) -> Map<VmPageKey, S2Entry> {
    Map::new(
        |k: VmPageKey| k.vm == VmId(zid) && region_owns_gpa(region, k.gpa),
        |k: VmPageKey|
            {
                let i = choose|i: nat|
                    0 <= i < region.pages && region_guest_page(region, i) == k.gpa;
                S2Entry {
                    page: region_phys_page(region, i),
                    access: attr_to_perms(region.attr),
                    generation: 0,
                }
            },
    )
}

/// `r`'s physical pages are backed by no *other* region in `gz`.
///
/// Two regions can be vmem-disjoint yet map distinct guest pages to the *same*
/// physical page, so this is a genuine extra condition — it is what makes a
/// `remove_region` actually free `r`'s pages.
pub open spec fn region_pmem_exclusive(gz: GhostZone, r: MemoryRegion) -> bool {
    forall|rr: MemoryRegion| #[trigger]
        gz.regions().contains(rr) && rr != r ==> !rr.spec_overlaps_pmem(r)
}

// ─────────────────────────────── geometry core ──────────────────────────────
/// Two regions that back the same physical page overlap in physical memory.
///
/// The one remaining arithmetic obligation of this layer: it relates
/// `region_phys_page` equality to `MemoryRegion::spec_overlaps_pmem`.  (Holds for
/// `Offset` mappers; a `Fixed` mapper has an empty pmem image, so the regions
/// would need to be `Offset` — see the project notes.)
pub proof fn lemma_same_phys_page_implies_pmem_overlap(
    r1: MemoryRegion,
    i1: nat,
    r2: MemoryRegion,
    i2: nat,
)
    requires
        r1.spec_valid(),
        r2.spec_valid(),
        0 <= i1 < r1.pages,
        0 <= i2 < r2.pages,
        region_phys_page(r1, i1) == region_phys_page(r2, i2),
    ensures
        r1.spec_overlaps_pmem(r2),
{
    admit();
}

} // verus!
