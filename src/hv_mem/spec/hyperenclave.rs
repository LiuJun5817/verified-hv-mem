//! HyperEnclave memory-isolation policy.
//!
//! The policy separates physical pages into four externally checked classes:
//! normal-world memory, EPC memory, monitor memory, and the allocator pool.
//! DMA pages are a subset of normal-world memory.  The class partition is a
//! trusted configuration fact; assignment of private pages to individual
//! enclaves is dynamic state checked on every enclave insertion. Enclave EPC
//! pages and enclave GPT backing frames may be leaf-mapped. Normal-memory
//! regions may additionally be mapped into an enclave through an explicit
//! dynamic Shared transition; VeriHyMem's own page-table backing frames may
//! not be leaf-mapped.
//!
//! Private and Shared are protection classifications, not permanent physical
//! memory classes. EPC and enclave-owned GPT backing frames are eligible for
//! enclave Private mappings. Normal-memory marshalling pages remain physically
//! normal memory but enter the S2-Shared projection while an authorized enclave
//! mapping exists. After the final enclave mapping is removed, a page still
//! mapped by the root returns to the root's S2-Private projection. The
//! enclave-normal-page authorization itself is an integration premise.
//!
//! Executable operations for this state machine live in
//! `hv_mem::imp::hyperenclave`. Its policy-neutral software projection and
//! complete transition-refinement proof live in
//! `refinement::software::hyperenclave`.
use super::GhostZone;
use crate::{
    address::{addr::SpecPAddr, region::MemoryRegion},
    memory_set::SpecMemorySet,
    model::types::PhysPage,
};
use verus_state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;

verus! {

use crate::constants::*;

/// Zone zero is the normal-world translation domain.  Non-zero zones are
/// enclave translation domains.
pub open spec fn root_zone_id() -> nat {
    0
}

/// Physical pages that may be mapped by the normal-world CPU page table,
/// including dedicated sanitized backing pages intentionally exposed read-only.
pub uninterp spec fn normal_memory() -> Set<PhysPage>;

/// Physical pages from which enclaves receive private code/data pages.
pub uninterp spec fn epc_memory() -> Set<PhysPage>;

/// Hypervisor code, data, heap, and metadata.  No guest leaf mapping may target
/// this class.
pub uninterp spec fn monitor_pool() -> Set<PhysPage>;

/// Pages managed by VeriHyMem's global allocator for page tables and other
/// internal structures. These pages are statically configured and are not
/// inserted into a zone's leaf-mapping memory set.
pub uninterp spec fn allocator_pool() -> Set<PhysPage>;

/// GPT backing frames privately owned by enclave zone `zid`. HyperEnclave's
/// RAII allocator discipline supplies this dynamic ownership classification at
/// the integration boundary.
pub uninterp spec fn enclave_gpt_backing_frames(zid: nat) -> Set<PhysPage>;

/// Pages reachable by the root-cell IOMMU page table.
pub uninterp spec fn dma_memory() -> Set<PhysPage>;

/// Trusted result of the external memory-layout checker.
pub axiom fn memory_classes_pairwise_disjoint()
    ensures
        normal_memory().disjoint(epc_memory()),
        normal_memory().disjoint(monitor_pool()),
        normal_memory().disjoint(allocator_pool()),
        epc_memory().disjoint(monitor_pool()),
        epc_memory().disjoint(allocator_pool()),
        monitor_pool().disjoint(allocator_pool()),
;

/// Trusted result of the external DMA-configuration checker.
pub axiom fn dma_memory_is_normal_memory()
    ensures
        dma_memory().subset_of(normal_memory()),
;

/// An enclave GPT backing frame must come from the global allocator pool.
pub axiom fn enclave_gpt_backing_frames_are_allocator_memory()
    ensures
        forall|zid: nat, page: PhysPage| #[trigger]
            enclave_gpt_backing_frames(zid).contains(page)
                ==> allocator_pool().contains(page),
;

/// Physical page occupied by page index `i` of `region`.
pub open spec fn he_region_phys_page(region: MemoryRegion, i: nat) -> PhysPage {
    PhysPage(region.pstart@.0 / SPEC_PAGE_SIZE + i)
}

/// Complete physical-page footprint of `region`.
pub open spec fn he_region_phys_pages(region: MemoryRegion) -> Set<PhysPage> {
    Set::new(
        |page: PhysPage|
            exists|i: nat|
                0 <= i < region.pages && #[trigger] he_region_phys_page(region, i) == page,
    )
}

pub open spec fn region_in_normal_memory(region: MemoryRegion) -> bool {
    he_region_phys_pages(region).subset_of(normal_memory())
}

pub open spec fn region_in_epc_memory(region: MemoryRegion) -> bool {
    he_region_phys_pages(region).subset_of(epc_memory())
}

pub open spec fn region_in_monitor_pool(region: MemoryRegion) -> bool {
    he_region_phys_pages(region).subset_of(monitor_pool())
}

pub open spec fn region_in_allocator_pool(region: MemoryRegion) -> bool {
    he_region_phys_pages(region).subset_of(allocator_pool())
}

pub open spec fn region_in_enclave_gpt_backing_frames(
    zid: nat,
    region: MemoryRegion,
) -> bool {
    he_region_phys_pages(region).subset_of(enclave_gpt_backing_frames(zid))
}

/// Static integration obligation for the global allocator's complete backing
/// range.  Page-table and internal frames are allocated only from this range;
/// there is no runtime transition that changes its memory class.
pub open spec fn allocator_backing_in_allocator_pool(base: SpecPAddr, frames: nat) -> bool {
    forall|i: nat|
        0 <= i < frames ==> #[trigger]
            allocator_pool().contains(PhysPage(base.0 / SPEC_PAGE_SIZE + i))
}

pub open spec fn region_in_dma_memory(region: MemoryRegion) -> bool {
    he_region_phys_pages(region).subset_of(dma_memory())
}

/// Enclave leaf mappings come from private EPC pages or the enclave's GPT
/// backing frames. VeriHyMem's own page-table backing frames are not in either
/// class and therefore remain outside this authorization.
pub open spec fn region_in_enclave_memory(zid: nat, region: MemoryRegion) -> bool {
    region_in_epc_memory(region) || region_in_enclave_gpt_backing_frames(zid, region)
}

/// Currently installed enclave-private CPU regions. This is the semantic
/// source used by the HyperEnclave policy; `enclave_private_regions_view`
/// below is a conservative cache used by the serialized overlap check.
pub open spec fn live_enclave_private_regions(
    zid: nat,
    zone: GhostZone,
) -> Set<MemoryRegion> {
    if zid == root_zone_id() {
        Set::empty()
    } else {
        Set::new(
            |region: MemoryRegion|
                zone.cpu_mem_set.regions.contains(region)
                    && region_in_enclave_memory(zid, region),
        )
    }
}

/// Currently installed normal-memory CPU regions in an enclave zone. These
/// are the exact dynamic Shared regions for the HyperEnclave policy. Sharing
/// scope is deliberately not represented here: the caller supplies the
/// marshalling-buffer authorization as an interface premise.
pub open spec fn live_shared_regions(
    zid: nat,
    zone: GhostZone,
) -> Set<MemoryRegion> {
    if zid == root_zone_id() {
        Set::empty()
    } else {
        Set::new(
            |region: MemoryRegion|
                zone.cpu_mem_set.regions.contains(region)
                    && region_in_normal_memory(region),
        )
    }
}

/// Runtime overlap guard used while constructing an enclave. The candidate is
/// compared with the conservative private-region entry for every live
/// enclave. Root mappings need no such scan because normal memory is statically
/// disjoint from both EPC memory and the allocator pool.
pub open spec fn enclave_insert_allowed(
    enclave_private_regions_view: Map<nat, Set<MemoryRegion>>,
    zid: nat,
    region: MemoryRegion,
) -> bool {
    &&& zid != root_zone_id()
    &&& region_in_enclave_memory(zid, region)
    &&& forall|other_zid: nat, old_region: MemoryRegion|
        enclave_private_regions_view.contains_key(other_zid) && other_zid != root_zone_id()
            && #[trigger] enclave_private_regions_view[other_zid].contains(old_region)
            ==> !old_region.spec_overlaps_pmem(region)
}

/// Specification of the dynamic overlap check used while constructing an
/// enclave.
pub open spec fn regions_pmem_nonoverlap(
    existing: Seq<MemoryRegion>,
    candidate: MemoryRegion,
) -> bool {
    forall|i: int| 0 <= i < existing.len() ==> !existing[i].spec_overlaps_pmem(candidate)
}

/// Whether all distinct regions in one memory set are physically disjoint.
pub open spec fn memory_set_regions_pmem_disjoint(mem_set: SpecMemorySet) -> bool {
    forall|r1: MemoryRegion, r2: MemoryRegion| #[trigger]
        mem_set.regions.contains(r1) && #[trigger] mem_set.regions.contains(r2) && r1 != r2
            ==> !r1.spec_overlaps_pmem(r2)
}

/// Inserting a physically fresh region preserves pairwise physical disjointness.
pub proof fn lemma_insert_region_preserves_pmem_disjoint(
    mem_set: SpecMemorySet,
    region: MemoryRegion,
)
    requires
        mem_set.wf(),
        memory_set_regions_pmem_disjoint(mem_set),
        region.spec_valid(),
        !mem_set.overlaps_pmem(region),
    ensures
        memory_set_regions_pmem_disjoint(mem_set.insert_region(region)),
{
    let new_mem_set = mem_set.insert_region(region);
    assert forall|r1: MemoryRegion, r2: MemoryRegion| #[trigger]
        new_mem_set.regions.contains(r1) && #[trigger] new_mem_set.regions.contains(r2) && r1
            != r2 implies !r1.spec_overlaps_pmem(r2) by {
        if r1 == region {
            r2.lemma_overlaps_pmem_symmetric(region);
        }
    }
}

/// Removing a region preserves pairwise physical disjointness.
pub proof fn lemma_remove_region_preserves_pmem_disjoint(
    mem_set: SpecMemorySet,
    region: MemoryRegion,
)
    requires
        memory_set_regions_pmem_disjoint(mem_set),
    ensures
        memory_set_regions_pmem_disjoint(mem_set.remove_region_exact(region)),
{
    let new_mem_set = mem_set.remove_region_exact(region);
    assert(forall|r1: MemoryRegion, r2: MemoryRegion| #[trigger]
        new_mem_set.regions.contains(r1) && #[trigger] new_mem_set.regions.contains(r2) && r1
            != r2 ==> !r1.spec_overlaps_pmem(r2));
}

/// A valid normal-memory region cannot also be enclave-private memory.
pub proof fn lemma_normal_region_not_enclave_memory(zid: nat, region: MemoryRegion)
    requires
        region.spec_valid(),
        region_in_normal_memory(region),
    ensures
        !region_in_enclave_memory(zid, region),
{
    let page = he_region_phys_page(region, 0);
    assert(he_region_phys_pages(region).contains(page));
    memory_classes_pairwise_disjoint();
    enclave_gpt_backing_frames_are_allocator_memory();
}

/// The same class-separation fact in the direction used by private insertion.
pub proof fn lemma_enclave_region_not_normal_memory(zid: nat, region: MemoryRegion)
    requires
        region.spec_valid(),
        region_in_enclave_memory(zid, region),
    ensures
        !region_in_normal_memory(region),
{
    if region_in_normal_memory(region) {
        lemma_normal_region_not_enclave_memory(zid, region);
    }
}

/// Updating one zone and recording its exact live Shared set preserves the
/// global exact-view relation.
pub proof fn lemma_shared_regions_update_preserves_exact(
    zone_ids: Set<nat>,
    zones: Map<nat, GhostZone>,
    shared_regions: Map<nat, Set<MemoryRegion>>,
    zid: nat,
    new_zone: GhostZone,
)
    requires
        zones.dom() == zone_ids,
        shared_regions.dom() == zone_ids,
        zones.contains_key(zid),
        forall|other: nat| #[trigger]
            zones.contains_key(other) ==> shared_regions[other]
                == live_shared_regions(other, zones[other]),
    ensures
        shared_regions.insert(zid, live_shared_regions(zid, new_zone)).dom() == zone_ids,
        forall|other: nat| #[trigger]
            zones.insert(zid, new_zone).contains_key(other) ==> shared_regions.insert(
                zid,
                live_shared_regions(zid, new_zone),
            )[other] == live_shared_regions(other, zones.insert(zid, new_zone)[other]),
{ }

tokenized_state_machine! {
    HyperEnclaveSpec {
        fields {
            #[sharding(variable)]
            pub zone_ids: Set<nat>,

            #[sharding(map)]
            pub zones: Map<nat, GhostZone>,

            /// Conservative per-zone private-region cache used by serialized
            /// runtime overlap checks. An entry may contain regions that have
            /// since been removed, but never omits a live enclave-private
            /// region. Normal-memory Shared regions never enter this cache.
            #[sharding(variable)]
            pub enclave_private_regions_view: Map<nat, Set<MemoryRegion>>,

            /// Exact per-enclave set of installed normal-memory Shared
            /// regions. Unlike `enclave_private_regions_view`, this state is not
            /// conservative: removing the final Shared mapping must allow the
            /// affected pages to return to the root's S2-Private projection.
            #[sharding(variable)]
            pub shared_regions: Map<nat, Set<MemoryRegion>>,
        }

        #[invariant]
        pub fn inv_zone_ids(&self) -> bool {
            self.zones.dom() == self.zone_ids
        }

        #[invariant]
        pub fn inv_enclave_private_regions_view_covers_live_regions(&self) -> bool {
            &&& self.enclave_private_regions_view.dom() == self.zone_ids
            &&& forall|zid: nat| #[trigger]
                self.zones.contains_key(zid) ==> {
                    &&& live_enclave_private_regions(zid, self.zones[zid]).subset_of(
                        self.enclave_private_regions_view[zid],
                    )
                    &&& forall|region: MemoryRegion| #[trigger]
                        self.enclave_private_regions_view[zid].contains(region) ==> {
                            &&& zid != root_zone_id()
                            &&& region.spec_valid()
                            &&& region_in_enclave_memory(zid, region)
                        }
                }
        }

        /// The Shared-region view is exact. Its root entry is empty, and every
        /// non-root entry is precisely the normal-memory subset of that
        /// enclave's installed CPU regions.
        #[invariant]
        pub fn inv_shared_regions_exact(&self) -> bool {
            &&& self.shared_regions.dom() == self.zone_ids
            &&& forall|zid: nat| #[trigger]
                self.zones.contains_key(zid) ==> self.shared_regions[zid]
                    == live_shared_regions(zid, self.zones[zid])
        }

        /// Per-zone class policy. The normal world may map normal pages and root DMA
        /// pages. An enclave may map private EPC/GPT backing frames or dynamic
        /// normal-memory Shared regions on the CPU side and has no IOMMU
        /// mappings in the initial integration profile.
        #[invariant]
        pub fn inv_class_policy(&self) -> bool {
            forall|zid: nat| #[trigger] self.zones.contains_key(zid) ==> {
                &&& self.zones[zid].wf()
                &&& if zid == root_zone_id() {
                    &&& forall|r: MemoryRegion| #[trigger]
                        self.zones[zid].cpu_mem_set.regions.contains(r)
                            ==> region_in_normal_memory(r)
                    &&& forall|r: MemoryRegion| #[trigger]
                        self.zones[zid].iommu_mem_set.regions.contains(r)
                            ==> region_in_dma_memory(r)
                } else {
                    &&& forall|r: MemoryRegion| #[trigger]
                        self.zones[zid].cpu_mem_set.regions.contains(r)
                            ==> region_in_enclave_memory(zid, r) || region_in_normal_memory(r)
                    &&& self.zones[zid].iommu_mem_set.empty()
                }
            }
        }

        /// Dynamic exclusivity invariant for enclave-private physical
        /// mappings. Normal-memory Shared regions are intentionally excluded.
        #[invariant]
        pub fn inv_enclave_regions_pairwise_disjoint(&self) -> bool {
            forall|zid1: nat, zid2: nat, r1: MemoryRegion, r2: MemoryRegion|
                self.zones.contains_key(zid1) && self.zones.contains_key(zid2)
                    && zid1 != root_zone_id() && zid2 != root_zone_id()
                    && #[trigger] self.zones[zid1].cpu_mem_set.regions.contains(r1)
                    && #[trigger] self.zones[zid2].cpu_mem_set.regions.contains(r2)
                    && region_in_enclave_memory(zid1, r1)
                    && region_in_enclave_memory(zid2, r2)
                    && (zid1 != zid2 || r1 != r2)
                    ==> !r1.spec_overlaps_pmem(r2)
        }

        /// The executable root-IOMMU insertion rejects physical aliases. Keep
        /// that fact in the TSM so a removed DMA region releases pages exactly
        /// when its mappings disappear.
        #[invariant]
        pub fn inv_root_iommu_regions_pmem_disjoint(&self) -> bool {
            self.zones.contains_key(root_zone_id()) ==> memory_set_regions_pmem_disjoint(
                self.zones[root_zone_id()].iommu_mem_set,
            )
        }

        /// Reachable memory sets contain finitely many operation units. This is
        /// later used to refine clear operations to finite removal traces.
        #[invariant]
        pub fn inv_region_sets_finite(&self) -> bool {
            forall|zid: nat| #[trigger] self.zones.contains_key(zid) ==> {
                &&& self.zones[zid].cpu_mem_set.regions.finite()
                &&& self.zones[zid].iommu_mem_set.regions.finite()
            }
        }

        init! {
            initialize() {
                init zone_ids = Set::empty();
                init zones = Map::empty();
                init enclave_private_regions_view = Map::empty();
                init shared_regions = Map::empty();
            }
        }

        transition! {
            add_zone(zid: nat) {
                require(!pre.zone_ids.contains(zid));
                update zone_ids = pre.zone_ids.insert(zid);
                add zones += [zid => GhostZone {
                    cpu_mem_set: SpecMemorySet {
                        regions: Set::empty(),
                        mappings: Map::empty(),
                    },
                    iommu_mem_set: SpecMemorySet {
                        regions: Set::empty(),
                        mappings: Map::empty(),
                    },
                }];
                update enclave_private_regions_view = pre.enclave_private_regions_view.insert(
                    zid,
                    Set::empty(),
                );
                update shared_regions = pre.shared_regions.insert(
                    zid,
                    Set::empty(),
                );
            }
        }

        transition! {
            remove_zone(zid: nat) {
                remove zones -= [zid => let zone];
                require(zone.cpu_mem_set.empty());
                require(zone.iommu_mem_set.empty());
                update zone_ids = pre.zone_ids.remove(zid);
                update enclave_private_regions_view = pre.enclave_private_regions_view.remove(zid);
                update shared_regions = pre.shared_regions.remove(zid);
            }
        }

        /// Refresh one entry of the conservative global cache from its
        /// map-sharded zone token. This is a ghost-only operation used by the
        /// serialized private-region insertion scan.
        transition! {
            synchronize_enclave_private_regions_view(zid: nat) {
                remove zones -= [zid => let zone];
                update enclave_private_regions_view = pre.enclave_private_regions_view.insert(
                    zid,
                    live_enclave_private_regions(zid, zone),
                );
                add zones += [zid => zone];
            }
        }

        /// Assign a normal-world region to the root zone.
        transition! {
            cpu_insert_normal_region(region: MemoryRegion) {
                remove zones -= [root_zone_id() => let zone];
                require(region.spec_valid());
                require(region_in_normal_memory(region));
                require(!zone.cpu_mem_set.regions.contains(region));
                require(!zone.cpu_mem_set.overlaps_vmem(region));
                add zones += [root_zone_id() => zone.cpu_insert_region(region)];
            }
        }

        /// Dynamically assign an EPC or GPT backing region to one enclave.
        transition! {
            cpu_insert_enclave_private_region(zid: nat, region: MemoryRegion) {
                remove zones -= [zid => let zone];
                require(region.spec_valid());
                require(region_in_enclave_memory(zid, region));
                require(enclave_insert_allowed(pre.enclave_private_regions_view, zid, region));
                require(!zone.cpu_mem_set.regions.contains(region));
                require(!zone.cpu_mem_set.overlaps_vmem(region));
                add zones += [zid => zone.cpu_insert_region(region)];
                update enclave_private_regions_view = pre.enclave_private_regions_view.insert(
                    zid,
                    live_enclave_private_regions(zid, zone.cpu_insert_region(region)),
                );
            }
        }

        /// Install an explicitly authorized normal-memory Shared region in an
        /// enclave CPU stage-2 table. The sharing scope is an integration
        /// premise; the TSM records only the active Shared mapping.
        transition! {
            cpu_insert_enclave_shared_region(zid: nat, region: MemoryRegion) {
                remove zones -= [zid => let zone];
                require(zid != root_zone_id());
                require(region.spec_valid());
                require(region_in_normal_memory(region));
                require(!zone.cpu_mem_set.regions.contains(region));
                require(!zone.cpu_mem_set.overlaps_vmem(region));
                add zones += [zid => zone.cpu_insert_region(region)];
                update shared_regions = pre.shared_regions.insert(
                    zid,
                    live_shared_regions(zid, zone.cpu_insert_region(region)),
                );
            }
        }

        transition! {
            cpu_remove_region(zid: nat, region: MemoryRegion) {
                remove zones -= [zid => let zone];
                require(zone.cpu_mem_set.regions.contains(region));
                add zones += [zid => zone.cpu_remove_region(region)];
                update shared_regions = pre.shared_regions.insert(
                    zid,
                    live_shared_regions(zid, zone.cpu_remove_region(region)),
                );
            }
        }

        /// Tear down all CPU mappings of one enclave before removing its zone.
        transition! {
            cpu_clear_enclave_regions(zid: nat) {
                remove zones -= [zid => let zone];
                require(zid != root_zone_id());
                add zones += [zid => zone.cpu_clear()];
                update shared_regions = pre.shared_regions.insert(
                    zid,
                    Set::empty(),
                );
            }
        }

        /// Root-only IOMMU mappings. Enclave IOMMU sets remain empty.
        transition! {
            iommu_insert_region(region: MemoryRegion) {
                remove zones -= [root_zone_id() => let zone];
                require(region.spec_valid());
                require(region_in_dma_memory(region));
                require(!zone.iommu_mem_set.regions.contains(region));
                require(!zone.iommu_mem_set.overlaps_vmem(region));
                require(!zone.iommu_mem_set.overlaps_pmem(region));
                add zones += [root_zone_id() => zone.iommu_insert_region(region)];
            }
        }

        transition! {
            iommu_remove_region(region: MemoryRegion) {
                remove zones -= [root_zone_id() => let zone];
                require(zone.iommu_mem_set.regions.contains(region));
                add zones += [root_zone_id() => zone.iommu_remove_region(region)];
            }
        }

        /// Tear down all root-cell IOMMU mappings. Enclave IOMMU sets are
        /// always empty and therefore have no executable mutation operation.
        transition! {
            iommu_clear_regions() {
                remove zones -= [root_zone_id() => let zone];
                add zones += [root_zone_id() => zone.iommu_clear()];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(add_zone)]
        fn add_zone_inductive(pre: Self, post: Self, zid: nat) {
            assert(forall|other: nat| #[trigger]
                post.zones.contains_key(other) ==> post.shared_regions[other]
                    == live_shared_regions(other, post.zones[other]));
        }

        #[inductive(remove_zone)]
        fn remove_zone_inductive(pre: Self, post: Self, zid: nat) { }

        #[inductive(synchronize_enclave_private_regions_view)]
        fn synchronize_enclave_private_regions_view_inductive(
            pre: Self,
            post: Self,
            zid: nat,
        ) {
            assert(pre.zones.contains_key(zid));
            assert(pre.zone_ids.contains(zid));
            assert(pre.enclave_private_regions_view.contains_key(zid));
            assert(post.zone_ids == pre.zone_ids);
            assert(post.zones == pre.zones);
            assert(post.enclave_private_regions_view == pre.enclave_private_regions_view.insert(
                zid,
                live_enclave_private_regions(zid, pre.zones[zid]),
            ));
            assert(post.enclave_private_regions_view.dom()
                =~= pre.enclave_private_regions_view.dom());
        }

        #[inductive(cpu_insert_normal_region)]
        fn cpu_insert_normal_region_inductive(
            pre: Self,
            post: Self,
            region: MemoryRegion,
        ) {
            let old_zone = pre.zones[root_zone_id()];
            assert(old_zone.wf());
            old_zone.cpu_mem_set.lemma_insert_region_wf(region);
        }

        #[inductive(cpu_insert_enclave_private_region)]
        fn cpu_insert_enclave_private_region_inductive(
            pre: Self,
            post: Self,
            zid: nat,
            region: MemoryRegion,
        ) {
            let old_zone = pre.zones[zid];
            assert(old_zone.wf());
            old_zone.cpu_mem_set.lemma_insert_region_wf(region);
            let new_zone = old_zone.cpu_insert_region(region);
            lemma_enclave_region_not_normal_memory(zid, region);
            assert(post.enclave_private_regions_view.dom() =~= post.zone_ids);
            assert(forall|other: nat| #[trigger]
                post.zones.contains_key(other) ==> {
                    &&& live_enclave_private_regions(other, post.zones[other]).subset_of(
                        post.enclave_private_regions_view[other],
                    )
                    &&& forall|cached: MemoryRegion| #[trigger]
                        post.enclave_private_regions_view[other].contains(cached) ==> {
                            &&& other != root_zone_id()
                            &&& cached.spec_valid()
                            &&& region_in_enclave_memory(other, cached)
                        }
                });
            assert(live_shared_regions(zid, new_zone)
                =~= live_shared_regions(zid, old_zone));
            assert(forall|other: nat| #[trigger]
                post.zones.contains_key(other) ==> post.shared_regions[other]
                    == live_shared_regions(other, post.zones[other]));
            assert forall|zid1: nat, zid2: nat, r1: MemoryRegion, r2: MemoryRegion|
                post.zones.contains_key(zid1) && post.zones.contains_key(zid2)
                    && zid1 != root_zone_id() && zid2 != root_zone_id()
                    && #[trigger] post.zones[zid1].cpu_mem_set.regions.contains(r1)
                    && #[trigger] post.zones[zid2].cpu_mem_set.regions.contains(r2)
                    && region_in_enclave_memory(zid1, r1)
                    && region_in_enclave_memory(zid2, r2)
                    && (zid1 != zid2 || r1 != r2)
                    implies !r1.spec_overlaps_pmem(r2) by {
                let r1_is_new = !pre.zones[zid1].cpu_mem_set.regions.contains(r1);
                let r2_is_new = !pre.zones[zid2].cpu_mem_set.regions.contains(r2);
                if r1_is_new {
                    assert(pre.enclave_private_regions_view[zid2].contains(r2));
                    r2.lemma_overlaps_pmem_symmetric(region);
                } else if r2_is_new {
                    assert(pre.enclave_private_regions_view[zid1].contains(r1));
                }
            }
        }

        #[inductive(cpu_insert_enclave_shared_region)]
        fn cpu_insert_enclave_shared_region_inductive(
            pre: Self,
            post: Self,
            zid: nat,
            region: MemoryRegion,
        ) {
            let old_zone = pre.zones[zid];
            assert(old_zone.wf());
            old_zone.cpu_mem_set.lemma_insert_region_wf(region);
            lemma_normal_region_not_enclave_memory(zid, region);
            lemma_shared_regions_update_preserves_exact(
                pre.zone_ids,
                pre.zones,
                pre.shared_regions,
                zid,
                old_zone.cpu_insert_region(region),
            );
        }

        #[inductive(cpu_remove_region)]
        fn cpu_remove_region_inductive(
            pre: Self,
            post: Self,
            zid: nat,
            region: MemoryRegion,
        ) {
            let old_zone = pre.zones[zid];
            assert(old_zone.wf());
            old_zone.cpu_mem_set.lemma_remove_region_exact_wf(region);
            lemma_shared_regions_update_preserves_exact(
                pre.zone_ids,
                pre.zones,
                pre.shared_regions,
                zid,
                old_zone.cpu_remove_region(region),
            );
        }

        #[inductive(cpu_clear_enclave_regions)]
        fn cpu_clear_enclave_regions_inductive(pre: Self, post: Self, zid: nat) {
            assert(live_shared_regions(zid, pre.zones[zid].cpu_clear()) =~= Set::empty());
            lemma_shared_regions_update_preserves_exact(
                pre.zone_ids,
                pre.zones,
                pre.shared_regions,
                zid,
                pre.zones[zid].cpu_clear(),
            );
        }

        #[inductive(iommu_insert_region)]
        fn iommu_insert_region_inductive(
            pre: Self,
            post: Self,
            region: MemoryRegion,
        ) {
            let old_zone = pre.zones[root_zone_id()];
            assert(old_zone.wf());
            old_zone.iommu_mem_set.lemma_insert_region_wf(region);
            lemma_insert_region_preserves_pmem_disjoint(old_zone.iommu_mem_set, region);
        }

        #[inductive(iommu_remove_region)]
        fn iommu_remove_region_inductive(
            pre: Self,
            post: Self,
            region: MemoryRegion,
        ) {
            let old_zone = pre.zones[root_zone_id()];
            assert(old_zone.wf());
            old_zone.iommu_mem_set.lemma_remove_region_exact_wf(region);
            lemma_remove_region_preserves_pmem_disjoint(old_zone.iommu_mem_set, region);
        }

        #[inductive(iommu_clear_regions)]
        fn iommu_clear_regions_inductive(pre: Self, post: Self) { }
    }
}

pub type HyperEnclaveSpecInstance = HyperEnclaveSpec::Instance;

pub type HyperEnclaveZoneIdsToken = HyperEnclaveSpec::zone_ids;

pub type HyperEnclaveZoneToken = HyperEnclaveSpec::zones;

pub type HyperEnclavePrivateRegionsViewToken = HyperEnclaveSpec::enclave_private_regions_view;

pub type HyperEnclaveSharedRegionsToken = HyperEnclaveSpec::shared_regions;

} // verus!
