//! Draft HyperEnclave memory-isolation policy.
//!
//! The demo separates physical pages into four externally checked classes:
//! normal-world memory, EPC memory, monitor memory, and the allocator pool.
//! DMA pages are a subset of normal-world memory.  The class partition is a
//! trusted configuration fact; assignment of EPC pages to individual enclaves
//! is dynamic state checked on every enclave insertion. `ALLOCATOR_POOL` is
//! reserved for page-table and other internal frames and never appears as a
//! zone-visible region.
//!
//! Executable operations for this state machine live in
//! `hv_mem::imp::hyperenclave`.  Refinement to the policy-neutral
//! software/machine models remains separate follow-up work.
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

/// Enclave leaf mappings come only from private EPC pages. `ALLOCATOR_POOL`
/// frames back translation structures but are not leaf-mapped into a zone.
pub open spec fn region_in_enclave_memory(region: MemoryRegion) -> bool {
    region_in_epc_memory(region)
}

/// Runtime overlap guard used while constructing an enclave. The candidate is
/// compared with the conservative EPC-region entry for every live enclave.
/// Root mappings need no such scan because their physical class is statically
/// disjoint from EPC memory.
pub open spec fn enclave_insert_allowed(
    epc_regions_view: Map<nat, Set<MemoryRegion>>,
    zid: nat,
    region: MemoryRegion,
) -> bool {
    &&& zid != root_zone_id()
    &&& region_in_enclave_memory(region)
    &&& forall|other_zid: nat, old_region: MemoryRegion|
        epc_regions_view.contains_key(other_zid) && other_zid != root_zone_id()
            && #[trigger] epc_regions_view[other_zid].contains(old_region)
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

tokenized_state_machine! {
    HyperEnclaveSpec {
        fields {
            #[sharding(variable)]
            pub zone_ids: Set<nat>,

            #[sharding(map)]
            pub zones: Map<nat, GhostZone>,

            /// Conservative per-zone EPC-region cache used by serialized
            /// runtime overlap checks. An entry may contain regions that have
            /// since been removed, but never omits a live enclave region.
            #[sharding(variable)]
            pub epc_regions_view: Map<nat, Set<MemoryRegion>>,
        }

        #[invariant]
        pub fn inv_zone_ids(&self) -> bool {
            self.zones.dom() == self.zone_ids
        }

        #[invariant]
        pub fn inv_epc_regions_view_covers_live_regions(&self) -> bool {
            &&& self.epc_regions_view.dom() == self.zone_ids
            &&& forall|zid: nat| #[trigger]
                self.zones.contains_key(zid) && zid != root_zone_id() ==> self.zones[zid]
                    .cpu_mem_set.regions.subset_of(self.epc_regions_view[zid])
        }

        /// Per-zone class policy.  The normal world may map normal pages and root DMA
        /// pages.  An enclave may map EPC pages on the CPU side and has no IOMMU
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
                            ==> region_in_enclave_memory(r)
                    &&& self.zones[zid].iommu_mem_set.empty()
                }
            }
        }

        /// Dynamic exclusivity invariant for enclave physical mappings.
        #[invariant]
        pub fn inv_enclave_regions_pairwise_disjoint(&self) -> bool {
            forall|zid1: nat, zid2: nat, r1: MemoryRegion, r2: MemoryRegion|
                self.zones.contains_key(zid1) && self.zones.contains_key(zid2)
                    && zid1 != root_zone_id() && zid2 != root_zone_id()
                    && #[trigger] self.zones[zid1].cpu_mem_set.regions.contains(r1)
                    && #[trigger] self.zones[zid2].cpu_mem_set.regions.contains(r2)
                    && (zid1 != zid2 || r1 != r2)
                    ==> !r1.spec_overlaps_pmem(r2)
        }

        init! {
            initialize() {
                init zone_ids = Set::empty();
                init zones = Map::empty();
                init epc_regions_view = Map::empty();
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
                update epc_regions_view = pre.epc_regions_view.insert(zid, Set::empty());
            }
        }

        transition! {
            remove_zone(zid: nat) {
                remove zones -= [zid => let zone];
                require(zone.cpu_mem_set.empty());
                require(zone.iommu_mem_set.empty());
                update zone_ids = pre.zone_ids.remove(zid);
                update epc_regions_view = pre.epc_regions_view.remove(zid);
            }
        }

        /// Refresh one entry of the conservative global cache from its
        /// map-sharded zone token. This is a ghost-only operation used by the
        /// serialized EPC insertion scan.
        transition! {
            synchronize_epc_regions_view(zid: nat) {
                remove zones -= [zid => let zone];
                update epc_regions_view = pre.epc_regions_view.insert(
                    zid,
                    zone.cpu_mem_set.regions,
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

        /// Dynamically assign an EPC region to one enclave.
        transition! {
            cpu_insert_epc_region(zid: nat, region: MemoryRegion) {
                remove zones -= [zid => let zone];
                require(region.spec_valid());
                require(region_in_epc_memory(region));
                require(enclave_insert_allowed(pre.epc_regions_view, zid, region));
                require(!zone.cpu_mem_set.regions.contains(region));
                require(!zone.cpu_mem_set.overlaps_vmem(region));
                add zones += [zid => zone.cpu_insert_region(region)];
                update epc_regions_view = pre.epc_regions_view.insert(
                    zid,
                    zone.cpu_insert_region(region).cpu_mem_set.regions,
                );
            }
        }

        transition! {
            cpu_remove_region(zid: nat, region: MemoryRegion) {
                remove zones -= [zid => let zone];
                require(zone.cpu_mem_set.regions.contains(region));
                add zones += [zid => zone.cpu_remove_region(region)];
            }
        }

        /// Tear down all CPU mappings of one enclave before removing its zone.
        transition! {
            cpu_clear_enclave_regions(zid: nat) {
                remove zones -= [zid => let zone];
                require(zid != root_zone_id());
                add zones += [zid => zone.cpu_clear()];
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

        // Draft proof boundary: these obligations are intentionally visible as
        // admits.  Replacing them with inductive proofs is the first production
        // task; the later software/machine refinement is a separate layer.
        #[inductive(initialize)]
        fn initialize_inductive(post: Self) {
            admit();
        }

        #[inductive(add_zone)]
        fn add_zone_inductive(pre: Self, post: Self, zid: nat) {
            admit();
        }

        #[inductive(remove_zone)]
        fn remove_zone_inductive(pre: Self, post: Self, zid: nat) {
            admit();
        }

        #[inductive(synchronize_epc_regions_view)]
        fn synchronize_epc_regions_view_inductive(pre: Self, post: Self, zid: nat) {
            assert(pre.zones.contains_key(zid));
            assert(pre.zone_ids.contains(zid));
            assert(pre.epc_regions_view.contains_key(zid));
            assert(post.zone_ids == pre.zone_ids);
            assert(post.zones == pre.zones);
            assert(post.epc_regions_view == pre.epc_regions_view.insert(
                zid,
                pre.zones[zid].cpu_mem_set.regions,
            ));
            assert(post.epc_regions_view.dom() =~= pre.epc_regions_view.dom());
        }

        #[inductive(cpu_insert_normal_region)]
        fn cpu_insert_normal_region_inductive(
            pre: Self,
            post: Self,
            region: MemoryRegion,
        ) {
            admit();
        }

        #[inductive(cpu_insert_epc_region)]
        fn cpu_insert_epc_region_inductive(
            pre: Self,
            post: Self,
            zid: nat,
            region: MemoryRegion,
        ) {
            admit();
        }

        #[inductive(cpu_remove_region)]
        fn cpu_remove_region_inductive(
            pre: Self,
            post: Self,
            zid: nat,
            region: MemoryRegion,
        ) {
            admit();
        }

        #[inductive(cpu_clear_enclave_regions)]
        fn cpu_clear_enclave_regions_inductive(pre: Self, post: Self, zid: nat) {
            admit();
        }

        #[inductive(iommu_insert_region)]
        fn iommu_insert_region_inductive(
            pre: Self,
            post: Self,
            region: MemoryRegion,
        ) {
            admit();
        }

        #[inductive(iommu_remove_region)]
        fn iommu_remove_region_inductive(
            pre: Self,
            post: Self,
            region: MemoryRegion,
        ) {
            admit();
        }

        #[inductive(iommu_clear_regions)]
        fn iommu_clear_regions_inductive(pre: Self, post: Self) {
            admit();
        }
    }
}

pub type HyperEnclaveSpecInstance = HyperEnclaveSpec::Instance;

pub type HyperEnclaveZoneIdsToken = HyperEnclaveSpec::zone_ids;

pub type HyperEnclaveZoneToken = HyperEnclaveSpec::zones;

pub type HyperEnclaveEpcRegionsViewToken = HyperEnclaveSpec::epc_regions_view;

} // verus!
