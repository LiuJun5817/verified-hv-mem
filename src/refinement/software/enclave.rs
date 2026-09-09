//! `SoftwareView` projection and transition refinement for `EnclaveSpec`.
use vstd::prelude::*;

verus! {

use super::*;
use crate::address::addr::SpecVAddr;
use crate::address::frame::SpecFrame;
use crate::address::region::MemoryRegion;
use crate::constants::*;
use crate::hv_mem::spec::enclave::*;
use crate::hv_mem::spec::GhostZone;
use crate::memory_set::SpecMemorySet;
use crate::model::convert::*;
use crate::model::software::*;
use crate::model::software::proof::*;
use crate::model::types::{GuestPage, PhysPage, S2Entry, VmId, VmPageKey};

// ---------------------------------------------------------------------------
// Enclave-policy page classifications and projections
// ---------------------------------------------------------------------------
/// Combines every live zone's CPU entries into the policy-neutral S2 map.
pub open spec fn state_s2_map(state: EnclaveSpec::State) -> Map<VmPageKey, S2Entry> {
    zones_s2_map(state.zone_ids, state.zones)
}

/// Combines every live zone's IOMMU entries into the policy-neutral IOMMU map.
/// `EnclaveSpec`'s class invariant makes every non-root contribution empty.
pub open spec fn state_iommu_s2_map(state: EnclaveSpec::State) -> Map<VmPageKey, S2Entry> {
    zones_iommu_s2_map(state.zone_ids, state.zones)
}

/// Physical pages in the exact per-enclave Shared-region projection.
pub open spec fn state_s2_shared_pages(state: EnclaveSpec::State) -> Set<PhysPage> {
    Set::new(
        |page: PhysPage|
            exists|zid: nat, region: MemoryRegion|
                #![trigger state.shared_regions[zid].contains(region)]
                state.zone_ids.contains(zid) && state.shared_regions.contains_key(zid)
                    && state.shared_regions[zid].contains(region) && region_pages(region).contains(
                    page,
                ),
    )
}

/// Per-VM S2-Private pages. A mapped page is Private exactly while it is not
/// present in `EnclaveSpec`'s exact dynamic Shared projection.
pub open spec fn state_s2_private_pages(state: EnclaveSpec::State) -> Map<
    VmId,
    Set<PhysPage>,
> {
    Map::new(
        |vm: VmId| state.zone_ids.contains(vm.0),
        |vm: VmId|
            zone_cpu_mapped_pages(state.zones[vm.0]).difference(state_s2_shared_pages(state)),
    )
}

/// Per-VM IOMMU-Private pages. Only the root entry can be nonempty under the
/// `EnclaveSpec` class invariant.
pub open spec fn state_iommu_private_pages(state: EnclaveSpec::State) -> Map<
    VmId,
    Set<PhysPage>,
> {
    Map::new(
        |vm: VmId| state.zone_ids.contains(vm.0),
        |vm: VmId| zone_iommu_mapped_pages(state.zones[vm.0]),
    )
}

/// The current `EnclaveSpec` profile has no IOMMU-Shared mappings.
pub open spec fn state_iommu_shared_pages(_state: EnclaveSpec::State) -> Set<PhysPage> {
    Set::empty()
}

/// `EnclaveSpec` state equipped with its policy-neutral [`SoftwareView`].
pub ghost struct EnclaveSoftwareSpec {
    pub state: EnclaveSpec::State,
}

impl EnclaveSoftwareSpec {
    pub open spec fn view(&self) -> SoftwareView {
        SoftwareView {
            all_vms: Set::new(|vm: VmId| self.state.zone_ids.contains(vm.0)),
            s2_private_pages: state_s2_private_pages(self.state),
            s2_shared_pages: state_s2_shared_pages(self.state),
            s2_map: state_s2_map(self.state),
            iommu_private_pages: state_iommu_private_pages(self.state),
            iommu_shared_pages: state_iommu_shared_pages(self.state),
            iommu_s2_map: state_iommu_s2_map(self.state),
        }
    }
}

// ---------------------------------------------------------------------------
// Projection facts
// ---------------------------------------------------------------------------
/// The common refinement geometry and the enclave policy's geometry denote
/// the same physical pages.
proof fn lemma_region_pages_match_enclave(region: MemoryRegion)
    ensures
        region_pages(region) == enclave_region_phys_pages(region),
{
    assert forall|page: PhysPage|
        region_pages(region).contains(page) <==> enclave_region_phys_pages(region).contains(page) by {
        if region_pages(region).contains(page) {
            let i = choose|i: nat|
                0 <= i < region.pages && crate::hv_mem::spec::budget::region_phys_page(region, i)
                    == page;
            assert(crate::hv_mem::spec::budget::region_phys_page(region, i) == enclave_region_phys_page(
                region,
                i,
            ));
        }
        if enclave_region_phys_pages(region).contains(page) {
            let i = choose|i: nat| 0 <= i < region.pages && enclave_region_phys_page(region, i) == page;
            assert(crate::hv_mem::spec::budget::region_phys_page(region, i) == enclave_region_phys_page(
                region,
                i,
            ));
        }
    }
}

/// Every page of an installed non-root normal-memory region is in the exact
/// dynamic Shared projection.
proof fn lemma_nonroot_normal_region_page_is_shared(
    spec: EnclaveSoftwareSpec,
    zid: nat,
    region: MemoryRegion,
    page: PhysPage,
)
    requires
        spec.state.invariant(),
        spec.state.zones.contains_key(zid),
        zid != root_zone_id(),
        spec.state.zones[zid].cpu_mem_set.regions.contains(region),
        region_in_normal_memory(region),
        region_pages(region).contains(page),
    ensures
        state_s2_shared_pages(spec.state).contains(page),
{
    assert(spec.state.inv_zone_ids());
    assert(spec.state.inv_shared_regions_exact());
    assert(spec.state.shared_regions.contains_key(zid));
    assert(spec.state.shared_regions[zid] == live_shared_regions(zid, spec.state.zones[zid]));
    assert(live_shared_regions(zid, spec.state.zones[zid]).contains(region));
    assert(spec.state.shared_regions[zid].contains(region));
}

/// Recover the live non-root normal-memory region represented by a Shared
/// page.  This hides the exact `shared_regions` cache from later refinement
/// arguments.
proof fn lemma_shared_page_has_normal_region(
    spec: EnclaveSoftwareSpec,
    page: PhysPage,
) -> (witness: (nat, MemoryRegion))
    requires
        spec.state.invariant(),
        spec.view().s2_shared_pages.contains(page),
    ensures
        witness.0 != root_zone_id(),
        spec.state.zones.contains_key(witness.0),
        spec.state.zones[witness.0].cpu_mem_set.regions.contains(witness.1),
        region_in_normal_memory(witness.1),
        region_pages(witness.1).contains(page),
{
    let (zid, region) = choose|zid: nat, region: MemoryRegion|
        #![trigger spec.state.shared_regions[zid].contains(region)]
        spec.state.zone_ids.contains(zid)
            && spec.state.shared_regions.contains_key(zid)
            && spec.state.shared_regions[zid].contains(region)
            && region_pages(region).contains(page);
    assert(spec.state.zones.contains_key(zid));
    assert(spec.state.shared_regions[zid]
        == live_shared_regions(zid, spec.state.zones[zid]));
    (zid, region)
}

/// Every Shared page has a concrete non-root CPU mapping witness.
proof fn lemma_shared_page_has_nonroot_entry(
    spec: EnclaveSoftwareSpec,
    page: PhysPage,
) -> (key: VmPageKey)
    requires
        spec.state.invariant(),
        spec.view().s2_shared_pages.contains(page),
    ensures
        spec.view().s2_map.contains_key(key),
        key.vm != VmId(root_zone_id()),
        spec.view().s2_map[key].page == page,
{
    let (zid, region) = lemma_shared_page_has_normal_region(spec, page);
    let i = choose|i: nat| 0 <= i < region.pages && region_phys_page(region, i) == page;
    let key = VmPageKey::new(VmId(zid), region_guest_page(region, i));
    lemma_region_to_abstract_entries(zid, region);
    lemma_region_in_memory_set_maps_entries(zid, spec.state.zones[zid].cpu_mem_set, region);
    lemma_region_phys_page_linear(region, i);
    key
}

/// A non-root mapped page outside the Shared projection is backed by an
/// enclave-private EPC or GPT-backing region.
proof fn lemma_nonroot_unshared_mapped_page_has_private_region(
    spec: EnclaveSoftwareSpec,
    zid: nat,
    page: PhysPage,
)
    requires
        spec.state.invariant(),
        spec.state.zones.contains_key(zid),
        zid != root_zone_id(),
        zone_cpu_mapped_pages(spec.state.zones[zid]).contains(page),
        !state_s2_shared_pages(spec.state).contains(page),
    ensures
        exists|region: MemoryRegion| #[trigger]
            spec.state.zones[zid].cpu_mem_set.regions.contains(region) && region_pages(
                region,
            ).contains(page) && region_in_enclave_memory(zid, region),
{
    assert(spec.state.inv_class_policy());
    let mem_set = spec.state.zones[zid].cpu_mem_set;
    assert(mem_set.wf());
    lemma_memory_set_mapped_page_has_region(mem_set, page);
    let region = choose|region: MemoryRegion| #[trigger]
        mem_set.regions.contains(region) && region_pages(region).contains(page);
    assert(region_in_enclave_memory(zid, region) || region_in_normal_memory(region));
    if region_in_normal_memory(region) {
        lemma_nonroot_normal_region_page_is_shared(spec, zid, region, page);
    }
}

/// Normal-world and enclave-private regions cannot contain the same physical
/// page, even when they are different concrete regions.
proof fn lemma_normal_and_enclave_page_disjoint(
    normal_region: MemoryRegion,
    enclave_region: MemoryRegion,
    zid: nat,
    page: PhysPage,
)
    requires
        region_in_normal_memory(normal_region),
        region_in_enclave_memory(zid, enclave_region),
        region_pages(normal_region).contains(page),
        region_pages(enclave_region).contains(page),
    ensures
        false,
{
    lemma_region_pages_match_enclave(normal_region);
    lemma_region_pages_match_enclave(enclave_region);
    assert(normal_memory().contains(page));
    memory_classes_pairwise_disjoint();
    if region_in_epc_memory(enclave_region) {
        assert(epc_memory().contains(page));
    } else {
        assert(region_in_enclave_gpt_backing_frames(zid, enclave_region));
        assert(enclave_gpt_backing_frames(zid).contains(page));
        enclave_gpt_backing_frames_are_allocator_memory();
        assert(allocator_pool().contains(page));
    }
}

/// Every invariant `EnclaveSpec` state projects to a well-formed SoftwareView.
pub proof fn lemma_enclave_projection_wf(spec: EnclaveSoftwareSpec)
    requires
        spec.state.invariant(),
    ensures
        spec.view().wf(),
{
    let sw = spec.view();
    assert(spec.state.inv_zone_ids());
    assert(spec.state.inv_shared_regions_exact());
    assert(spec.state.inv_class_policy());
    assert(spec.state.inv_enclave_regions_cross_zone_disjoint());

    assert(sw.s2_private_pages.dom() =~= sw.all_vms);
    assert forall|vm1: VmId, vm2: VmId| #[trigger]
        sw.all_vms.contains(vm1) && #[trigger] sw.all_vms.contains(vm2) && vm1
            != vm2 implies forall|page: PhysPage| #[trigger]
        sw.s2_private_pages[vm1].contains(page) ==> !sw.s2_private_pages[vm2].contains(page) by {
        assert forall|page: PhysPage| #[trigger]
            sw.s2_private_pages[vm1].contains(page) implies !sw.s2_private_pages[vm2].contains(
            page,
        ) by {
            if sw.s2_private_pages[vm2].contains(page) {
                let zid1 = vm1.0;
                let zid2 = vm2.0;
                assert(zid1 != zid2);
                assert(spec.state.zones.contains_key(zid1));
                assert(spec.state.zones.contains_key(zid2));
                assert(zone_cpu_mapped_pages(spec.state.zones[zid1]).contains(page));
                assert(zone_cpu_mapped_pages(spec.state.zones[zid2]).contains(page));
                assert(!state_s2_shared_pages(spec.state).contains(page));

                if zid1 != root_zone_id() && zid2 != root_zone_id() {
                    lemma_nonroot_unshared_mapped_page_has_private_region(spec, zid1, page);
                    lemma_nonroot_unshared_mapped_page_has_private_region(spec, zid2, page);
                    let r1 = choose|region: MemoryRegion| #[trigger]
                        spec.state.zones[zid1].cpu_mem_set.regions.contains(region) && region_pages(
                            region,
                        ).contains(page) && region_in_enclave_memory(zid1, region);
                    let r2 = choose|region: MemoryRegion| #[trigger]
                        spec.state.zones[zid2].cpu_mem_set.regions.contains(region) && region_pages(
                            region,
                        ).contains(page) && region_in_enclave_memory(zid2, region);
                    assert(r1.spec_valid());
                    assert(r2.spec_valid());
                    lemma_shared_page_implies_pmem_overlap(r1, r2, page);
                    assert(!r1.spec_overlaps_pmem(r2));
                } else if zid1 == root_zone_id() {
                    let root_set = spec.state.zones[zid1].cpu_mem_set;
                    assert(root_set.wf());
                    lemma_memory_set_mapped_page_has_region(root_set, page);
                    let root_region = choose|region: MemoryRegion| #[trigger]
                        root_set.regions.contains(region) && region_pages(region).contains(page);
                    assert(region_in_normal_memory(root_region));
                    lemma_nonroot_unshared_mapped_page_has_private_region(spec, zid2, page);
                    let enclave_region = choose|region: MemoryRegion| #[trigger]
                        spec.state.zones[zid2].cpu_mem_set.regions.contains(region) && region_pages(
                            region,
                        ).contains(page) && region_in_enclave_memory(zid2, region);
                    lemma_normal_and_enclave_page_disjoint(root_region, enclave_region, zid2, page);
                } else {
                    let root_set = spec.state.zones[zid2].cpu_mem_set;
                    assert(root_set.wf());
                    lemma_memory_set_mapped_page_has_region(root_set, page);
                    let root_region = choose|region: MemoryRegion| #[trigger]
                        root_set.regions.contains(region) && region_pages(region).contains(page);
                    assert(region_in_normal_memory(root_region));
                    lemma_nonroot_unshared_mapped_page_has_private_region(spec, zid1, page);
                    let enclave_region = choose|region: MemoryRegion| #[trigger]
                        spec.state.zones[zid1].cpu_mem_set.regions.contains(region) && region_pages(
                            region,
                        ).contains(page) && region_in_enclave_memory(zid1, region);
                    lemma_normal_and_enclave_page_disjoint(root_region, enclave_region, zid1, page);
                }
            }
        }
    }
    assert(forall|vm: VmId| #[trigger]
        sw.all_vms.contains(vm) ==> forall|page: PhysPage| #[trigger]
            sw.s2_private_pages[vm].contains(page) ==> !sw.s2_shared_pages.contains(page));
    assert(sw.s2_classification_wf());

    assert forall|key: VmPageKey| #[trigger] sw.s2_map.contains_key(key) implies {
        &&& sw.all_vms.contains(key.vm)
        &&& sw.s2_private_or_shared(key.vm, sw.s2_map[key].page)
    } by {
        let zid = key.vm.0;
        let page = sw.s2_map[key].page;
        assert(spec.state.zone_ids.contains(zid));
        assert(spec.state.zones.contains_key(zid));
        assert(zone_s2_entries(zid, spec.state.zones[zid]).contains_key(key));
        assert(memory_set_mapped_pages(spec.state.zones[zid].cpu_mem_set).contains(page));
        if !sw.s2_shared_pages.contains(page) {
            assert(sw.s2_private_pages[key.vm].contains(page));
        }
    }
    assert(sw.translation_wf());

    assert(sw.iommu_private_pages.dom() =~= sw.all_vms);
    assert forall|vm1: VmId, vm2: VmId| #[trigger]
        sw.all_vms.contains(vm1) && #[trigger] sw.all_vms.contains(vm2) && vm1
            != vm2 implies forall|page: PhysPage| #[trigger]
        sw.iommu_private_pages[vm1].contains(page) ==> !sw.iommu_private_pages[vm2].contains(
            page,
        ) by {
        if vm1.0 != root_zone_id() {
            assert(spec.state.zones[vm1.0].iommu_mem_set.empty());
            assert(zone_iommu_mapped_pages(spec.state.zones[vm1.0]) =~= Set::<PhysPage>::empty());
        } else {
            assert(vm2.0 != root_zone_id());
            assert(spec.state.zones[vm2.0].iommu_mem_set.empty());
            assert(zone_iommu_mapped_pages(spec.state.zones[vm2.0]) =~= Set::<PhysPage>::empty());
        }
    }
    assert forall|vm1: VmId, vm2: VmId| #[trigger]
        sw.all_vms.contains(vm1) && #[trigger] sw.all_vms.contains(vm2) && vm1
            != vm2 implies forall|page: PhysPage| #[trigger]
        sw.iommu_private_pages[vm1].contains(page) ==> !sw.s2_private_pages[vm2].contains(page) by {
        assert forall|page: PhysPage| #[trigger]
            sw.iommu_private_pages[vm1].contains(page) implies !sw.s2_private_pages[vm2].contains(
            page,
        ) by {
            if sw.s2_private_pages[vm2].contains(page) {
                if vm1.0 != root_zone_id() {
                    assert(spec.state.zones[vm1.0].iommu_mem_set.empty());
                    assert(zone_iommu_mapped_pages(spec.state.zones[vm1.0]) =~= Set::<
                        PhysPage,
                    >::empty());
                } else {
                    assert(vm2.0 != root_zone_id());
                    let iommu_set = spec.state.zones[root_zone_id()].iommu_mem_set;
                    assert(iommu_set.wf());
                    lemma_memory_set_mapped_page_has_region(iommu_set, page);
                    let normal_region = choose|region: MemoryRegion| #[trigger]
                        iommu_set.regions.contains(region) && region_pages(region).contains(page);
                    assert(region_in_dma_memory(normal_region));
                    lemma_region_pages_match_enclave(normal_region);
                    dma_memory_is_normal_memory();
                    assert(region_in_normal_memory(normal_region));

                    assert(!state_s2_shared_pages(spec.state).contains(page));
                    lemma_nonroot_unshared_mapped_page_has_private_region(spec, vm2.0, page);
                    let enclave_region = choose|region: MemoryRegion| #[trigger]
                        spec.state.zones[vm2.0].cpu_mem_set.regions.contains(region)
                            && region_pages(region).contains(page) && region_in_enclave_memory(
                            vm2.0,
                            region,
                        );
                    lemma_normal_and_enclave_page_disjoint(
                        normal_region,
                        enclave_region,
                        vm2.0,
                        page,
                    );
                }
            }
        }
    }
    assert(forall|vm: VmId| #[trigger]
        sw.all_vms.contains(vm) ==> forall|page: PhysPage| #[trigger]
            sw.iommu_private_pages[vm].contains(page) ==> !sw.iommu_shared_pages.contains(page));
    assert(forall|vm: VmId| #[trigger]
        sw.all_vms.contains(vm) ==> forall|page: PhysPage| #[trigger]
            sw.s2_private_pages[vm].contains(page) ==> !sw.iommu_shared_pages.contains(page));
    assert(sw.iommu_classification_wf());

    assert forall|key: VmPageKey| #[trigger] sw.iommu_s2_map.contains_key(key) implies {
        &&& sw.all_vms.contains(key.vm)
        &&& sw.iommu_private_pages.contains_key(key.vm)
        &&& (sw.iommu_private_pages[key.vm].contains(sw.iommu_s2_map[key].page)
            || sw.iommu_shared_pages.contains(sw.iommu_s2_map[key].page))
    } by {
        let zid = key.vm.0;
        let page = sw.iommu_s2_map[key].page;
        assert(spec.state.zone_ids.contains(zid));
        assert(spec.state.zones.contains_key(zid));
        assert(zone_iommu_s2_entries(zid, spec.state.zones[zid]).contains_key(key));
        assert(memory_set_mapped_pages(spec.state.zones[zid].iommu_mem_set).contains(page));
        assert(sw.iommu_private_pages[key.vm].contains(page));
    }
    assert(sw.iommu_translation_wf());
    assert(sw.iommu_wf());
    assert(sw.wf());
}

proof fn lemma_cpu_mapped_page_has_entry(spec: EnclaveSoftwareSpec, zid: nat, page: PhysPage)
    requires
        spec.state.invariant(),
        spec.state.zones.contains_key(zid),
        zone_cpu_mapped_pages(spec.state.zones[zid]).contains(page),
    ensures
        exists|key: VmPageKey| #[trigger]
            spec.view().s2_map.contains_key(key) && key.vm == VmId(zid)
                && spec.view().s2_map[key].page == page,
{
    let mem_set = spec.state.zones[zid].cpu_mem_set;
    assert(spec.state.inv_class_policy());
    lemma_memory_set_mapped_page_has_region(mem_set, page);
    let region = choose|region: MemoryRegion| #[trigger]
        mem_set.regions.contains(region) && region_pages(region).contains(page);
    let i = choose|i: nat| 0 <= i < region.pages && region_phys_page(region, i) == page;
    let key = VmPageKey::new(VmId(zid), region_guest_page(region, i));
    lemma_region_to_abstract_entries(zid, region);
    lemma_region_in_memory_set_maps_entries(zid, mem_set, region);
    assert(region_to_abstract(zid, region).entries().contains_key(key));
    assert(region_to_abstract(zid, region).entries()[key].page == page) by {
        lemma_region_phys_page_linear(region, i);
    }
    assert(spec.view().s2_map.contains_key(key));
    assert(spec.view().s2_map[key].page == page);
}

proof fn lemma_cpu_entry_maps_page(spec: EnclaveSoftwareSpec, key: VmPageKey)
    requires
        spec.state.invariant(),
        spec.view().s2_map.contains_key(key),
    ensures
        zone_cpu_mapped_pages(spec.state.zones[key.vm.0]).contains(spec.view().s2_map[key].page),
{
    assert(spec.state.zones.contains_key(key.vm.0));
    let vaddr = vaddr_of_gpa(key.gpa);
    let mem_set = spec.state.zones[key.vm.0].cpu_mem_set;
    assert(mem_set.mappings.contains_key(vaddr));
    let frame = mem_set.mappings[vaddr];
    assert(frame_phys_page(frame) == spec.view().s2_map[key].page);
    assert(exists|address: SpecVAddr| #[trigger]
        mem_set.mappings.contains_key(address) && frame_phys_page(mem_set.mappings[address])
            == spec.view().s2_map[key].page) by {
        let address = vaddr;
    }
}

// ---------------------------------------------------------------------------
// Abstract one-page and region-trace helpers
// ---------------------------------------------------------------------------
pub open spec fn region_page(region: Region, i: nat) -> Region {
    Region {
        vm: region.vm,
        gpa_base: region.gpa_base + i,
        phys_base: region.phys_base + i,
        count: 1,
        access: region.access,
    }
}

pub open spec fn region_tail(region: Region) -> Region {
    Region {
        vm: region.vm,
        gpa_base: region.gpa_base + 1,
        phys_base: region.phys_base + 1,
        count: (region.count - 1) as nat,
        access: region.access,
    }
}

proof fn lemma_region_head_tail(region: Region)
    requires
        region.count > 1,
    ensures
        region_page(region, 0).wf(),
        region_tail(region).wf(),
        region.pages() =~= region_page(region, 0).pages().union(region_tail(region).pages()),
        region.entries() =~= region_page(region, 0).entries().union_prefer_right(
            region_tail(region).entries(),
        ),
        region_page(region, 0).pages().disjoint(region_tail(region).pages()),
        region_page(region, 0).entries().dom().disjoint(region_tail(region).entries().dom()),
{
    let head = region_page(region, 0);
    let tail = region_tail(region);
    assert(forall|page: PhysPage| #[trigger]
        region.pages().contains(page) <==> head.pages().union(tail.pages()).contains(page));
    assert(forall|key: VmPageKey| #[trigger]
        region.entries().contains_key(key) <==> head.entries().union_prefer_right(
            tail.entries(),
        ).contains_key(key));
    assert(forall|key: VmPageKey|
        #![trigger region.entries()[key]]
        #![trigger head.entries().union_prefer_right(tail.entries())[key]]
        region.entries().contains_key(key) ==> region.entries()[key]
            == head.entries().union_prefer_right(tail.entries())[key]);
}

proof fn lemma_single_page_region(region: Region)
    requires
        region.count == 1,
    ensures
        region == region_page(region, 0),
        region.pages() == Set::new(|page: PhysPage| page == region.phys_page(0)),
        region.entries().dom() == Set::new(
            |key: VmPageKey| key == VmPageKey::new(region.vm, region.guest_page(0)),
        ),
        forall|map: Map<VmPageKey, S2Entry>| #[trigger]
            map.union_prefer_right(region.entries()) =~= map.insert(
                VmPageKey::new(region.vm, region.guest_page(0)),
                region.entries()[VmPageKey::new(region.vm, region.guest_page(0))],
            ),
{
    assert(forall|page: PhysPage| #[trigger]
        region.pages().contains(page) <==> page == region.phys_page(0));
    assert(forall|key: VmPageKey| #[trigger]
        region.entries().contains_key(key) <==> key == VmPageKey::new(
            region.vm,
            region.guest_page(0),
        ));
    let only_key = VmPageKey::new(region.vm, region.guest_page(0));
    assert forall|map: Map<VmPageKey, S2Entry>| #[trigger]
        map.union_prefer_right(region.entries()) =~= map.insert(
            only_key,
            region.entries()[only_key],
        ) by {
        assert(forall|key: VmPageKey| #[trigger]
            map.union_prefer_right(region.entries()).contains_key(key) <==> map.insert(
                only_key,
                region.entries()[only_key],
            ).contains_key(key));
        assert(forall|key: VmPageKey|
            #![trigger map.union_prefer_right(region.entries())[key]]
            #![trigger map.insert(only_key, region.entries()[only_key])[key]]
            map.union_prefer_right(region.entries()).contains_key(key) ==> map.union_prefer_right(
                region.entries(),
            )[key] == map.insert(only_key, region.entries()[only_key])[key]);
    }
}

proof fn lemma_abstract_region_entry_targets_page(region: Region, key: VmPageKey)
    requires
        region.entries().contains_key(key),
    ensures
        region.pages().contains(region.entries()[key].page),
{
}

/// Insert one root mapping. Existing root-Private aliases are handled by a
/// temporary Private-to-Shared transfer, while already Shared pages stay
/// Shared and previously unmapped pages become root-Private.
proof fn lemma_root_insert_one(pre: SoftwareView, region: Region) -> (result: (
    SoftwareView,
    Seq<SoftwareOp>,
))
    requires
        pre.wf(),
        region.wf(),
        region.count == 1,
        region.vm == VmId(root_zone_id()),
        pre.all_vms.contains(region.vm),
        forall|key: VmPageKey| #[trigger]
            region.entries().contains_key(key) ==> !pre.s2_map.contains_key(key),
        forall|page: PhysPage, vm: VmId| #[trigger]
            region.pages().contains(page) && #[trigger] pre.all_vms.contains(vm) && vm != region.vm
                ==> !pre.s2_private_pages[vm].contains(page),
        forall|page: PhysPage| #[trigger]
            region.pages().contains(page) && pre.s2_private_pages[region.vm].contains(page)
                ==> exists|key: VmPageKey| #[trigger]
                pre.s2_map.contains_key(key) && key.vm == region.vm && pre.s2_map[key].page == page,
        forall|page: PhysPage, vm: VmId| #[trigger]
            region.pages().contains(page) && #[trigger] pre.all_vms.contains(vm) && vm != region.vm
                ==> !pre.iommu_private_pages[vm].contains(page),
        forall|page: PhysPage| #[trigger]
            region.pages().contains(page) ==> !pre.iommu_shared_pages.contains(page),
    ensures
        result.0.all_vms == pre.all_vms,
        result.0.s2_private_pages =~= pre.s2_private_pages.insert(
            region.vm,
            pre.s2_private_pages[region.vm].union(region.pages().difference(pre.s2_shared_pages)),
        ),
        result.0.s2_shared_pages == pre.s2_shared_pages,
        result.0.s2_map =~= pre.s2_map.union_prefer_right(region.entries()),
        result.0.iommu_private_pages == pre.iommu_private_pages,
        result.0.iommu_shared_pages == pre.iommu_shared_pages,
        result.0.iommu_s2_map == pre.iommu_s2_map,
        result.0.wf(),
        run_software_ops(pre, result.0, result.1),
{
    lemma_single_page_region(region);
    let page = region.phys_page(0);
    let gpa = region.guest_page(0);
    let key = VmPageKey::new(region.vm, gpa);
    assert(region.pages().contains(page));
    assert(region.entries().contains_key(key));
    assert(region.entries()[key].page == page);
    assert(pre.s2_private_pages.contains_key(region.vm));
    if pre.s2_shared_pages.contains(page) {
        assert(SoftwareView::cpu_insert_shared_region_enabled(pre, region));
        let post = SoftwareView {
            s2_shared_pages: pre.s2_shared_pages.union(region.pages()),
            s2_map: pre.s2_map.union_prefer_right(region.entries()),
            ..pre
        };
        assert(SoftwareView::cpu_insert_shared_region_step(pre, post, region));
        assert(post.s2_map =~= pre.s2_map.insert(key, region.entries()[key]));
        assert(post.s2_shared_pages =~= pre.s2_shared_pages.insert(page));
        assert(SoftwareView::map_s2_shared_step(pre, post, region.vm, gpa, region.entries()[key]));
        lemma_map_s2_shared_step_preserves_wf(pre, post, region.vm, gpa, region.entries()[key]);
        assert(post.s2_shared_pages =~= pre.s2_shared_pages);
        assert(region.pages().difference(pre.s2_shared_pages) =~= Set::<PhysPage>::empty());
        assert(pre.s2_private_pages[region.vm].union(region.pages().difference(pre.s2_shared_pages))
            =~= pre.s2_private_pages[region.vm]);
        assert(post.s2_private_pages =~= pre.s2_private_pages.insert(
            region.vm,
            pre.s2_private_pages[region.vm].union(region.pages().difference(pre.s2_shared_pages)),
        ));
        let op = SoftwareOp::CpuInsertSharedRegion(region);
        assert(SoftwareView::step(pre, post, op));
        lemma_run_software_ops_single(pre, post, op);
        (post, seq![op])
    } else if pre.s2_private_pages[region.vm].contains(page) {
        let shared = SoftwareView {
            s2_private_pages: pre.s2_private_pages.insert(
                region.vm,
                pre.s2_private_pages[region.vm].remove(page),
            ),
            s2_shared_pages: pre.s2_shared_pages.insert(page),
            ..pre
        };
        assert(SoftwareView::make_s2_shared_step(pre, shared, region.vm, page));
        lemma_make_s2_shared_step_preserves_wf(pre, shared, region.vm, page);

        assert(SoftwareView::cpu_insert_shared_region_enabled(shared, region));
        let mapped = SoftwareView {
            s2_shared_pages: shared.s2_shared_pages.union(region.pages()),
            s2_map: shared.s2_map.union_prefer_right(region.entries()),
            ..shared
        };
        assert(SoftwareView::cpu_insert_shared_region_step(shared, mapped, region));
        assert(mapped.s2_map =~= shared.s2_map.insert(key, region.entries()[key]));
        assert(mapped.s2_shared_pages =~= shared.s2_shared_pages.insert(page));
        assert(SoftwareView::map_s2_shared_step(
            shared,
            mapped,
            region.vm,
            gpa,
            region.entries()[key],
        ));
        lemma_map_s2_shared_step_preserves_wf(
            shared,
            mapped,
            region.vm,
            gpa,
            region.entries()[key],
        );

        let post = SoftwareView {
            s2_private_pages: mapped.s2_private_pages.insert(
                region.vm,
                mapped.s2_private_pages[region.vm].insert(page),
            ),
            s2_shared_pages: mapped.s2_shared_pages.remove(page),
            ..mapped
        };
        assert forall|other: VmPageKey| #[trigger]
            mapped.s2_map.contains_key(other) && mapped.s2_map[other].page == page implies other.vm
            == region.vm by {
            if other != key {
                assert(pre.s2_map.contains_key(other));
                assert(pre.all_vms.contains(other.vm));
                assert(pre.s2_private_or_shared(other.vm, page));
                assert(!pre.s2_shared_pages.contains(page));
                assert(pre.s2_private_pages[other.vm].contains(page));
                if other.vm != region.vm {
                    assert(!pre.s2_private_pages[other.vm].contains(page));
                }
            }
        }
        assert forall|other: VmId| #[trigger]
            mapped.all_vms.contains(other) && other
                != region.vm implies !mapped.iommu_private_pages[other].contains(page) by {
            assert(pre.iommu_classification_wf());
            if mapped.iommu_private_pages[other].contains(page) {
                assert(!pre.s2_private_pages[region.vm].contains(page));
            }
        }
        assert(!mapped.iommu_shared_pages.contains(page)) by {
            assert(pre.iommu_classification_wf());
        }
        assert(mapped.all_vms.contains(region.vm));
        assert(mapped.s2_shared_pages.contains(page));
        assert(mapped.s2_map.contains_key(key));
        assert(mapped.s2_map[key].page == page);
        assert(exists|some: VmPageKey| #[trigger]
            mapped.s2_map.contains_key(some) && some.vm == region.vm && mapped.s2_map[some].page
                == page) by {
            let some = key;
        }
        assert(post.s2_private_pages == mapped.s2_private_pages.insert(
            region.vm,
            mapped.s2_private_pages[region.vm].insert(page),
        ));
        assert(post.s2_shared_pages == mapped.s2_shared_pages.remove(page));
        assert(SoftwareView::make_s2_private_step(mapped, post, region.vm, page));
        lemma_make_s2_private_step_preserves_wf(mapped, post, region.vm, page);
        assert(post.s2_shared_pages =~= pre.s2_shared_pages);
        assert(post.s2_private_pages =~= pre.s2_private_pages);
        assert(post.s2_map =~= pre.s2_map.union_prefer_right(region.entries()));
        assert(pre.s2_private_pages[region.vm].union(region.pages().difference(pre.s2_shared_pages))
            =~= pre.s2_private_pages[region.vm]);
        assert(pre.s2_private_pages =~= pre.s2_private_pages.insert(
            region.vm,
            pre.s2_private_pages[region.vm].union(region.pages().difference(pre.s2_shared_pages)),
        ));
        let first = SoftwareOp::MakeS2Shared(region.vm, page);
        let second = SoftwareOp::CpuInsertSharedRegion(region);
        let third = SoftwareOp::MakeS2Private(region.vm, page);
        assert(SoftwareView::step(pre, shared, first));
        assert(SoftwareView::step(shared, mapped, second));
        assert(SoftwareView::step(mapped, post, third));
        lemma_run_software_ops_single(pre, shared, first);
        lemma_run_software_ops_single(shared, mapped, second);
        lemma_run_software_ops_single(mapped, post, third);
        lemma_run_software_ops_concat(pre, shared, mapped, seq![first], seq![second]);
        assert(seq![first] + seq![second] == seq![first, second]);
        lemma_run_software_ops_concat(pre, mapped, post, seq![first, second], seq![third]);
        assert(seq![first, second] + seq![third] == seq![first, second, third]);
        (post, seq![first, second, third])
    } else {
        assert(SoftwareView::cpu_insert_private_region_enabled(pre, region));
        let post = SoftwareView {
            s2_private_pages: pre.s2_private_pages.insert(
                region.vm,
                pre.s2_private_pages[region.vm].union(region.pages()),
            ),
            s2_map: pre.s2_map.union_prefer_right(region.entries()),
            ..pre
        };
        assert(SoftwareView::cpu_insert_private_region_step(pre, post, region));
        assert(post.s2_map =~= pre.s2_map.insert(key, region.entries()[key]));
        assert(pre.s2_private_pages[region.vm].union(region.pages())
            =~= pre.s2_private_pages[region.vm].insert(page));
        assert(post.s2_private_pages =~= pre.s2_private_pages.insert(
            region.vm,
            pre.s2_private_pages[region.vm].insert(page),
        ));
        assert(SoftwareView::map_s2_private_step(pre, post, region.vm, gpa, region.entries()[key]));
        lemma_map_s2_private_step_preserves_wf(pre, post, region.vm, gpa, region.entries()[key]);
        assert(region.pages().difference(pre.s2_shared_pages) =~= region.pages());
        let op = SoftwareOp::CpuInsertPrivateRegion(region);
        assert(SoftwareView::step(pre, post, op));
        lemma_run_software_ops_single(pre, post, op);
        (post, seq![op])
    }
}

proof fn lemma_root_insert_region(pre: SoftwareView, region: Region) -> (result: (
    SoftwareView,
    Seq<SoftwareOp>,
))
    requires
        pre.wf(),
        region.wf(),
        region.vm == VmId(root_zone_id()),
        pre.all_vms.contains(region.vm),
        forall|key: VmPageKey| #[trigger]
            region.entries().contains_key(key) ==> !pre.s2_map.contains_key(key),
        forall|page: PhysPage, vm: VmId| #[trigger]
            region.pages().contains(page) && #[trigger] pre.all_vms.contains(vm) && vm != region.vm
                ==> !pre.s2_private_pages[vm].contains(page),
        forall|page: PhysPage| #[trigger]
            region.pages().contains(page) && pre.s2_private_pages[region.vm].contains(page)
                ==> exists|key: VmPageKey| #[trigger]
                pre.s2_map.contains_key(key) && key.vm == region.vm && pre.s2_map[key].page == page,
        forall|page: PhysPage, vm: VmId| #[trigger]
            region.pages().contains(page) && #[trigger] pre.all_vms.contains(vm) && vm != region.vm
                ==> !pre.iommu_private_pages[vm].contains(page),
        forall|page: PhysPage| #[trigger]
            region.pages().contains(page) ==> !pre.iommu_shared_pages.contains(page),
    ensures
        result.0.all_vms == pre.all_vms,
        result.0.s2_private_pages =~= pre.s2_private_pages.insert(
            region.vm,
            pre.s2_private_pages[region.vm].union(region.pages().difference(pre.s2_shared_pages)),
        ),
        result.0.s2_shared_pages == pre.s2_shared_pages,
        result.0.s2_map =~= pre.s2_map.union_prefer_right(region.entries()),
        result.0.iommu_private_pages == pre.iommu_private_pages,
        result.0.iommu_shared_pages == pre.iommu_shared_pages,
        result.0.iommu_s2_map == pre.iommu_s2_map,
        result.0.wf(),
        run_software_ops(pre, result.0, result.1),
    decreases region.count,
{
    if region.count == 1 {
        lemma_root_insert_one(pre, region)
    } else {
        let head = region_page(region, 0);
        let tail = region_tail(region);
        lemma_region_head_tail(region);
        assert(forall|key: VmPageKey| #[trigger]
            head.entries().contains_key(key) ==> region.entries().contains_key(key));
        assert(forall|page: PhysPage| #[trigger]
            head.pages().contains(page) ==> region.pages().contains(page));
        assert(forall|page: PhysPage| #[trigger]
            tail.pages().contains(page) ==> region.pages().contains(page));
        let first = lemma_root_insert_one(pre, head);
        let middle = first.0;
        assert forall|key: VmPageKey| #[trigger]
            tail.entries().contains_key(key) implies !middle.s2_map.contains_key(key) by {
            assert(region.entries().contains_key(key));
            assert(!pre.s2_map.contains_key(key));
            assert(!head.entries().contains_key(key));
        }
        assert forall|page: PhysPage, vm: VmId| #[trigger]
            tail.pages().contains(page) && #[trigger] middle.all_vms.contains(vm) && vm
                != tail.vm implies !middle.s2_private_pages[vm].contains(page) by {
            assert(region.pages().contains(page));
        }
        assert forall|page: PhysPage| #[trigger]
            tail.pages().contains(page) && middle.s2_private_pages[tail.vm].contains(
                page,
            ) implies exists|key: VmPageKey| #[trigger]
            middle.s2_map.contains_key(key) && key.vm == tail.vm && middle.s2_map[key].page
                == page by {
            assert(!head.pages().contains(page));
            assert(middle.s2_private_pages[tail.vm] =~= pre.s2_private_pages[region.vm].union(
                head.pages().difference(pre.s2_shared_pages),
            ));
            assert(pre.s2_private_pages[region.vm].contains(page));
            assert(exists|key: VmPageKey| #[trigger]
                pre.s2_map.contains_key(key) && key.vm == region.vm && pre.s2_map[key].page
                    == page);
            let key = choose|key: VmPageKey| #[trigger]
                pre.s2_map.contains_key(key) && key.vm == region.vm && pre.s2_map[key].page == page;
            assert(middle.s2_map.contains_key(key));
        }
        assert forall|page: PhysPage, vm: VmId| #[trigger]
            tail.pages().contains(page) && #[trigger] middle.all_vms.contains(vm) && vm
                != tail.vm implies !middle.iommu_private_pages[vm].contains(page) by {
            assert(region.pages().contains(page));
        }
        assert forall|page: PhysPage| #[trigger]
            tail.pages().contains(page) implies !middle.iommu_shared_pages.contains(page) by {
            assert(region.pages().contains(page));
        }
        let rest = lemma_root_insert_region(middle, tail);
        let post = rest.0;
        assert(post.s2_private_pages =~= pre.s2_private_pages.insert(
            region.vm,
            pre.s2_private_pages[region.vm].union(region.pages().difference(pre.s2_shared_pages)),
        )) by {
            assert(forall|page: PhysPage| #[trigger]
                head.pages().union(tail.pages()).difference(pre.s2_shared_pages).contains(page)
                    <==> head.pages().difference(pre.s2_shared_pages).union(
                    tail.pages().difference(pre.s2_shared_pages),
                ).contains(page));
            assert(pre.s2_private_pages[region.vm].union(
                head.pages().difference(pre.s2_shared_pages),
            ).union(tail.pages().difference(pre.s2_shared_pages))
                =~= pre.s2_private_pages[region.vm].union(
                region.pages().difference(pre.s2_shared_pages),
            ));
        }
        assert(post.s2_map =~= pre.s2_map.union_prefer_right(region.entries())) by {
            assert(pre.s2_map.union_prefer_right(head.entries()).union_prefer_right(tail.entries())
                =~= pre.s2_map.union_prefer_right(
                head.entries().union_prefer_right(tail.entries()),
            ));
        }
        lemma_run_software_ops_concat(pre, middle, post, first.1, rest.1);
        (post, first.1 + rest.1)
    }
}

pub open spec fn private_after_cpu_remove(pre: SoftwareView, region: Region) -> Map<
    VmId,
    Set<PhysPage>,
> {
    let post_map = pre.s2_map.remove_keys(region.entries().dom());
    private_pages_after_unmap(
        pre.s2_private_pages,
        post_map,
        region.vm,
        region.pages(),
    )
}

/// Remove one root mapping while retaining the root-Private classification if
/// another root alias survives. Shared pages remain Shared because an enclave
/// alias is required to survive the root removal.
proof fn lemma_root_remove_one(pre: SoftwareView, region: Region) -> (result: (
    SoftwareView,
    Seq<SoftwareOp>,
))
    requires
        pre.wf(),
        region.wf(),
        region.count == 1,
        region.vm == VmId(root_zone_id()),
        pre.all_vms.contains(region.vm),
        abstract_region_installed(pre.s2_map, region),
        forall|page: PhysPage| #[trigger]
            region.pages().contains(page) ==> pre.s2_shared_pages.contains(page)
                || pre.s2_private_pages[region.vm].contains(page),
        forall|page: PhysPage| #[trigger]
            region.pages().contains(page) && pre.s2_shared_pages.contains(page) ==> exists|
                key: VmPageKey,
            | #[trigger]
                pre.s2_map.remove_keys(region.entries().dom()).contains_key(key)
                    && pre.s2_map.remove_keys(region.entries().dom())[key].page == page,
    ensures
        result.0.all_vms == pre.all_vms,
        result.0.s2_private_pages =~= private_after_cpu_remove(pre, region),
        result.0.s2_shared_pages == pre.s2_shared_pages,
        result.0.s2_map =~= pre.s2_map.remove_keys(region.entries().dom()),
        result.0.iommu_private_pages == pre.iommu_private_pages,
        result.0.iommu_shared_pages == pre.iommu_shared_pages,
        result.0.iommu_s2_map == pre.iommu_s2_map,
        result.0.wf(),
        run_software_ops(pre, result.0, result.1),
{
    lemma_single_page_region(region);
    let page = region.phys_page(0);
    let gpa = region.guest_page(0);
    let key = VmPageKey::new(region.vm, gpa);
    let post_map = pre.s2_map.remove(key);
    assert(region.pages().contains(page));
    assert(region.entries().contains_key(key));
    assert(region.entries()[key].page == page);
    assert(pre.s2_map.contains_key(key));
    assert(pre.s2_map[key] == region.entries()[key]);
    assert(pre.s2_map.remove_keys(region.entries().dom()) =~= post_map);
    if pre.s2_shared_pages.contains(page) {
        assert(SoftwareView::cpu_remove_shared_region_enabled(pre, region));
        assert(exists|other: VmPageKey| #[trigger]
            post_map.contains_key(other) && post_map[other].page == page);
        let post = SoftwareView { s2_map: post_map, ..pre };
        assert(SoftwareView::cpu_remove_shared_region_step(pre, post, region));
        assert(SoftwareView::unmap_s2_shared_step(pre, post, region.vm, gpa));
        lemma_unmap_s2_shared_step_preserves_wf(pre, post, region.vm, gpa);
        assert(private_after_cpu_remove(pre, region) =~= pre.s2_private_pages) by {
            assert(!pre.s2_private_pages[region.vm].contains(page));
            assert(forall|other: PhysPage| #[trigger]
                pre.s2_private_pages[region.vm].contains(other) ==> !region.pages().contains(
                    other,
                ));
            assert(private_after_cpu_remove(pre, region)[region.vm]
                =~= pre.s2_private_pages[region.vm]);
            assert(pre.s2_private_pages.insert(region.vm, pre.s2_private_pages[region.vm])
                =~= pre.s2_private_pages);
        }
        let op = SoftwareOp::CpuRemoveSharedRegion(region);
        assert(SoftwareView::step(pre, post, op));
        lemma_run_software_ops_single(pre, post, op);
        (post, seq![op])
    } else {
        assert(pre.s2_private_pages[region.vm].contains(page));
        assert(SoftwareView::cpu_remove_private_region_enabled(pre, region));
        let post = SoftwareView {
            s2_private_pages: private_pages_after_unmap(
                pre.s2_private_pages,
                post_map,
                region.vm,
                region.pages(),
            ),
            s2_map: post_map,
            ..pre
        };
        assert(SoftwareView::cpu_remove_private_region_step(pre, post, region));
        assert(region.pages() =~= Set::<PhysPage>::empty().insert(page));
        assert(SoftwareView::unmap_s2_private_step(pre, post, region.vm, gpa, page));
        lemma_unmap_s2_private_step_preserves_wf(pre, post, region.vm, gpa, page);
        let op = SoftwareOp::CpuRemovePrivateRegion(region);
        assert(SoftwareView::step(pre, post, op));
        lemma_run_software_ops_single(pre, post, op);
        (post, seq![op])
    }
}

proof fn lemma_root_remove_region(pre: SoftwareView, region: Region) -> (result: (
    SoftwareView,
    Seq<SoftwareOp>,
))
    requires
        pre.wf(),
        region.wf(),
        region.vm == VmId(root_zone_id()),
        pre.all_vms.contains(region.vm),
        abstract_region_installed(pre.s2_map, region),
        forall|page: PhysPage| #[trigger]
            region.pages().contains(page) ==> pre.s2_shared_pages.contains(page)
                || pre.s2_private_pages[region.vm].contains(page),
        forall|page: PhysPage| #[trigger]
            region.pages().contains(page) && pre.s2_shared_pages.contains(page) ==> exists|
                key: VmPageKey,
            | #[trigger]
                pre.s2_map.remove_keys(region.entries().dom()).contains_key(key)
                    && pre.s2_map.remove_keys(region.entries().dom())[key].page == page,
    ensures
        result.0.all_vms == pre.all_vms,
        result.0.s2_private_pages =~= private_after_cpu_remove(pre, region),
        result.0.s2_shared_pages == pre.s2_shared_pages,
        result.0.s2_map =~= pre.s2_map.remove_keys(region.entries().dom()),
        result.0.iommu_private_pages == pre.iommu_private_pages,
        result.0.iommu_shared_pages == pre.iommu_shared_pages,
        result.0.iommu_s2_map == pre.iommu_s2_map,
        result.0.wf(),
        run_software_ops(pre, result.0, result.1),
    decreases region.count,
{
    if region.count == 1 {
        lemma_root_remove_one(pre, region)
    } else {
        let head = region_page(region, 0);
        let tail = region_tail(region);
        lemma_region_head_tail(region);
        assert(forall|key: VmPageKey| #[trigger]
            head.entries().contains_key(key) ==> region.entries().contains_key(key));
        assert(forall|key: VmPageKey| #[trigger]
            tail.entries().contains_key(key) ==> region.entries().contains_key(key));
        assert(forall|page: PhysPage| #[trigger]
            head.pages().contains(page) ==> region.pages().contains(page));
        assert(forall|page: PhysPage| #[trigger]
            tail.pages().contains(page) ==> region.pages().contains(page));
        assert(abstract_region_installed(pre.s2_map, head));
        assert forall|page: PhysPage| #[trigger]
            head.pages().contains(page) && pre.s2_shared_pages.contains(page) implies exists|
            key: VmPageKey,
        | #[trigger]
            pre.s2_map.remove_keys(head.entries().dom()).contains_key(key)
                && pre.s2_map.remove_keys(head.entries().dom())[key].page == page by {
            let key = choose|key: VmPageKey| #[trigger]
                pre.s2_map.remove_keys(region.entries().dom()).contains_key(key)
                    && pre.s2_map.remove_keys(region.entries().dom())[key].page == page;
            assert(pre.s2_map.remove_keys(head.entries().dom()).contains_key(key));
        }
        let first = lemma_root_remove_one(pre, head);
        let middle = first.0;
        assert(abstract_region_installed(middle.s2_map, tail)) by {
            assert forall|key: VmPageKey| #[trigger]
                tail.entries().contains_key(key) implies middle.s2_map.contains_key(key)
                && middle.s2_map[key] == tail.entries()[key] by {
                assert(!head.entries().contains_key(key));
            }
        }
        assert forall|page: PhysPage| #[trigger]
            tail.pages().contains(page) implies middle.s2_shared_pages.contains(page)
            || middle.s2_private_pages[tail.vm].contains(page) by {
            assert(!head.pages().contains(page));
            if !pre.s2_shared_pages.contains(page) {
                assert(pre.s2_private_pages[region.vm].contains(page));
                assert(middle.s2_private_pages[tail.vm] =~= Set::new(
                    |other_page: PhysPage|
                        pre.s2_private_pages[region.vm].contains(other_page) && (
                        !head.pages().contains(other_page) || exists|key: VmPageKey| #[trigger]
                            pre.s2_map.remove_keys(head.entries().dom()).contains_key(key)
                                && pre.s2_map.remove_keys(head.entries().dom())[key].page
                                == other_page),
                ));
            }
        }
        assert forall|page: PhysPage| #[trigger]
            tail.pages().contains(page) && middle.s2_shared_pages.contains(page) implies exists|
            key: VmPageKey,
        | #[trigger]
            middle.s2_map.remove_keys(tail.entries().dom()).contains_key(key)
                && middle.s2_map.remove_keys(tail.entries().dom())[key].page == page by {
            let key = choose|key: VmPageKey| #[trigger]
                pre.s2_map.remove_keys(region.entries().dom()).contains_key(key)
                    && pre.s2_map.remove_keys(region.entries().dom())[key].page == page;
            assert(middle.s2_map.remove_keys(tail.entries().dom()) =~= pre.s2_map.remove_keys(
                region.entries().dom(),
            )) by {
                assert(pre.s2_map.remove_keys(head.entries().dom()).remove_keys(
                    tail.entries().dom(),
                ) =~= pre.s2_map.remove_keys(
                    head.entries().union_prefer_right(tail.entries()).dom(),
                ));
            }
        }
        let rest = lemma_root_remove_region(middle, tail);
        let post = rest.0;
        assert(middle.s2_map.remove_keys(tail.entries().dom()) =~= pre.s2_map.remove_keys(
            region.entries().dom(),
        )) by {
            assert(pre.s2_map.remove_keys(head.entries().dom()).remove_keys(tail.entries().dom())
                =~= pre.s2_map.remove_keys(
                head.entries().union_prefer_right(tail.entries()).dom(),
            ));
        }
        assert(private_after_cpu_remove(middle, tail) =~= private_after_cpu_remove(pre, region))
            by {
            let final_map = pre.s2_map.remove_keys(region.entries().dom());
            assert forall|page: PhysPage| #[trigger]
                private_after_cpu_remove(middle, tail)[region.vm].contains(page)
                    <==> private_after_cpu_remove(pre, region)[region.vm].contains(page) by {
                let after_head = pre.s2_map.remove_keys(head.entries().dom());
                assert(middle.s2_map =~= after_head);
                assert(middle.s2_private_pages =~= private_after_cpu_remove(pre, head));
                if private_after_cpu_remove(middle, tail)[region.vm].contains(page) {
                    assert(middle.s2_private_pages[region.vm].contains(page));
                    assert(pre.s2_private_pages[region.vm].contains(page));
                    if region.pages().contains(page) {
                        if tail.pages().contains(page) {
                            assert(exists|key: VmPageKey| #[trigger]
                                middle.s2_map.remove_keys(tail.entries().dom()).contains_key(key)
                                    && middle.s2_map.remove_keys(tail.entries().dom())[key].page
                                    == page);
                        } else {
                            assert(head.pages().contains(page));
                            assert(exists|key: VmPageKey| #[trigger]
                                after_head.contains_key(key) && after_head[key].page == page);
                            let key = choose|key: VmPageKey| #[trigger]
                                after_head.contains_key(key) && after_head[key].page == page;
                            if tail.entries().contains_key(key) {
                                lemma_abstract_region_entry_targets_page(tail, key);
                                assert(tail.entries()[key] == after_head[key]);
                                assert(tail.pages().contains(page));
                            }
                            assert(final_map.contains_key(key));
                            assert(final_map[key].page == page);
                        }
                    }
                }
                if private_after_cpu_remove(pre, region)[region.vm].contains(page) {
                    assert(pre.s2_private_pages[region.vm].contains(page));
                    if head.pages().contains(page) {
                        assert(exists|key: VmPageKey| #[trigger]
                            final_map.contains_key(key) && final_map[key].page == page);
                        let key = choose|key: VmPageKey| #[trigger]
                            final_map.contains_key(key) && final_map[key].page == page;
                        assert(after_head.contains_key(key));
                        assert(after_head[key].page == page);
                    }
                    assert(private_after_cpu_remove(pre, head)[region.vm].contains(page));
                    if tail.pages().contains(page) {
                        assert(exists|key: VmPageKey| #[trigger]
                            final_map.contains_key(key) && final_map[key].page == page);
                    }
                }
            }
            assert(private_after_cpu_remove(middle, tail).dom() =~= private_after_cpu_remove(
                pre,
                region,
            ).dom());
            assert forall|vm: VmId| #[trigger]
                private_after_cpu_remove(middle, tail).contains_key(
                    vm,
                ) implies private_after_cpu_remove(middle, tail)[vm] =~= private_after_cpu_remove(
                pre,
                region,
            )[vm] by {
                if vm != region.vm {
                }
            }
        }
        assert(post.s2_private_pages =~= private_after_cpu_remove(pre, region));
        lemma_run_software_ops_concat(pre, middle, post, first.1, rest.1);
        (post, first.1 + rest.1)
    }
}

pub open spec fn private_pages_made_shared(
    pre: SoftwareView,
    owner: VmId,
    region: Region,
) -> SoftwareView {
    SoftwareView {
        s2_private_pages: pre.s2_private_pages.insert(
            owner,
            pre.s2_private_pages[owner].difference(region.pages()),
        ),
        s2_shared_pages: pre.s2_shared_pages.union(
            pre.s2_private_pages[owner].intersect(region.pages()),
        ),
        ..pre
    }
}

proof fn lemma_make_one_page_shared(pre: SoftwareView, owner: VmId, region: Region) -> (result: (
    SoftwareView,
    Seq<SoftwareOp>,
))
    requires
        pre.wf(),
        region.wf(),
        region.count == 1,
        pre.all_vms.contains(owner),
        forall|page: PhysPage, vm: VmId| #[trigger]
            region.pages().contains(page) && #[trigger] pre.all_vms.contains(vm)
                && pre.s2_private_pages[vm].contains(page) ==> vm == owner,
        forall|page: PhysPage| #[trigger]
            region.pages().contains(page) && pre.s2_private_pages[owner].contains(page) ==> exists|
                key: VmPageKey,
            | #[trigger]
                pre.s2_map.contains_key(key) && key.vm == owner && pre.s2_map[key].page == page,
    ensures
        result.0 =~= private_pages_made_shared(pre, owner, region),
        result.0.wf(),
        run_software_ops(pre, result.0, result.1),
{
    lemma_single_page_region(region);
    let page = region.phys_page(0);
    assert(region.pages().contains(page));
    if pre.s2_private_pages[owner].contains(page) {
        let post = SoftwareView {
            s2_private_pages: pre.s2_private_pages.insert(
                owner,
                pre.s2_private_pages[owner].remove(page),
            ),
            s2_shared_pages: pre.s2_shared_pages.insert(page),
            ..pre
        };
        assert(SoftwareView::make_s2_shared_step(pre, post, owner, page));
        lemma_make_s2_shared_step_preserves_wf(pre, post, owner, page);
        assert(pre.s2_private_pages[owner].difference(region.pages())
            =~= pre.s2_private_pages[owner].remove(page));
        assert(pre.s2_private_pages[owner].intersect(region.pages()) =~= Set::<
            PhysPage,
        >::empty().insert(page));
        let target = private_pages_made_shared(pre, owner, region);
        assert(post.s2_private_pages =~= target.s2_private_pages);
        assert(post.s2_shared_pages =~= target.s2_shared_pages);
        assert(post.all_vms == target.all_vms);
        assert(post.s2_map == target.s2_map);
        assert(post.iommu_private_pages == target.iommu_private_pages);
        assert(post.iommu_shared_pages == target.iommu_shared_pages);
        assert(post.iommu_s2_map == target.iommu_s2_map);
        assert(post == target);
        let op = SoftwareOp::MakeS2Shared(owner, page);
        assert(SoftwareView::step(pre, post, op));
        lemma_run_software_ops_single(pre, post, op);
        (post, seq![op])
    } else {
        assert(pre.s2_private_pages[owner].difference(region.pages())
            =~= pre.s2_private_pages[owner]);
        assert(pre.s2_private_pages[owner].intersect(region.pages()) =~= Set::<PhysPage>::empty());
        let target = private_pages_made_shared(pre, owner, region);
        assert(target.s2_private_pages =~= pre.s2_private_pages);
        assert(target.s2_shared_pages =~= pre.s2_shared_pages);
        assert(target == pre);
        (pre, Seq::empty())
    }
}

proof fn lemma_make_region_shared(pre: SoftwareView, owner: VmId, region: Region) -> (result: (
    SoftwareView,
    Seq<SoftwareOp>,
))
    requires
        pre.wf(),
        region.wf(),
        pre.all_vms.contains(owner),
        forall|page: PhysPage, vm: VmId| #[trigger]
            region.pages().contains(page) && #[trigger] pre.all_vms.contains(vm)
                && pre.s2_private_pages[vm].contains(page) ==> vm == owner,
        forall|page: PhysPage| #[trigger]
            region.pages().contains(page) && pre.s2_private_pages[owner].contains(page) ==> exists|
                key: VmPageKey,
            | #[trigger]
                pre.s2_map.contains_key(key) && key.vm == owner && pre.s2_map[key].page == page,
    ensures
        result.0 =~= private_pages_made_shared(pre, owner, region),
        result.0.wf(),
        run_software_ops(pre, result.0, result.1),
    decreases region.count,
{
    if region.count == 1 {
        lemma_make_one_page_shared(pre, owner, region)
    } else {
        let head = region_page(region, 0);
        let tail = region_tail(region);
        lemma_region_head_tail(region);
        assert(forall|page: PhysPage| #[trigger]
            head.pages().contains(page) ==> region.pages().contains(page));
        assert(forall|page: PhysPage| #[trigger]
            tail.pages().contains(page) ==> region.pages().contains(page));
        let first = lemma_make_one_page_shared(pre, owner, head);
        let middle = first.0;
        assert forall|page: PhysPage, vm: VmId| #[trigger]
            tail.pages().contains(page) && #[trigger] middle.all_vms.contains(vm)
                && middle.s2_private_pages[vm].contains(page) implies vm == owner by {
            assert(!head.pages().contains(page));
            if vm == owner {
            } else {
                assert(pre.s2_private_pages[vm].contains(page));
            }
        }
        assert forall|page: PhysPage| #[trigger]
            tail.pages().contains(page) && middle.s2_private_pages[owner].contains(
                page,
            ) implies exists|key: VmPageKey| #[trigger]
            middle.s2_map.contains_key(key) && key.vm == owner && middle.s2_map[key].page
                == page by {
            assert(!head.pages().contains(page));
            assert(pre.s2_private_pages[owner].contains(page));
            let key = choose|key: VmPageKey| #[trigger]
                pre.s2_map.contains_key(key) && key.vm == owner && pre.s2_map[key].page == page;
            assert(middle.s2_map.contains_key(key));
        }
        let rest = lemma_make_region_shared(middle, owner, tail);
        let post = rest.0;
        let lhs = private_pages_made_shared(middle, owner, tail);
        let rhs = private_pages_made_shared(pre, owner, region);
        assert(lhs.s2_private_pages =~= rhs.s2_private_pages) by {
            assert(pre.s2_private_pages[owner].difference(head.pages()).difference(tail.pages())
                =~= pre.s2_private_pages[owner].difference(region.pages()));
        }
        assert(lhs.s2_shared_pages =~= rhs.s2_shared_pages) by {
            assert(pre.s2_shared_pages.union(
                pre.s2_private_pages[owner].intersect(head.pages()),
            ).union(pre.s2_private_pages[owner].difference(head.pages()).intersect(tail.pages()))
                =~= pre.s2_shared_pages.union(
                pre.s2_private_pages[owner].intersect(region.pages()),
            ));
        }
        assert(lhs.all_vms == rhs.all_vms);
        assert(lhs.s2_map == rhs.s2_map);
        assert(lhs.iommu_private_pages == rhs.iommu_private_pages);
        assert(lhs.iommu_shared_pages == rhs.iommu_shared_pages);
        assert(lhs.iommu_s2_map == rhs.iommu_s2_map);
        assert(lhs == rhs);
        lemma_run_software_ops_concat(pre, middle, post, first.1, rest.1);
        (post, first.1 + rest.1)
    }
}

pub open spec fn shared_pages_made_private(
    pre: SoftwareView,
    owner: VmId,
    region: Region,
    target_shared: Set<PhysPage>,
) -> SoftwareView {
    SoftwareView {
        s2_private_pages: pre.s2_private_pages.insert(
            owner,
            pre.s2_private_pages[owner].union(
                pre.s2_shared_pages.difference(target_shared).intersect(region.pages()),
            ),
        ),
        s2_shared_pages: pre.s2_shared_pages.difference(region.pages().difference(target_shared)),
        ..pre
    }
}

proof fn lemma_make_one_page_private(
    pre: SoftwareView,
    owner: VmId,
    region: Region,
    target_shared: Set<PhysPage>,
) -> (result: (SoftwareView, Seq<SoftwareOp>))
    requires
        pre.wf(),
        region.wf(),
        region.count == 1,
        pre.all_vms.contains(owner),
        forall|page: PhysPage| #[trigger]
            region.pages().contains(page) && pre.s2_shared_pages.contains(page)
                && !target_shared.contains(page) ==> {
                &&& exists|key: VmPageKey| #[trigger]
                    pre.s2_map.contains_key(key) && key.vm == owner && pre.s2_map[key].page == page
                &&& forall|key: VmPageKey| #[trigger]
                    pre.s2_map.contains_key(key) && pre.s2_map[key].page == page ==> key.vm == owner
                &&& forall|other: VmId| #[trigger]
                    pre.all_vms.contains(other) && other != owner
                        ==> !pre.iommu_private_pages[other].contains(page)
                &&& !pre.iommu_shared_pages.contains(page)
            },
    ensures
        result.0 == shared_pages_made_private(pre, owner, region, target_shared),
        result.0.wf(),
        run_software_ops(pre, result.0, result.1),
{
    lemma_single_page_region(region);
    let page = region.phys_page(0);
    assert(region.pages().contains(page));
    if pre.s2_shared_pages.contains(page) && !target_shared.contains(page) {
        let post = SoftwareView {
            s2_private_pages: pre.s2_private_pages.insert(
                owner,
                pre.s2_private_pages[owner].insert(page),
            ),
            s2_shared_pages: pre.s2_shared_pages.remove(page),
            ..pre
        };
        assert(SoftwareView::make_s2_private_step(pre, post, owner, page));
        lemma_make_s2_private_step_preserves_wf(pre, post, owner, page);
        assert(pre.s2_shared_pages.difference(target_shared).intersect(region.pages()) =~= Set::<
            PhysPage,
        >::empty().insert(page));
        assert(pre.s2_private_pages[owner].union(
            pre.s2_shared_pages.difference(target_shared).intersect(region.pages()),
        ) =~= pre.s2_private_pages[owner].insert(page));
        assert(region.pages().difference(target_shared) =~= region.pages());
        assert(pre.s2_shared_pages.difference(region.pages().difference(target_shared))
            =~= pre.s2_shared_pages.remove(page));
        let target = shared_pages_made_private(pre, owner, region, target_shared);
        assert(post.s2_private_pages =~= target.s2_private_pages);
        assert(post.s2_shared_pages =~= target.s2_shared_pages);
        assert(post == target);
        let op = SoftwareOp::MakeS2Private(owner, page);
        assert(SoftwareView::step(pre, post, op));
        lemma_run_software_ops_single(pre, post, op);
        (post, seq![op])
    } else {
        assert(pre.s2_shared_pages.difference(target_shared).intersect(region.pages()) =~= Set::<
            PhysPage,
        >::empty());
        assert(pre.s2_private_pages[owner].union(
            pre.s2_shared_pages.difference(target_shared).intersect(region.pages()),
        ) =~= pre.s2_private_pages[owner]);
        assert(pre.s2_shared_pages.difference(region.pages().difference(target_shared))
            =~= pre.s2_shared_pages);
        let target = shared_pages_made_private(pre, owner, region, target_shared);
        assert(target.s2_private_pages =~= pre.s2_private_pages);
        assert(target.s2_shared_pages =~= pre.s2_shared_pages);
        assert(target == pre);
        (pre, Seq::empty())
    }
}

proof fn lemma_make_region_private(
    pre: SoftwareView,
    owner: VmId,
    region: Region,
    target_shared: Set<PhysPage>,
) -> (result: (SoftwareView, Seq<SoftwareOp>))
    requires
        pre.wf(),
        region.wf(),
        pre.all_vms.contains(owner),
        forall|page: PhysPage| #[trigger]
            region.pages().contains(page) && pre.s2_shared_pages.contains(page)
                && !target_shared.contains(page) ==> {
                &&& exists|key: VmPageKey| #[trigger]
                    pre.s2_map.contains_key(key) && key.vm == owner && pre.s2_map[key].page == page
                &&& forall|key: VmPageKey| #[trigger]
                    pre.s2_map.contains_key(key) && pre.s2_map[key].page == page ==> key.vm == owner
                &&& forall|other: VmId| #[trigger]
                    pre.all_vms.contains(other) && other != owner
                        ==> !pre.iommu_private_pages[other].contains(page)
                &&& !pre.iommu_shared_pages.contains(page)
            },
    ensures
        result.0 == shared_pages_made_private(pre, owner, region, target_shared),
        result.0.wf(),
        run_software_ops(pre, result.0, result.1),
    decreases region.count,
{
    if region.count == 1 {
        lemma_make_one_page_private(pre, owner, region, target_shared)
    } else {
        let head = region_page(region, 0);
        let tail = region_tail(region);
        lemma_region_head_tail(region);
        assert(forall|page: PhysPage| #[trigger]
            head.pages().contains(page) ==> region.pages().contains(page));
        assert(forall|page: PhysPage| #[trigger]
            tail.pages().contains(page) ==> region.pages().contains(page));
        let first = lemma_make_one_page_private(pre, owner, head, target_shared);
        let middle = first.0;
        assert forall|page: PhysPage| #[trigger]
            tail.pages().contains(page) && middle.s2_shared_pages.contains(page)
                && !target_shared.contains(page) implies {
            &&& exists|key: VmPageKey| #[trigger]
                middle.s2_map.contains_key(key) && key.vm == owner && middle.s2_map[key].page
                    == page
            &&& forall|key: VmPageKey| #[trigger]
                middle.s2_map.contains_key(key) && middle.s2_map[key].page == page ==> key.vm
                    == owner
            &&& forall|other: VmId| #[trigger]
                middle.all_vms.contains(other) && other != owner
                    ==> !middle.iommu_private_pages[other].contains(page)
            &&& !middle.iommu_shared_pages.contains(page)
        } by {
            assert(!head.pages().contains(page));
            assert(pre.s2_shared_pages.contains(page));
            assert(middle.s2_map == pre.s2_map);
            assert(middle.iommu_private_pages == pre.iommu_private_pages);
            assert(middle.iommu_shared_pages == pre.iommu_shared_pages);
            assert(middle.all_vms == pre.all_vms);
            assert(exists|key: VmPageKey| #[trigger]
                pre.s2_map.contains_key(key) && key.vm == owner && pre.s2_map[key].page == page);
            let witness = choose|key: VmPageKey| #[trigger]
                pre.s2_map.contains_key(key) && key.vm == owner && pre.s2_map[key].page == page;
            assert(exists|key: VmPageKey| #[trigger]
                middle.s2_map.contains_key(key) && key.vm == owner && middle.s2_map[key].page
                    == page) by {
                let key = witness;
            }
            assert(forall|key: VmPageKey| #[trigger]
                pre.s2_map.contains_key(key) && pre.s2_map[key].page == page ==> key.vm == owner);
            assert(forall|key: VmPageKey| #[trigger]
                middle.s2_map.contains_key(key) && middle.s2_map[key].page == page ==> key.vm
                    == owner);
            assert(forall|other: VmId| #[trigger]
                pre.all_vms.contains(other) && other != owner
                    ==> !pre.iommu_private_pages[other].contains(page));
            assert(forall|other: VmId| #[trigger]
                middle.all_vms.contains(other) && other != owner
                    ==> !middle.iommu_private_pages[other].contains(page));
            assert(!pre.iommu_shared_pages.contains(page));
        }
        let rest = lemma_make_region_private(middle, owner, tail, target_shared);
        let post = rest.0;
        let lhs = shared_pages_made_private(middle, owner, tail, target_shared);
        let rhs = shared_pages_made_private(pre, owner, region, target_shared);
        assert(lhs.s2_private_pages =~= rhs.s2_private_pages) by {
            assert(pre.s2_private_pages[owner].union(
                pre.s2_shared_pages.difference(target_shared).intersect(head.pages()),
            ).union(
                pre.s2_shared_pages.difference(head.pages().difference(target_shared)).difference(
                    target_shared,
                ).intersect(tail.pages()),
            ) =~= pre.s2_private_pages[owner].union(
                pre.s2_shared_pages.difference(target_shared).intersect(region.pages()),
            ));
        }
        assert(lhs.s2_shared_pages =~= rhs.s2_shared_pages) by {
            assert(pre.s2_shared_pages.difference(
                head.pages().difference(target_shared),
            ).difference(tail.pages().difference(target_shared)) =~= pre.s2_shared_pages.difference(
                region.pages().difference(target_shared),
            ));
        }
        assert(lhs.all_vms == rhs.all_vms);
        assert(lhs.s2_map == rhs.s2_map);
        assert(lhs.iommu_private_pages == rhs.iommu_private_pages);
        assert(lhs.iommu_shared_pages == rhs.iommu_shared_pages);
        assert(lhs.iommu_s2_map == rhs.iommu_s2_map);
        assert(lhs == rhs);
        lemma_run_software_ops_concat(pre, middle, post, first.1, rest.1);
        (post, first.1 + rest.1)
    }
}

// ---------------------------------------------------------------------------
// Lifecycle and stuttering transitions
// ---------------------------------------------------------------------------
proof fn lemma_add_zone_step_refines(
    pre: EnclaveSoftwareSpec,
    post: EnclaveSoftwareSpec,
    zid: nat,
) -> (ops: Seq<SoftwareOp>)
    requires
        pre.state.invariant(),
        EnclaveSpec::State::next_by(
            pre.state,
            post.state,
            EnclaveSpec::Step::add_zone(zid),
        ),
    ensures
        post.state.invariant(),
        run_software_ops(pre.view(), post.view(), ops),
{
    reveal(EnclaveSpec::State::next_by);
    let next = EnclaveSpec::take_step::add_zone(pre.state, zid);
    let vm = VmId(zid);
    let empty_zone = GhostZone {
        cpu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
        iommu_mem_set: SpecMemorySet { regions: Set::empty(), mappings: Map::empty() },
    };
    assert(post.state.zone_ids == pre.state.zone_ids.insert(zid));
    assert(post.state.zones == pre.state.zones.insert(zid, empty_zone));
    assert(post.state.shared_regions == pre.state.shared_regions.insert(zid, Set::empty()));
    assert(post.view().all_vms =~= pre.view().all_vms.insert(vm));
    assert(post.view().s2_shared_pages =~= pre.view().s2_shared_pages) by {
        assert forall|page: PhysPage| #[trigger]
            post.view().s2_shared_pages.contains(page) <==> pre.view().s2_shared_pages.contains(
                page,
            ) by {
            if post.view().s2_shared_pages.contains(page) {
                let (other, region) = choose|other: nat, region: MemoryRegion|
                    #![trigger post.state.shared_regions[other].contains(region)]
                    post.state.zone_ids.contains(other) && post.state.shared_regions.contains_key(
                        other,
                    ) && post.state.shared_regions[other].contains(region) && region_pages(
                        region,
                    ).contains(page);
                assert(other != zid);
            }
            if pre.view().s2_shared_pages.contains(page) {
                let (other, region) = choose|other: nat, region: MemoryRegion|
                    #![trigger pre.state.shared_regions[other].contains(region)]
                    pre.state.zone_ids.contains(other) && pre.state.shared_regions.contains_key(
                        other,
                    ) && pre.state.shared_regions[other].contains(region) && region_pages(
                        region,
                    ).contains(page);
                assert(post.state.shared_regions[other].contains(region));
            }
        }
    }
    assert(post.view().s2_private_pages =~= pre.view().s2_private_pages.insert(vm, Set::empty()))
        by {
        assert forall|other: VmId| #[trigger]
            post.view().s2_private_pages.contains_key(
                other,
            ) implies post.view().s2_private_pages[other] =~= pre.view().s2_private_pages.insert(
            vm,
            Set::empty(),
        )[other] by {
            if other != vm {
                assert(post.state.zones[other.0] == pre.state.zones[other.0]);
            }
        }
    }
    assert(post.view().s2_map =~= pre.view().s2_map);
    assert(post.view().iommu_private_pages =~= pre.view().iommu_private_pages.insert(
        vm,
        Set::empty(),
    )) by {
        assert(forall|other: VmId| #[trigger]
            post.view().iommu_private_pages.contains_key(other)
                ==> post.view().iommu_private_pages[other]
                =~= pre.view().iommu_private_pages.insert(vm, Set::empty())[other]);
    }
    assert(post.view().iommu_shared_pages =~= pre.view().iommu_shared_pages);
    assert(post.view().iommu_s2_map =~= pre.view().iommu_s2_map);
    let op = SoftwareOp::AddVm(vm);
    assert(SoftwareView::step(pre.view(), post.view(), op));
    lemma_run_software_ops_single(pre.view(), post.view(), op);
    seq![op]
}

proof fn lemma_remove_zone_step_refines(
    pre: EnclaveSoftwareSpec,
    post: EnclaveSoftwareSpec,
    zid: nat,
) -> (ops: Seq<SoftwareOp>)
    requires
        pre.state.invariant(),
        EnclaveSpec::State::next_by(
            pre.state,
            post.state,
            EnclaveSpec::Step::remove_zone(zid),
        ),
    ensures
        post.state.invariant(),
        run_software_ops(pre.view(), post.view(), ops),
{
    reveal(EnclaveSpec::State::next_by);
    let vm = VmId(zid);
    assert(pre.state.zones.contains_key(zid));
    assert(pre.state.zones[zid].cpu_mem_set.empty());
    assert(pre.state.zones[zid].iommu_mem_set.empty());
    assert(pre.view().s2_private_pages[vm] =~= Set::<PhysPage>::empty());
    assert(pre.view().iommu_private_pages[vm] =~= Set::<PhysPage>::empty());
    assert(forall|key: VmPageKey| #[trigger] pre.view().s2_map.contains_key(key) ==> key.vm != vm);
    assert(forall|key: VmPageKey| #[trigger]
        pre.view().iommu_s2_map.contains_key(key) ==> key.vm != vm);
    assert(SoftwareView::remove_vm_enabled(pre.view(), vm));
    assert(post.state.zone_ids == pre.state.zone_ids.remove(zid));
    assert(post.state.zones == pre.state.zones.remove(zid));
    assert(post.state.shared_regions == pre.state.shared_regions.remove(zid));
    assert(post.view().all_vms =~= pre.view().all_vms.remove(vm));
    assert(pre.state.shared_regions[zid] =~= Set::<MemoryRegion>::empty()) by {
        assert(pre.state.inv_shared_regions_exact());
    }
    assert(post.view().s2_shared_pages =~= pre.view().s2_shared_pages) by {
        assert forall|page: PhysPage| #[trigger]
            post.view().s2_shared_pages.contains(page) <==> pre.view().s2_shared_pages.contains(
                page,
            ) by {
            if pre.view().s2_shared_pages.contains(page) {
                let (other, region) = choose|other: nat, region: MemoryRegion|
                    #![trigger pre.state.shared_regions[other].contains(region)]
                    pre.state.zone_ids.contains(other) && pre.state.shared_regions.contains_key(
                        other,
                    ) && pre.state.shared_regions[other].contains(region) && region_pages(
                        region,
                    ).contains(page);
                if other == zid {
                    assert(!pre.state.shared_regions[other].contains(region));
                }
                assert(other != zid);
                assert(post.state.zone_ids.contains(other));
                assert(post.state.shared_regions[other].contains(region));
            }
        }
    }
    assert(post.view().s2_private_pages =~= pre.view().s2_private_pages.remove(vm)) by {
        assert forall|other: VmId| #[trigger]
            post.view().s2_private_pages.contains_key(
                other,
            ) implies post.view().s2_private_pages[other] =~= pre.view().s2_private_pages.remove(
            vm,
        )[other] by {
            assert(other != vm);
            assert(post.state.zones[other.0] == pre.state.zones[other.0]);
        }
    }
    assert(post.view().s2_map =~= pre.view().s2_map);
    assert(post.view().iommu_private_pages =~= pre.view().iommu_private_pages.remove(vm)) by {
        assert(forall|other: VmId| #[trigger]
            post.view().iommu_private_pages.contains_key(other)
                ==> post.view().iommu_private_pages[other]
                =~= pre.view().iommu_private_pages.remove(vm)[other]);
    }
    assert(post.view().iommu_shared_pages =~= pre.view().iommu_shared_pages);
    assert(post.view().iommu_s2_map =~= pre.view().iommu_s2_map);
    let op = SoftwareOp::RemoveVm(vm);
    assert(SoftwareView::step(pre.view(), post.view(), op));
    lemma_run_software_ops_single(pre.view(), post.view(), op);
    seq![op]
}

proof fn lemma_synchronize_step_refines(
    pre: EnclaveSoftwareSpec,
    post: EnclaveSoftwareSpec,
    zid: nat,
) -> (ops: Seq<SoftwareOp>)
    requires
        pre.state.invariant(),
        EnclaveSpec::State::next_by(
            pre.state,
            post.state,
            EnclaveSpec::Step::synchronize_enclave_private_regions_view(zid),
        ),
    ensures
        post.state.invariant(),
        run_software_ops(pre.view(), post.view(), ops),
{
    reveal(EnclaveSpec::State::next_by);
    let next = EnclaveSpec::take_step::synchronize_enclave_private_regions_view(
        pre.state,
        zid,
    );
    assert(post.state.zone_ids == pre.state.zone_ids);
    assert(post.state.zones == pre.state.zones);
    assert(post.state.shared_regions == pre.state.shared_regions);
    assert(post.view() == pre.view());
    Seq::empty()
}

// ---------------------------------------------------------------------------
// Root CPU transitions
// ---------------------------------------------------------------------------
proof fn lemma_cpu_insert_normal_region_step_refines(
    pre: EnclaveSoftwareSpec,
    post: EnclaveSoftwareSpec,
    concrete: MemoryRegion,
) -> (ops: Seq<SoftwareOp>)
    requires
        pre.state.invariant(),
        EnclaveSpec::State::next_by(
            pre.state,
            post.state,
            EnclaveSpec::Step::cpu_insert_normal_region(concrete),
        ),
    ensures
        post.state.invariant(),
        run_software_ops(pre.view(), post.view(), ops),
{
    reveal(EnclaveSpec::State::next_by);
    let zid = root_zone_id();
    let vm = VmId(zid);
    let old_zone = pre.state.zones[zid];
    let region = region_to_abstract(zid, concrete);
    assert(post.state.zone_ids == pre.state.zone_ids);
    assert(post.state.zones == pre.state.zones.insert(zid, old_zone.cpu_insert_region(concrete)));
    assert(post.state.shared_regions == pre.state.shared_regions);
    assert(old_zone.wf());
    old_zone.cpu_mem_set.lemma_insert_region_wf(concrete);
    lemma_enclave_projection_wf(pre);
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_zones_s2_entries_fresh(pre.state.zone_ids, pre.state.zones, zid, concrete);
    lemma_memory_set_mapped_pages_insert(old_zone.cpu_mem_set, concrete);
    lemma_zones_s2_insert(pre.state.zone_ids, pre.state.zones, zid, concrete);
    assert(post.view().s2_shared_pages =~= pre.view().s2_shared_pages) by {
        assert(post.state.shared_regions == pre.state.shared_regions);
    }
    assert forall|page: PhysPage, other: VmId| #[trigger]
        region.pages().contains(page) && #[trigger] pre.view().all_vms.contains(other) && other
            != vm implies !pre.view().s2_private_pages[other].contains(page) by {
        if pre.view().s2_private_pages[other].contains(page) {
            assert(other.0 != root_zone_id());
            lemma_nonroot_unshared_mapped_page_has_private_region(pre, other.0, page);
            let enclave_region = choose|stored: MemoryRegion| #[trigger]
                pre.state.zones[other.0].cpu_mem_set.regions.contains(stored) && region_pages(
                    stored,
                ).contains(page) && region_in_enclave_memory(other.0, stored);
            lemma_normal_and_enclave_page_disjoint(concrete, enclave_region, other.0, page);
        }
    }
    assert forall|page: PhysPage| #[trigger]
        region.pages().contains(page) && pre.view().s2_private_pages[vm].contains(
            page,
        ) implies exists|key: VmPageKey| #[trigger]
        pre.view().s2_map.contains_key(key) && key.vm == vm && pre.view().s2_map[key].page
            == page by {
        lemma_cpu_mapped_page_has_entry(pre, zid, page);
    }
    assert forall|page: PhysPage, other: VmId| #[trigger]
        region.pages().contains(page) && #[trigger] pre.view().all_vms.contains(other) && other
            != vm implies !pre.view().iommu_private_pages[other].contains(page) by {
        assert(pre.state.zones[other.0].iommu_mem_set.empty());
    }
    assert(forall|page: PhysPage| #[trigger]
        region.pages().contains(page) ==> !pre.view().iommu_shared_pages.contains(page));
    let trace = lemma_root_insert_region(pre.view(), region);
    let target = trace.0;
    assert(post.view().all_vms == target.all_vms);
    assert(post.view().s2_shared_pages =~= target.s2_shared_pages);
    assert(post.view().s2_map =~= target.s2_map);
    assert(post.view().iommu_private_pages == target.iommu_private_pages);
    assert(post.view().iommu_shared_pages == target.iommu_shared_pages);
    assert(post.view().iommu_s2_map == target.iommu_s2_map);
    assert(post.view().s2_private_pages =~= target.s2_private_pages) by {
        let added_pages = region_pages(concrete);
        assert forall|other: VmId| #[trigger]
            post.view().s2_private_pages.contains_key(
                other,
            ) implies post.view().s2_private_pages[other] =~= target.s2_private_pages[other] by {
            if other == vm {
                assert(zone_cpu_mapped_pages(post.state.zones[zid]) =~= zone_cpu_mapped_pages(
                    pre.state.zones[zid],
                ).union(added_pages));
                assert(forall|page: PhysPage| #[trigger]
                    zone_cpu_mapped_pages(pre.state.zones[zid]).union(added_pages).difference(
                        pre.view().s2_shared_pages,
                    ).contains(page) <==> pre.view().s2_private_pages[vm].union(
                        added_pages.difference(pre.view().s2_shared_pages),
                    ).contains(page));
            }
        }
    }
    assert(post.view() == target);
    trace.1
}

proof fn lemma_cpu_remove_root_normal_region_refines(
    pre: EnclaveSoftwareSpec,
    concrete: MemoryRegion,
) -> (result: (EnclaveSoftwareSpec, Seq<SoftwareOp>))
    requires
        pre.state.invariant(),
        pre.state.zones.contains_key(root_zone_id()),
        pre.state.zones[root_zone_id()].cpu_mem_set.regions.contains(concrete),
    ensures
        result.0.state.invariant(),
        EnclaveSpec::State::next_by(
            pre.state,
            result.0.state,
            EnclaveSpec::Step::cpu_remove_region(root_zone_id(), concrete),
        ),
        run_software_ops(pre.view(), result.0.view(), result.1),
{
    let zid = root_zone_id();
    let vm = VmId(zid);
    let old_zone = pre.state.zones[zid];
    let region = region_to_abstract(zid, concrete);
    let post = EnclaveSoftwareSpec {
        state: EnclaveSpec::take_step::cpu_remove_region(pre.state, zid, concrete),
    };
    reveal(EnclaveSpec::State::next_by);
    assert(post.state.zone_ids == pre.state.zone_ids);
    assert(post.state.zones == pre.state.zones.insert(zid, old_zone.cpu_remove_region(concrete)));
    assert(old_zone.wf());
    old_zone.cpu_mem_set.lemma_remove_region_exact_wf(concrete);
    assert(live_shared_regions(zid, old_zone) =~= Set::<MemoryRegion>::empty());
    assert(live_shared_regions(zid, old_zone.cpu_remove_region(concrete)) =~= Set::<
        MemoryRegion,
    >::empty());
    assert(post.state.shared_regions =~= pre.state.shared_regions) by {
        assert forall|other: nat| #[trigger]
            post.state.shared_regions.contains_key(other) implies post.state.shared_regions[other]
            =~= pre.state.shared_regions[other] by {
            if other == zid {
                assert(pre.state.shared_regions[other] == live_shared_regions(
                    other,
                    pre.state.zones[other],
                ));
            }
        }
    }
    lemma_enclave_projection_wf(pre);
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_zones_s2_remove(pre.state.zone_ids, pre.state.zones, zid, concrete);
    lemma_region_in_memory_set_maps_entries(zid, old_zone.cpu_mem_set, concrete);
    assert(region.wf());
    assert(pre.view().all_vms.contains(vm));
    assert(abstract_region_installed(pre.view().s2_map, region));
    assert forall|page: PhysPage| #[trigger]
        region.pages().contains(page) implies pre.view().s2_shared_pages.contains(page)
        || pre.view().s2_private_pages[vm].contains(page) by {
        lemma_memory_set_region_page_is_mapped(old_zone.cpu_mem_set, concrete, page);
    }
    assert forall|page: PhysPage| #[trigger]
        region.pages().contains(page) && pre.view().s2_shared_pages.contains(page) implies exists|
        key: VmPageKey,
    | #[trigger]
        pre.view().s2_map.remove_keys(region.entries().dom()).contains_key(key)
            && pre.view().s2_map.remove_keys(region.entries().dom())[key].page == page by {
        let key = lemma_shared_page_has_nonroot_entry(pre, page);
        assert(!region.entries().contains_key(key)) by {
            if region.entries().contains_key(key) {
                assert(key.vm == vm);
            }
        }
        assert(pre.view().s2_map.remove_keys(region.entries().dom()).contains_key(key));
    }
    let trace = lemma_root_remove_region(pre.view(), region);
    let target = trace.0;
    assert(post.view().all_vms == target.all_vms);
    assert(post.view().s2_shared_pages =~= target.s2_shared_pages) by {
        assert(post.state.shared_regions =~= pre.state.shared_regions);
    }
    assert(post.view().s2_map =~= target.s2_map);
    assert(post.view().iommu_private_pages == target.iommu_private_pages);
    assert(post.view().iommu_shared_pages == target.iommu_shared_pages);
    assert(post.view().iommu_s2_map == target.iommu_s2_map);
    assert(post.view().s2_private_pages =~= target.s2_private_pages) by {
        assert forall|owner: VmId| #[trigger]
            post.view().s2_private_pages.contains_key(
                owner,
            ) implies post.view().s2_private_pages[owner] =~= target.s2_private_pages[owner] by {
            if owner == vm {
                assert forall|page: PhysPage| #[trigger]
                    post.view().s2_private_pages[owner].contains(page)
                        <==> private_after_cpu_remove(pre.view(), region)[owner].contains(page) by {
                    if post.view().s2_private_pages[owner].contains(page) {
                        lemma_memory_set_mapped_pages_iff_region_page(
                            post.state.zones[zid].cpu_mem_set,
                            page,
                        );
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            post.state.zones[zid].cpu_mem_set.regions.contains(stored)
                                && region_pages(stored).contains(page);
                        assert(old_zone.cpu_mem_set.regions.contains(stored));
                        assert(stored != concrete);
                        lemma_memory_set_region_page_is_mapped(old_zone.cpu_mem_set, stored, page);
                        assert(pre.view().s2_private_pages[owner].contains(page));
                        if region.pages().contains(page) {
                            lemma_cpu_mapped_page_has_entry(post, zid, page);
                            let key = choose|key: VmPageKey| #[trigger]
                                post.view().s2_map.contains_key(key) && key.vm == owner
                                    && post.view().s2_map[key].page == page;
                            assert(pre.view().s2_map.remove_keys(
                                region.entries().dom(),
                            ).contains_key(key));
                        }
                    }
                    if private_after_cpu_remove(pre.view(), region)[owner].contains(page) {
                        assert(pre.view().s2_private_pages[owner].contains(page));
                        if !region.pages().contains(page) {
                            lemma_memory_set_mapped_pages_iff_region_page(
                                old_zone.cpu_mem_set,
                                page,
                            );
                            let stored = choose|stored: MemoryRegion| #[trigger]
                                old_zone.cpu_mem_set.regions.contains(stored) && region_pages(
                                    stored,
                                ).contains(page);
                            assert(stored != concrete);
                            lemma_memory_set_region_page_is_mapped(
                                post.state.zones[zid].cpu_mem_set,
                                stored,
                                page,
                            );
                        } else {
                            let key = choose|key: VmPageKey| #[trigger]
                                pre.view().s2_map.remove_keys(region.entries().dom()).contains_key(
                                    key,
                                ) && pre.view().s2_map.remove_keys(region.entries().dom())[key].page
                                    == page;
                            assert(post.view().s2_map.contains_key(key));
                            assert(post.view().s2_map[key].page == page);
                            lemma_cpu_entry_maps_page(post, key);
                        }
                    }
                }
            } else {
                assert(post.state.zones[owner.0] == pre.state.zones[owner.0]);
            }
        }
    }
    assert(post.view() == target);
    (post, trace.1)
}

// ---------------------------------------------------------------------------
// Enclave-private CPU transitions
// ---------------------------------------------------------------------------
proof fn lemma_cpu_insert_enclave_private_region_step_refines(
    pre: EnclaveSoftwareSpec,
    post: EnclaveSoftwareSpec,
    zid: nat,
    concrete: MemoryRegion,
) -> (ops: Seq<SoftwareOp>)
    requires
        pre.state.invariant(),
        EnclaveSpec::State::next_by(
            pre.state,
            post.state,
            EnclaveSpec::Step::cpu_insert_enclave_private_region(zid, concrete),
        ),
    ensures
        post.state.invariant(),
        run_software_ops(pre.view(), post.view(), ops),
{
    reveal(EnclaveSpec::State::next_by);
    let next = EnclaveSpec::take_step::cpu_insert_enclave_private_region(
        pre.state,
        zid,
        concrete,
    );
    let vm = VmId(zid);
    let old_zone = pre.state.zones[zid];
    let region = region_to_abstract(zid, concrete);
    assert(post.state.zone_ids == pre.state.zone_ids);
    assert(post.state.zones == pre.state.zones.insert(zid, old_zone.cpu_insert_region(concrete)));
    assert(post.state.shared_regions == pre.state.shared_regions);
    assert(old_zone.wf());
    old_zone.cpu_mem_set.lemma_insert_region_wf(concrete);
    lemma_enclave_region_not_normal_memory(zid, concrete);
    lemma_enclave_projection_wf(pre);
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_zones_s2_entries_fresh(pre.state.zone_ids, pre.state.zones, zid, concrete);
    lemma_memory_set_mapped_pages_insert(old_zone.cpu_mem_set, concrete);
    lemma_zones_s2_insert(pre.state.zone_ids, pre.state.zones, zid, concrete);
    assert(region.wf());
    assert(pre.view().all_vms.contains(vm));
    assert forall|page: PhysPage, other: VmId| #[trigger]
        region.pages().contains(page) && #[trigger] pre.view().all_vms.contains(
            other,
        ) && other != vm implies !pre.view().s2_private_pages[other].contains(page) by {
        if pre.view().s2_private_pages[other].contains(page) {
            if other.0 == root_zone_id() {
                let root_set = pre.state.zones[root_zone_id()].cpu_mem_set;
                lemma_memory_set_mapped_page_has_region(root_set, page);
                let normal_region = choose|stored: MemoryRegion| #[trigger]
                    root_set.regions.contains(stored) && region_pages(stored).contains(page);
                assert(region_in_normal_memory(normal_region));
                lemma_normal_and_enclave_page_disjoint(normal_region, concrete, zid, page);
            } else {
                lemma_nonroot_unshared_mapped_page_has_private_region(pre, other.0, page);
                let old_region = choose|stored: MemoryRegion| #[trigger]
                    pre.state.zones[other.0].cpu_mem_set.regions.contains(stored) && region_pages(
                        stored,
                    ).contains(page) && region_in_enclave_memory(other.0, stored);
                assert(live_enclave_private_regions(other.0, pre.state.zones[other.0]).contains(
                    old_region,
                ));
                assert(pre.state.enclave_private_regions_view[other.0].contains(old_region));
                lemma_shared_page_implies_pmem_overlap(old_region, concrete, page);
            }
        }
    }
    assert forall|page: PhysPage| #[trigger]
        region.pages().contains(page) implies !pre.view().s2_shared_pages.contains(page) by {
        if pre.view().s2_shared_pages.contains(page) {
            let (_, normal_region) = lemma_shared_page_has_normal_region(pre, page);
            lemma_normal_and_enclave_page_disjoint(normal_region, concrete, zid, page);
        }
    }
    assert forall|page: PhysPage, other: VmId| #[trigger]
        region.pages().contains(page) && #[trigger] pre.view().all_vms.contains(other) && other
            != vm implies !pre.view().iommu_private_pages[other].contains(page) by {
        if other.0 == root_zone_id() && pre.view().iommu_private_pages[other].contains(page) {
            let iommu_set = pre.state.zones[root_zone_id()].iommu_mem_set;
            lemma_memory_set_mapped_page_has_region(iommu_set, page);
            let normal_region = choose|stored: MemoryRegion| #[trigger]
                iommu_set.regions.contains(stored) && region_pages(stored).contains(page);
            assert(region_in_dma_memory(normal_region));
            lemma_region_pages_match_enclave(normal_region);
            dma_memory_is_normal_memory();
            assert(region_in_normal_memory(normal_region));
            lemma_normal_and_enclave_page_disjoint(normal_region, concrete, zid, page);
        } else if other.0 != root_zone_id() {
            assert(pre.state.zones[other.0].iommu_mem_set.empty());
        }
    }
    assert(forall|page: PhysPage| #[trigger]
        region.pages().contains(page) ==> !pre.view().iommu_shared_pages.contains(page));
    assert(SoftwareView::cpu_insert_private_region_enabled(pre.view(), region));
    assert(post.view().all_vms =~= pre.view().all_vms);
    assert(post.view().s2_shared_pages =~= pre.view().s2_shared_pages);
    assert(post.view().s2_map =~= pre.view().s2_map.union_prefer_right(region.entries()));
    assert(post.view().iommu_private_pages =~= pre.view().iommu_private_pages);
    assert(post.view().iommu_shared_pages =~= pre.view().iommu_shared_pages);
    assert(post.view().iommu_s2_map =~= pre.view().iommu_s2_map);
    assert(post.view().s2_private_pages =~= pre.view().s2_private_pages.insert(
        vm,
        pre.view().s2_private_pages[vm].union(region.pages()),
    )) by {
        assert forall|other: VmId| #[trigger]
            post.view().s2_private_pages.contains_key(
                other,
            ) implies post.view().s2_private_pages[other] =~= pre.view().s2_private_pages.insert(
            vm,
            pre.view().s2_private_pages[vm].union(region.pages()),
        )[other] by {
            if other == vm {
                assert(zone_cpu_mapped_pages(post.state.zones[zid]) =~= zone_cpu_mapped_pages(
                    pre.state.zones[zid],
                ).union(region.pages()));
            }
        }
    }
    assert(SoftwareView::cpu_insert_private_region_step(pre.view(), post.view(), region));
    let op = SoftwareOp::CpuInsertPrivateRegion(region);
    assert(SoftwareView::step(pre.view(), post.view(), op));
    lemma_run_software_ops_single(pre.view(), post.view(), op);
    seq![op]
}

proof fn lemma_cpu_remove_enclave_private_region_refines(
    pre: EnclaveSoftwareSpec,
    zid: nat,
    concrete: MemoryRegion,
) -> (result: (EnclaveSoftwareSpec, Seq<SoftwareOp>))
    requires
        pre.state.invariant(),
        pre.state.zones.contains_key(zid),
        zid != root_zone_id(),
        pre.state.zones[zid].cpu_mem_set.regions.contains(concrete),
        region_in_enclave_memory(zid, concrete),
    ensures
        result.0.state.invariant(),
        EnclaveSpec::State::next_by(
            pre.state,
            result.0.state,
            EnclaveSpec::Step::cpu_remove_region(zid, concrete),
        ),
        run_software_ops(pre.view(), result.0.view(), result.1),
{
    let vm = VmId(zid);
    let old_zone = pre.state.zones[zid];
    let region = region_to_abstract(zid, concrete);
    let post = EnclaveSoftwareSpec {
        state: EnclaveSpec::take_step::cpu_remove_region(pre.state, zid, concrete),
    };
    reveal(EnclaveSpec::State::next_by);
    assert(post.state.zone_ids == pre.state.zone_ids);
    assert(post.state.zones == pre.state.zones.insert(zid, old_zone.cpu_remove_region(concrete)));
    assert(old_zone.wf());
    old_zone.cpu_mem_set.lemma_remove_region_exact_wf(concrete);
    lemma_enclave_region_not_normal_memory(zid, concrete);
    assert(live_shared_regions(zid, old_zone.cpu_remove_region(concrete)) =~= live_shared_regions(
        zid,
        old_zone,
    )) by {
        assert forall|stored: MemoryRegion| #[trigger]
            live_shared_regions(zid, old_zone.cpu_remove_region(concrete)).contains(stored)
                <==> live_shared_regions(zid, old_zone).contains(stored) by {
            if stored == concrete {
                assert(!region_in_normal_memory(concrete));
            }
        }
    }
    assert(post.state.shared_regions =~= pre.state.shared_regions) by {
        assert forall|other: nat| #[trigger]
            post.state.shared_regions.contains_key(other) implies post.state.shared_regions[other]
            =~= pre.state.shared_regions[other] by {
            if other == zid {
                assert(pre.state.shared_regions[other] == live_shared_regions(
                    other,
                    pre.state.zones[other],
                ));
            }
        }
    }
    lemma_enclave_projection_wf(pre);
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_zones_s2_remove(pre.state.zone_ids, pre.state.zones, zid, concrete);
    lemma_region_in_memory_set_maps_entries(zid, old_zone.cpu_mem_set, concrete);
    assert(region.wf());
    assert(pre.view().all_vms.contains(vm));
    assert forall|page: PhysPage| #[trigger]
        region.pages().contains(page) implies !pre.view().s2_shared_pages.contains(page) by {
        if pre.view().s2_shared_pages.contains(page) {
            let (_, normal_region) = lemma_shared_page_has_normal_region(pre, page);
            lemma_normal_and_enclave_page_disjoint(normal_region, concrete, zid, page);
        }
    }
    assert forall|page: PhysPage| #[trigger]
        region.pages().contains(page) implies pre.view().s2_private_pages[vm].contains(page) by {
        lemma_memory_set_region_page_is_mapped(old_zone.cpu_mem_set, concrete, page);
    }
    assert(abstract_region_installed(pre.view().s2_map, region));
    assert(SoftwareView::cpu_remove_private_region_enabled(pre.view(), region));
    assert(post.view().all_vms =~= pre.view().all_vms);
    assert(post.view().s2_shared_pages =~= pre.view().s2_shared_pages) by {
        assert(forall|page: PhysPage| #[trigger]
            post.view().s2_shared_pages.contains(page) <==> pre.view().s2_shared_pages.contains(
                page,
            ));
    }
    assert(post.view().s2_map =~= pre.view().s2_map.remove_keys(region.entries().dom()));
    assert(post.view().iommu_private_pages =~= pre.view().iommu_private_pages);
    assert(post.view().iommu_shared_pages =~= pre.view().iommu_shared_pages);
    assert(post.view().iommu_s2_map =~= pre.view().iommu_s2_map);
    let target_private = private_pages_after_unmap(
        pre.view().s2_private_pages,
        post.view().s2_map,
        vm,
        region.pages(),
    );
    assert(post.view().s2_private_pages =~= target_private) by {
        assert forall|other: VmId| #[trigger]
            post.view().s2_private_pages.contains_key(
                other,
            ) implies post.view().s2_private_pages[other] =~= target_private[other] by {
            if other == vm {
                assert forall|page: PhysPage| #[trigger]
                    post.view().s2_private_pages[other].contains(page)
                        <==> target_private[other].contains(page) by {
                    if post.view().s2_private_pages[other].contains(page) {
                        lemma_cpu_mapped_page_has_entry(post, zid, page);
                        let key = choose|key: VmPageKey| #[trigger]
                            post.view().s2_map.contains_key(key) && key.vm == other
                                && post.view().s2_map[key].page == page;
                        assert(pre.view().s2_map.contains_key(key));
                        lemma_cpu_entry_maps_page(pre, key);
                        assert(pre.view().s2_private_pages[other].contains(page));
                    }
                    if target_private[other].contains(page) {
                        if !region.pages().contains(page) {
                            lemma_memory_set_mapped_pages_iff_region_page(
                                old_zone.cpu_mem_set,
                                page,
                            );
                            let stored = choose|stored: MemoryRegion| #[trigger]
                                old_zone.cpu_mem_set.regions.contains(stored)
                                    && region_pages(stored).contains(page);
                            assert(stored != concrete);
                            lemma_memory_set_region_page_is_mapped(
                                post.state.zones[zid].cpu_mem_set,
                                stored,
                                page,
                            );
                        } else {
                            let key = choose|key: VmPageKey| #[trigger]
                                post.view().s2_map.contains_key(key) && key.vm == other
                                    && post.view().s2_map[key].page == page;
                            lemma_cpu_entry_maps_page(post, key);
                        }
                    }
                }
            }
        }
    }
    assert(SoftwareView::cpu_remove_private_region_step(pre.view(), post.view(), region));
    let op = SoftwareOp::CpuRemovePrivateRegion(region);
    assert(SoftwareView::step(pre.view(), post.view(), op));
    lemma_run_software_ops_single(pre.view(), post.view(), op);
    (post, seq![op])
}

// ---------------------------------------------------------------------------
// Dynamic enclave Shared insertion
// ---------------------------------------------------------------------------
proof fn lemma_cpu_insert_enclave_shared_region_step_refines(
    pre: EnclaveSoftwareSpec,
    post: EnclaveSoftwareSpec,
    zid: nat,
    concrete: MemoryRegion,
) -> (ops: Seq<SoftwareOp>)
    requires
        pre.state.invariant(),
        EnclaveSpec::State::next_by(
            pre.state,
            post.state,
            EnclaveSpec::Step::cpu_insert_enclave_shared_region(zid, concrete),
        ),
    ensures
        post.state.invariant(),
        run_software_ops(pre.view(), post.view(), ops),
{
    reveal(EnclaveSpec::State::next_by);
    let root = VmId(root_zone_id());
    let vm = VmId(zid);
    let old_zone = pre.state.zones[zid];
    let region = region_to_abstract(zid, concrete);
    assert(post.state.zone_ids == pre.state.zone_ids);
    assert(post.state.zones == pre.state.zones.insert(zid, old_zone.cpu_insert_region(concrete)));
    assert(old_zone.wf());
    old_zone.cpu_mem_set.lemma_insert_region_wf(concrete);
    lemma_normal_region_not_enclave_memory(zid, concrete);
    lemma_enclave_projection_wf(pre);
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_zones_s2_entries_fresh(pre.state.zone_ids, pre.state.zones, zid, concrete);
    lemma_memory_set_mapped_pages_insert(old_zone.cpu_mem_set, concrete);
    lemma_zones_s2_insert(pre.state.zone_ids, pre.state.zones, zid, concrete);
    assert(region.wf());
    assert(pre.view().all_vms.contains(vm));
    assert forall|page: PhysPage, owner: VmId| #[trigger]
        region.pages().contains(page) && #[trigger] pre.view().all_vms.contains(owner)
            && pre.view().s2_private_pages[owner].contains(page) implies owner == root by {
        if owner != root {
            lemma_nonroot_unshared_mapped_page_has_private_region(pre, owner.0, page);
            let enclave_region = choose|stored: MemoryRegion| #[trigger]
                pre.state.zones[owner.0].cpu_mem_set.regions.contains(stored) && region_pages(
                    stored,
                ).contains(page) && region_in_enclave_memory(owner.0, stored);
            lemma_normal_and_enclave_page_disjoint(concrete, enclave_region, owner.0, page);
        }
    }
    let transfer = if pre.view().all_vms.contains(root) {
        assert forall|page: PhysPage| #[trigger]
            region.pages().contains(page) && pre.view().s2_private_pages[root].contains(
                page,
            ) implies exists|key: VmPageKey| #[trigger]
            pre.view().s2_map.contains_key(key) && key.vm == root && pre.view().s2_map[key].page
                == page by {
            lemma_cpu_mapped_page_has_entry(pre, root_zone_id(), page);
        }
        lemma_make_region_shared(pre.view(), root, region)
    } else {
        (pre.view(), Seq::empty())
    };
    let middle = transfer.0;
    assert(middle.wf());
    assert(middle.s2_map == pre.view().s2_map);
    assert(middle.iommu_private_pages == pre.view().iommu_private_pages);
    assert(middle.iommu_shared_pages == pre.view().iommu_shared_pages);
    assert(middle.iommu_s2_map == pre.view().iommu_s2_map);
    assert(middle.all_vms.contains(vm));
    assert(forall|key: VmPageKey| #[trigger]
        region.entries().contains_key(key) ==> !middle.s2_map.contains_key(key));
    assert forall|page: PhysPage, owner: VmId| #[trigger]
        region.pages().contains(page) && #[trigger] middle.all_vms.contains(
            owner,
        ) implies !middle.s2_private_pages[owner].contains(page) by {
        if middle.s2_private_pages[owner].contains(page) {
            if owner == root {
                if pre.view().all_vms.contains(root) {
                    assert(middle.s2_private_pages[root]
                        =~= pre.view().s2_private_pages[root].difference(region.pages()));
                } else {
                    assert(false);
                }
            } else {
                assert(middle.s2_private_pages[owner] =~= pre.view().s2_private_pages[owner]);
                assert(pre.view().s2_private_pages[owner].contains(page));
                assert(pre.view().all_vms.contains(owner));
                assert(owner == root);
            }
        }
    }
    assert(SoftwareView::cpu_insert_shared_region_enabled(middle, region));
    let mapped = SoftwareView {
        s2_shared_pages: middle.s2_shared_pages.union(region.pages()),
        s2_map: middle.s2_map.union_prefer_right(region.entries()),
        ..middle
    };
    assert(SoftwareView::cpu_insert_shared_region_step(middle, mapped, region));
    let op = SoftwareOp::CpuInsertSharedRegion(region);
    assert(SoftwareView::step(middle, mapped, op));
    lemma_run_software_ops_single(middle, mapped, op);
    assert(post.view().all_vms == mapped.all_vms);
    assert(post.view().s2_map =~= mapped.s2_map);
    assert(post.view().iommu_private_pages == mapped.iommu_private_pages);
    assert(post.view().iommu_shared_pages == mapped.iommu_shared_pages);
    assert(post.view().iommu_s2_map == mapped.iommu_s2_map);
    assert(post.view().s2_shared_pages =~= mapped.s2_shared_pages) by {
        assert(post.view().s2_shared_pages =~= pre.view().s2_shared_pages.union(region.pages()))
            by {
            assert forall|page: PhysPage| #[trigger]
                post.view().s2_shared_pages.contains(page) <==> pre.view().s2_shared_pages.union(
                    region.pages(),
                ).contains(page) by {
                if post.view().s2_shared_pages.contains(page) {
                    let (other, stored) = choose|other: nat, stored: MemoryRegion|
                        #![trigger post.state.shared_regions[other].contains(stored)]
                        post.state.zone_ids.contains(other)
                            && post.state.shared_regions.contains_key(other)
                            && post.state.shared_regions[other].contains(stored) && region_pages(
                            stored,
                        ).contains(page);
                    if other == zid && stored == concrete {
                    } else {
                        assert(pre.state.shared_regions[other].contains(stored));
                    }
                }
                if region.pages().contains(page) {
                    assert(post.state.shared_regions[zid].contains(concrete));
                }
                if pre.view().s2_shared_pages.contains(page) {
                    let (other, stored) = choose|other: nat, stored: MemoryRegion|
                        #![trigger pre.state.shared_regions[other].contains(stored)]
                        pre.state.zone_ids.contains(other) && pre.state.shared_regions.contains_key(
                            other,
                        ) && pre.state.shared_regions[other].contains(stored) && region_pages(
                            stored,
                        ).contains(page);
                    assert(post.state.shared_regions[other].contains(stored));
                }
            }
        }
        if pre.view().all_vms.contains(root) {
            assert(middle.s2_shared_pages =~= pre.view().s2_shared_pages.union(
                pre.view().s2_private_pages[root].intersect(region.pages()),
            ));
        } else {
            assert(middle.s2_shared_pages == pre.view().s2_shared_pages);
        }
        assert(middle.s2_shared_pages.union(region.pages()) =~= pre.view().s2_shared_pages.union(
            region.pages(),
        ));
    }
    assert(post.view().s2_private_pages =~= mapped.s2_private_pages) by {
        assert forall|owner: VmId| #[trigger]
            post.view().s2_private_pages.contains_key(
                owner,
            ) implies post.view().s2_private_pages[owner] =~= mapped.s2_private_pages[owner] by {
            if owner == root {
                assert(post.view().s2_private_pages[owner]
                    =~= pre.view().s2_private_pages[owner].difference(region.pages())) by {
                    assert(forall|page: PhysPage| #[trigger]
                        post.view().s2_private_pages[owner].contains(page)
                            <==> pre.view().s2_private_pages[owner].difference(
                            region.pages(),
                        ).contains(page));
                }
            } else if owner == vm {
                assert(zone_cpu_mapped_pages(post.state.zones[zid]) =~= zone_cpu_mapped_pages(
                    pre.state.zones[zid],
                ).union(region.pages()));
                assert forall|page: PhysPage| #[trigger]
                    post.view().s2_private_pages[owner].contains(page)
                        <==> pre.view().s2_private_pages[owner].contains(page) by {
                    if post.view().s2_private_pages[owner].contains(page)
                        && region.pages().contains(page) {
                        assert(post.view().s2_shared_pages.contains(page));
                    }
                }
            }
        }
    }
    assert(post.view() == mapped);
    lemma_run_software_ops_concat(pre.view(), middle, post.view(), transfer.1, seq![op]);
    transfer.1 + seq![op]
}

// ---------------------------------------------------------------------------
// Dynamic Shared removal and root-Private restoration
// ---------------------------------------------------------------------------
proof fn lemma_cpu_remove_enclave_shared_region_refines(
    pre: EnclaveSoftwareSpec,
    zid: nat,
    concrete: MemoryRegion,
) -> (result: (EnclaveSoftwareSpec, Seq<SoftwareOp>))
    requires
        pre.state.invariant(),
        pre.state.zones.contains_key(zid),
        zid != root_zone_id(),
        pre.state.zones[zid].cpu_mem_set.regions.contains(concrete),
        region_in_normal_memory(concrete),
    ensures
        result.0.state.invariant(),
        EnclaveSpec::State::next_by(
            pre.state,
            result.0.state,
            EnclaveSpec::Step::cpu_remove_region(zid, concrete),
        ),
        run_software_ops(pre.view(), result.0.view(), result.1),
{
    let root = VmId(root_zone_id());
    let vm = VmId(zid);
    let old_zone = pre.state.zones[zid];
    let region = region_to_abstract(zid, concrete);
    let post = EnclaveSoftwareSpec {
        state: EnclaveSpec::take_step::cpu_remove_region(pre.state, zid, concrete),
    };
    reveal(EnclaveSpec::State::next_by);
    assert(post.state.zone_ids == pre.state.zone_ids);
    assert(post.state.zones == pre.state.zones.insert(zid, old_zone.cpu_remove_region(concrete)));
    assert(old_zone.wf());
    old_zone.cpu_mem_set.lemma_remove_region_exact_wf(concrete);
    lemma_enclave_projection_wf(pre);
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_zones_s2_remove(pre.state.zone_ids, pre.state.zones, zid, concrete);
    lemma_region_in_memory_set_maps_entries(zid, old_zone.cpu_mem_set, concrete);
    assert(pre.state.shared_regions[zid].contains(concrete)) by {
        assert(pre.state.shared_regions[zid] == live_shared_regions(zid, old_zone));
    }
    assert(region.wf());
    assert(pre.view().all_vms.contains(vm));
    assert(forall|page: PhysPage| #[trigger]
        region.pages().contains(page) ==> pre.view().s2_shared_pages.contains(page));
    assert(abstract_region_installed(pre.view().s2_map, region));
    assert(SoftwareView::cpu_remove_shared_region_enabled(pre.view(), region));
    let removed_map = pre.view().s2_map.remove_keys(region.entries().dom());
    let removed_shared = Set::new(
        |page: PhysPage|
            {
                &&& pre.view().s2_shared_pages.contains(page)
                &&& (!region.pages().contains(page) || exists|key: VmPageKey| #[trigger]
                    removed_map.contains_key(key) && removed_map[key].page == page)
            },
    );
    let middle = SoftwareView {
        s2_shared_pages: removed_shared,
        s2_map: removed_map,
        ..pre.view()
    };
    assert(SoftwareView::cpu_remove_shared_region_step(pre.view(), middle, region));
    lemma_cpu_remove_shared_region_step_preserves_wf(pre.view(), middle, region);
    let remove_op = SoftwareOp::CpuRemoveSharedRegion(region);
    assert(SoftwareView::step(pre.view(), middle, remove_op));
    lemma_run_software_ops_single(pre.view(), middle, remove_op);

    assert forall|page: PhysPage| #[trigger]
        region.pages().contains(page) && middle.s2_shared_pages.contains(page)
            && !post.view().s2_shared_pages.contains(page) implies {
        &&& exists|key: VmPageKey| #[trigger]
            middle.s2_map.contains_key(key) && key.vm == root && middle.s2_map[key].page == page
        &&& forall|key: VmPageKey| #[trigger]
            middle.s2_map.contains_key(key) && middle.s2_map[key].page == page ==> key.vm == root
        &&& forall|other: VmId| #[trigger]
            middle.all_vms.contains(other) && other != root
                ==> !middle.iommu_private_pages[other].contains(page)
        &&& !middle.iommu_shared_pages.contains(page)
    } by {
        assert(exists|key: VmPageKey| #[trigger]
            middle.s2_map.contains_key(key) && middle.s2_map[key].page == page);
        assert forall|key: VmPageKey| #[trigger]
            middle.s2_map.contains_key(key) && middle.s2_map[key].page == page implies key.vm
            == root by {
            if key.vm != root {
                let other_zid = key.vm.0;
                assert(post.state.zones.contains_key(other_zid));
                let mem_set = post.state.zones[other_zid].cpu_mem_set;
                assert(memory_set_mapped_pages(mem_set).contains(page));
                lemma_memory_set_mapped_page_has_region(mem_set, page);
                let stored = choose|stored: MemoryRegion| #[trigger]
                    mem_set.regions.contains(stored) && region_pages(stored).contains(page);
                if region_in_enclave_memory(other_zid, stored) {
                    lemma_normal_and_enclave_page_disjoint(concrete, stored, other_zid, page);
                } else {
                    assert(region_in_normal_memory(stored));
                    assert(post.state.shared_regions[other_zid].contains(stored));
                    assert(post.view().s2_shared_pages.contains(page));
                }
            }
        }
        let key = choose|key: VmPageKey| #[trigger]
            middle.s2_map.contains_key(key) && middle.s2_map[key].page == page;
        assert(key.vm == root);
        assert(exists|some: VmPageKey| #[trigger]
            middle.s2_map.contains_key(some) && some.vm == root && middle.s2_map[some].page == page)
            by {
            let some = key;
        }
        assert forall|other: VmId| #[trigger]
            middle.all_vms.contains(other) && other
                != root implies !middle.iommu_private_pages[other].contains(page) by {
            assert(post.state.zones[other.0].iommu_mem_set.empty());
        }
    }
    let restoration = if middle.all_vms.contains(root) {
        lemma_make_region_private(middle, root, region, post.view().s2_shared_pages)
    } else {
        assert forall|page: PhysPage| #[trigger]
            region.pages().contains(page) implies !middle.s2_shared_pages.contains(page)
            || post.view().s2_shared_pages.contains(page) by {
            if middle.s2_shared_pages.contains(page) && !post.view().s2_shared_pages.contains(
                page,
            ) {
                let key = choose|key: VmPageKey| #[trigger]
                    middle.s2_map.contains_key(key) && key.vm == root && middle.s2_map[key].page
                        == page;
                assert(middle.all_vms.contains(key.vm));
            }
        }
        (middle, Seq::empty())
    };
    let target = restoration.0;
    assert(target.s2_map == post.view().s2_map);
    assert(target.all_vms == post.view().all_vms);
    assert(target.iommu_private_pages == post.view().iommu_private_pages);
    assert(target.iommu_shared_pages == post.view().iommu_shared_pages);
    assert(target.iommu_s2_map == post.view().iommu_s2_map);
    assert(target.s2_shared_pages =~= middle.s2_shared_pages.difference(
        region.pages().difference(post.view().s2_shared_pages),
    )) by {
        if middle.all_vms.contains(root) {
            assert(target == shared_pages_made_private(
                middle,
                root,
                region,
                post.view().s2_shared_pages,
            ));
        } else {
            assert(target == middle);
            assert(forall|page: PhysPage| #[trigger]
                region.pages().contains(page) ==> !middle.s2_shared_pages.contains(page)
                    || post.view().s2_shared_pages.contains(page));
        }
    }
    assert(middle.s2_shared_pages.difference(region.pages().difference(post.view().s2_shared_pages))
        =~= post.view().s2_shared_pages) by {
        assert forall|page: PhysPage| #[trigger]
            middle.s2_shared_pages.difference(
                region.pages().difference(post.view().s2_shared_pages),
            ).contains(page) <==> post.view().s2_shared_pages.contains(page) by {
            if post.view().s2_shared_pages.contains(page) {
                let (other, stored) = choose|other: nat, stored: MemoryRegion|
                    #![trigger post.state.shared_regions[other].contains(stored)]
                    post.state.zone_ids.contains(other) && post.state.shared_regions.contains_key(
                        other,
                    ) && post.state.shared_regions[other].contains(stored) && region_pages(
                        stored,
                    ).contains(page);
                assert(pre.state.shared_regions[other].contains(stored));
                if region.pages().contains(page) {
                    let i = choose|i: nat|
                        0 <= i < stored.pages && region_phys_page(stored, i) == page;
                    let key = VmPageKey::new(VmId(other), region_guest_page(stored, i));
                    lemma_region_in_memory_set_maps_entries(
                        other,
                        post.state.zones[other].cpu_mem_set,
                        stored,
                    );
                    lemma_region_to_abstract_entries(other, stored);
                    lemma_region_phys_page_linear(stored, i);
                    assert(middle.s2_map.contains_key(key));
                    assert(middle.s2_map[key].page == page);
                }
            }
            if middle.s2_shared_pages.contains(page) && (!region.pages().contains(page)
                || post.view().s2_shared_pages.contains(page)) {
                if !region.pages().contains(page) {
                    assert(pre.view().s2_shared_pages.contains(page));
                    let (other, stored) = choose|other: nat, stored: MemoryRegion|
                        #![trigger pre.state.shared_regions[other].contains(stored)]
                        pre.state.zone_ids.contains(other) && pre.state.shared_regions.contains_key(
                            other,
                        ) && pre.state.shared_regions[other].contains(stored) && region_pages(
                            stored,
                        ).contains(page);
                    if other == zid {
                        assert(stored != concrete);
                    }
                    assert(post.state.shared_regions[other].contains(stored));
                }
            }
        }
    }
    assert(target.s2_shared_pages =~= post.view().s2_shared_pages);
    assert(target.s2_private_pages =~= post.view().s2_private_pages) by {
        assert forall|owner: VmId| #[trigger]
            target.s2_private_pages.contains_key(owner) implies target.s2_private_pages[owner]
            =~= post.view().s2_private_pages[owner] by {
            if owner == root {
                assert forall|page: PhysPage| #[trigger]
                    target.s2_private_pages[owner].contains(page)
                        <==> post.view().s2_private_pages[owner].contains(page) by {
                    if target.s2_private_pages[owner].contains(page) {
                        if pre.view().s2_private_pages[owner].contains(page) {
                            assert(zone_cpu_mapped_pages(post.state.zones[root_zone_id()]).contains(
                                page,
                            ));
                        } else {
                            assert(middle.s2_shared_pages.contains(page));
                            assert(!post.view().s2_shared_pages.contains(page));
                            let key = choose|key: VmPageKey| #[trigger]
                                middle.s2_map.contains_key(key) && key.vm == root
                                    && middle.s2_map[key].page == page;
                            assert(zone_cpu_mapped_pages(post.state.zones[root_zone_id()]).contains(
                                page,
                            ));
                        }
                    }
                    if post.view().s2_private_pages[owner].contains(page) {
                        if !pre.view().s2_private_pages[owner].contains(page) {
                            assert(zone_cpu_mapped_pages(pre.state.zones[root_zone_id()]).contains(
                                page,
                            ));
                            assert(pre.view().s2_shared_pages.contains(page));
                            if region.pages().contains(page) {
                                lemma_cpu_mapped_page_has_entry(pre, root_zone_id(), page);
                                let key = choose|key: VmPageKey| #[trigger]
                                    pre.view().s2_map.contains_key(key) && key.vm == root
                                        && pre.view().s2_map[key].page == page;
                                assert(!region.entries().contains_key(key));
                                assert(middle.s2_map.contains_key(key));
                                assert(middle.s2_map[key].page == page);
                            }
                            assert(middle.s2_shared_pages.contains(page));
                        }
                    }
                }
            } else {
                assert(target.s2_private_pages[owner] =~= pre.view().s2_private_pages[owner]);
                assert forall|page: PhysPage| #[trigger]
                    pre.view().s2_private_pages[owner].contains(page)
                        <==> post.view().s2_private_pages[owner].contains(page) by {
                    if pre.view().s2_private_pages[owner].contains(page) {
                        lemma_nonroot_unshared_mapped_page_has_private_region(pre, owner.0, page);
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            pre.state.zones[owner.0].cpu_mem_set.regions.contains(stored)
                                && region_pages(stored).contains(page) && region_in_enclave_memory(
                                owner.0,
                                stored,
                            );
                        if owner.0 == zid {
                            assert(stored != concrete);
                        }
                        assert(post.state.zones[owner.0].cpu_mem_set.regions.contains(stored));
                        lemma_memory_set_region_page_is_mapped(
                            post.state.zones[owner.0].cpu_mem_set,
                            stored,
                            page,
                        );
                        if post.view().s2_shared_pages.contains(page) {
                            let (_, normal_region) = lemma_shared_page_has_normal_region(post, page);
                            lemma_normal_and_enclave_page_disjoint(
                                normal_region,
                                stored,
                                owner.0,
                                page,
                            );
                        }
                    }
                    if post.view().s2_private_pages[owner].contains(page) {
                        lemma_nonroot_unshared_mapped_page_has_private_region(post, owner.0, page);
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            post.state.zones[owner.0].cpu_mem_set.regions.contains(stored)
                                && region_pages(stored).contains(page) && region_in_enclave_memory(
                                owner.0,
                                stored,
                            );
                        assert(pre.state.zones[owner.0].cpu_mem_set.regions.contains(stored));
                        lemma_memory_set_region_page_is_mapped(
                            pre.state.zones[owner.0].cpu_mem_set,
                            stored,
                            page,
                        );
                        if pre.view().s2_shared_pages.contains(page) {
                            let (_, normal_region) = lemma_shared_page_has_normal_region(pre, page);
                            lemma_normal_and_enclave_page_disjoint(
                                normal_region,
                                stored,
                                owner.0,
                                page,
                            );
                        }
                    }
                }
            }
        }
    }
    assert(target == post.view());
    lemma_run_software_ops_concat(pre.view(), middle, post.view(), seq![remove_op], restoration.1);
    (post, seq![remove_op] + restoration.1)
}

// ---------------------------------------------------------------------------
// CPU removal dispatch and enclave clear
// ---------------------------------------------------------------------------
proof fn lemma_cpu_remove_region_refines(
    pre: EnclaveSoftwareSpec,
    zid: nat,
    concrete: MemoryRegion,
) -> (result: (EnclaveSoftwareSpec, Seq<SoftwareOp>))
    requires
        pre.state.invariant(),
        pre.state.zones.contains_key(zid),
        pre.state.zones[zid].cpu_mem_set.regions.contains(concrete),
    ensures
        result.0.state.invariant(),
        EnclaveSpec::State::next_by(
            pre.state,
            result.0.state,
            EnclaveSpec::Step::cpu_remove_region(zid, concrete),
        ),
        run_software_ops(pre.view(), result.0.view(), result.1),
{
    assert(pre.state.inv_class_policy());
    if zid == root_zone_id() {
        lemma_cpu_remove_root_normal_region_refines(pre, concrete)
    } else if region_in_enclave_memory(zid, concrete) {
        lemma_cpu_remove_enclave_private_region_refines(pre, zid, concrete)
    } else {
        assert(region_in_normal_memory(concrete));
        lemma_cpu_remove_enclave_shared_region_refines(pre, zid, concrete)
    }
}

proof fn lemma_cpu_remove_region_step_refines(
    pre: EnclaveSoftwareSpec,
    post: EnclaveSoftwareSpec,
    zid: nat,
    concrete: MemoryRegion,
) -> (ops: Seq<SoftwareOp>)
    requires
        pre.state.invariant(),
        EnclaveSpec::State::next_by(
            pre.state,
            post.state,
            EnclaveSpec::Step::cpu_remove_region(zid, concrete),
        ),
    ensures
        post.state.invariant(),
        run_software_ops(pre.view(), post.view(), ops),
{
    reveal(EnclaveSpec::State::next_by);
    let trace = lemma_cpu_remove_region_refines(pre, zid, concrete);
    trace.1
}

proof fn lemma_cpu_clear_enclave_refines(pre: EnclaveSoftwareSpec, zid: nat) -> (result: (
    EnclaveSoftwareSpec,
    Seq<SoftwareOp>,
))
    requires
        pre.state.invariant(),
        pre.state.zones.contains_key(zid),
        zid != root_zone_id(),
    ensures
        result.0.state.invariant(),
        result.0.state.zone_ids == pre.state.zone_ids,
        result.0.state.zones == pre.state.zones.insert(zid, pre.state.zones[zid].cpu_clear()),
        result.0.state.enclave_private_regions_view == pre.state.enclave_private_regions_view,
        result.0.state.shared_regions == pre.state.shared_regions.insert(zid, Set::empty()),
        run_software_ops(pre.view(), result.0.view(), result.1),
    decreases pre.state.zones[zid].cpu_mem_set.regions.len(),
{
    let regions = pre.state.zones[zid].cpu_mem_set.regions;
    if regions.len() == 0 {
        regions.lemma_len0_is_empty();
        let mem_set = pre.state.zones[zid].cpu_mem_set;
        assert(pre.state.zones[zid].wf());
        assert(mem_set.mappings =~= Map::<SpecVAddr, SpecFrame>::empty()) by {
            assert forall|vaddr: SpecVAddr| !mem_set.mappings.contains_key(vaddr) by {
                if mem_set.mappings.contains_key(vaddr) {
                    let frame = mem_set.mappings[vaddr];
                    assert(mem_set.mappings.contains_pair(vaddr, frame));
                    let (stored, i) = choose|stored: MemoryRegion, i: nat|
                        mem_set.regions.contains(stored) && 0 <= i < stored.pages && vaddr
                            == stored.spec_page_vaddr(i) && frame == stored.spec_frame(i);
                    assert(false);
                }
            }
        }
        assert(pre.state.zones[zid].cpu_clear() == pre.state.zones[zid]);
        assert(pre.state.shared_regions[zid] == Set::<MemoryRegion>::empty()) by {
            assert(pre.state.shared_regions[zid] == live_shared_regions(zid, pre.state.zones[zid]));
        }
        assert(pre.state.shared_regions.insert(zid, Set::empty()) == pre.state.shared_regions);
        (pre, Seq::empty())
    } else {
        let concrete = regions.choose();
        let first = lemma_cpu_remove_region_refines(pre, zid, concrete);
        let middle = first.0;
        reveal(EnclaveSpec::State::next_by);
        assert(middle.state.zone_ids == pre.state.zone_ids);
        assert(middle.state.zones == pre.state.zones.insert(
            zid,
            pre.state.zones[zid].cpu_remove_region(concrete),
        ));
        assert(middle.state.enclave_private_regions_view == pre.state.enclave_private_regions_view);
        assert(middle.state.shared_regions == pre.state.shared_regions.insert(
            zid,
            live_shared_regions(zid, pre.state.zones[zid].cpu_remove_region(concrete)),
        ));
        vstd::set::axiom_set_remove_len(regions, concrete);
        let rest = lemma_cpu_clear_enclave_refines(middle, zid);
        let post = rest.0;
        assert(post.state.zones == pre.state.zones.insert(zid, pre.state.zones[zid].cpu_clear()));
        assert(post.state.enclave_private_regions_view == pre.state.enclave_private_regions_view);
        assert(post.state.shared_regions == pre.state.shared_regions.insert(zid, Set::empty()));
        lemma_run_software_ops_concat(pre.view(), middle.view(), post.view(), first.1, rest.1);
        (post, first.1 + rest.1)
    }
}

proof fn lemma_cpu_clear_enclave_regions_step_refines(
    pre: EnclaveSoftwareSpec,
    post: EnclaveSoftwareSpec,
    zid: nat,
) -> (ops: Seq<SoftwareOp>)
    requires
        pre.state.invariant(),
        EnclaveSpec::State::next_by(
            pre.state,
            post.state,
            EnclaveSpec::Step::cpu_clear_enclave_regions(zid),
        ),
    ensures
        post.state.invariant(),
        run_software_ops(pre.view(), post.view(), ops),
{
    reveal(EnclaveSpec::State::next_by);
    let trace = lemma_cpu_clear_enclave_refines(pre, zid);
    assert(trace.0.state == post.state);
    trace.1
}

// ---------------------------------------------------------------------------
// Root IOMMU transitions
// ---------------------------------------------------------------------------
proof fn lemma_iommu_insert_region_step_refines(
    pre: EnclaveSoftwareSpec,
    post: EnclaveSoftwareSpec,
    concrete: MemoryRegion,
) -> (ops: Seq<SoftwareOp>)
    requires
        pre.state.invariant(),
        EnclaveSpec::State::next_by(
            pre.state,
            post.state,
            EnclaveSpec::Step::iommu_insert_region(concrete),
        ),
    ensures
        post.state.invariant(),
        run_software_ops(pre.view(), post.view(), ops),
{
    reveal(EnclaveSpec::State::next_by);
    let zid = root_zone_id();
    let vm = VmId(zid);
    let old_zone = pre.state.zones[zid];
    let old_set = old_zone.iommu_mem_set;
    let region = region_to_abstract(zid, concrete);
    assert(post.state.zone_ids == pre.state.zone_ids);
    assert(post.state.zones == pre.state.zones.insert(zid, old_zone.iommu_insert_region(concrete)));
    assert(post.state.enclave_private_regions_view == pre.state.enclave_private_regions_view);
    assert(post.state.shared_regions == pre.state.shared_regions);
    assert(old_zone.wf());
    old_set.lemma_insert_region_wf(concrete);
    lemma_enclave_projection_wf(pre);
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_zones_iommu_s2_entries_fresh(pre.state.zone_ids, pre.state.zones, zid, concrete);
    lemma_zones_iommu_s2_insert(pre.state.zone_ids, pre.state.zones, zid, concrete);
    lemma_memory_set_mapped_pages_insert(old_set, concrete);
    lemma_region_pages_match_enclave(concrete);
    dma_memory_is_normal_memory();
    assert(region_in_normal_memory(concrete));
    assert(region.wf());
    assert(pre.view().all_vms.contains(vm));
    assert forall|page: PhysPage, owner: VmId| #[trigger]
        region.pages().contains(page) && #[trigger] pre.view().all_vms.contains(
            owner,
        ) && owner != vm implies !pre.view().iommu_private_pages[owner].contains(page) by {
        assert(pre.state.zones[owner.0].iommu_mem_set.empty());
    }
    assert forall|page: PhysPage, owner: VmId| #[trigger]
        region.pages().contains(page) && #[trigger] pre.view().all_vms.contains(owner) && owner
            != vm implies !pre.view().s2_private_pages[owner].contains(page) by {
        if pre.view().s2_private_pages[owner].contains(page) {
            lemma_nonroot_unshared_mapped_page_has_private_region(pre, owner.0, page);
            let enclave_region = choose|stored: MemoryRegion| #[trigger]
                pre.state.zones[owner.0].cpu_mem_set.regions.contains(stored) && region_pages(
                    stored,
                ).contains(page) && region_in_enclave_memory(owner.0, stored);
            lemma_normal_and_enclave_page_disjoint(concrete, enclave_region, owner.0, page);
        }
    }
    assert(forall|page: PhysPage| #[trigger]
        region.pages().contains(page) ==> !pre.view().iommu_shared_pages.contains(page));
    assert(SoftwareView::iommu_insert_private_region_enabled(pre.view(), region));
    assert(post.view().all_vms == pre.view().all_vms);
    assert(post.view().s2_private_pages == pre.view().s2_private_pages);
    assert(post.view().s2_shared_pages == pre.view().s2_shared_pages);
    assert(post.view().s2_map == pre.view().s2_map);
    assert(post.view().iommu_shared_pages == pre.view().iommu_shared_pages);
    assert(post.view().iommu_private_pages =~= pre.view().iommu_private_pages.insert(
        vm,
        pre.view().iommu_private_pages[vm].union(region.pages()),
    )) by {
        assert forall|owner: VmId| #[trigger]
            post.view().iommu_private_pages.contains_key(
                owner,
            ) implies post.view().iommu_private_pages[owner]
            =~= pre.view().iommu_private_pages.insert(
            vm,
            pre.view().iommu_private_pages[vm].union(region.pages()),
        )[owner] by {
            if owner == vm {
                assert(zone_iommu_mapped_pages(post.state.zones[zid]) =~= zone_iommu_mapped_pages(
                    pre.state.zones[zid],
                ).union(region.pages()));
            }
        }
    }
    assert(post.view().iommu_s2_map =~= pre.view().iommu_s2_map.union_prefer_right(
        region.entries(),
    ));
    assert(SoftwareView::iommu_insert_private_region_step(pre.view(), post.view(), region));
    let op = SoftwareOp::IommuInsertPrivateRegion(region);
    assert(SoftwareView::step(pre.view(), post.view(), op));
    lemma_run_software_ops_single(pre.view(), post.view(), op);
    seq![op]
}

proof fn lemma_iommu_remove_region_refines(
    pre: EnclaveSoftwareSpec,
    concrete: MemoryRegion,
) -> (result: (EnclaveSoftwareSpec, Seq<SoftwareOp>))
    requires
        pre.state.invariant(),
        pre.state.zones.contains_key(root_zone_id()),
        pre.state.zones[root_zone_id()].iommu_mem_set.regions.contains(concrete),
    ensures
        result.0.state.invariant(),
        EnclaveSpec::State::next_by(
            pre.state,
            result.0.state,
            EnclaveSpec::Step::iommu_remove_region(concrete),
        ),
        run_software_ops(pre.view(), result.0.view(), result.1),
{
    let zid = root_zone_id();
    let vm = VmId(zid);
    let old_zone = pre.state.zones[zid];
    let old_set = old_zone.iommu_mem_set;
    let region = region_to_abstract(zid, concrete);
    let post = EnclaveSoftwareSpec {
        state: EnclaveSpec::take_step::iommu_remove_region(pre.state, concrete),
    };
    reveal(EnclaveSpec::State::next_by);
    assert(post.state.zone_ids == pre.state.zone_ids);
    assert(post.state.zones == pre.state.zones.insert(zid, old_zone.iommu_remove_region(concrete)));
    assert(post.state.enclave_private_regions_view == pre.state.enclave_private_regions_view);
    assert(post.state.shared_regions == pre.state.shared_regions);
    assert(old_zone.wf());
    old_set.lemma_remove_region_exact_wf(concrete);
    lemma_enclave_projection_wf(pre);
    lemma_region_to_abstract_pages(zid, concrete);
    lemma_region_to_abstract_entries(zid, concrete);
    lemma_region_in_memory_set_maps_entries(zid, old_set, concrete);
    lemma_zones_iommu_s2_remove(pre.state.zone_ids, pre.state.zones, zid, concrete);
    assert(region.wf());
    assert(pre.view().all_vms.contains(vm));
    assert forall|page: PhysPage| #[trigger]
        region.pages().contains(page) implies pre.view().iommu_private_pages[vm].contains(page) by {
        lemma_memory_set_region_page_is_mapped(old_set, concrete, page);
    }
    assert(abstract_region_installed(pre.view().iommu_s2_map, region));
    assert(SoftwareView::iommu_remove_private_region_enabled(pre.view(), region));
    assert(post.view().all_vms == pre.view().all_vms);
    assert(post.view().s2_private_pages == pre.view().s2_private_pages);
    assert(post.view().s2_shared_pages == pre.view().s2_shared_pages);
    assert(post.view().s2_map == pre.view().s2_map);
    assert(post.view().iommu_shared_pages == pre.view().iommu_shared_pages);
    let target_private = private_pages_after_unmap(
        pre.view().iommu_private_pages,
        post.view().iommu_s2_map,
        vm,
        region.pages(),
    );
    let post_set = post.state.zones[zid].iommu_mem_set;
    assert(post.state.inv_class_policy());
    assert(post.view().iommu_private_pages =~= target_private) by {
        assert forall|owner: VmId| #[trigger]
            post.view().iommu_private_pages.contains_key(
                owner,
            ) implies post.view().iommu_private_pages[owner] =~= target_private[owner] by {
            if owner == vm {
                assert forall|page: PhysPage| #[trigger]
                    post.view().iommu_private_pages[owner].contains(page)
                        <==> target_private[owner].contains(page) by {
                    if post.view().iommu_private_pages[owner].contains(page) {
                        lemma_memory_set_mapped_pages_iff_region_page(post_set, page);
                        let stored = choose|stored: MemoryRegion| #[trigger]
                            post_set.regions.contains(stored) && region_pages(stored).contains(page);
                        assert(stored != concrete);
                        assert(old_set.regions.contains(stored));
                        lemma_memory_set_region_page_is_mapped(old_set, stored, page);
                        if region.pages().contains(page) {
                            let i = choose|i: nat|
                                0 <= i < stored.pages && region_phys_page(stored, i) == page;
                            let key = VmPageKey::new(owner, region_guest_page(stored, i));
                            lemma_region_to_abstract_entries(zid, stored);
                            lemma_region_in_memory_set_maps_entries(zid, post_set, stored);
                            lemma_region_phys_page_linear(stored, i);
                            assert(post.view().iommu_s2_map.contains_key(key));
                            assert(post.view().iommu_s2_map[key].page == page);
                        }
                    }
                    if target_private[owner].contains(page) {
                        if !region.pages().contains(page) {
                            lemma_memory_set_mapped_pages_iff_region_page(old_set, page);
                            let stored = choose|stored: MemoryRegion| #[trigger]
                                old_set.regions.contains(stored) && region_pages(stored).contains(page);
                            assert(stored != concrete);
                            lemma_memory_set_region_page_is_mapped(
                                post.state.zones[zid].iommu_mem_set,
                                stored,
                                page,
                            );
                        } else {
                            let key = choose|key: VmPageKey| #[trigger]
                                post.view().iommu_s2_map.contains_key(key) && key.vm == owner
                                    && post.view().iommu_s2_map[key].page == page;
                            let vaddr = vaddr_of_gpa(key.gpa);
                            assert(post_set.mappings.contains_key(vaddr));
                            assert(frame_phys_page(post_set.mappings[vaddr]) == page);
                            assert(memory_set_mapped_pages(post_set).contains(page));
                        }
                    }
                }
            }
        }
    }
    assert(post.view().iommu_s2_map =~= pre.view().iommu_s2_map.remove_keys(
        region.entries().dom(),
    ));
    assert(SoftwareView::iommu_remove_private_region_step(pre.view(), post.view(), region));
    let op = SoftwareOp::IommuRemovePrivateRegion(region);
    assert(SoftwareView::step(pre.view(), post.view(), op));
    lemma_run_software_ops_single(pre.view(), post.view(), op);
    (post, seq![op])
}

proof fn lemma_iommu_remove_region_step_refines(
    pre: EnclaveSoftwareSpec,
    post: EnclaveSoftwareSpec,
    concrete: MemoryRegion,
) -> (ops: Seq<SoftwareOp>)
    requires
        pre.state.invariant(),
        EnclaveSpec::State::next_by(
            pre.state,
            post.state,
            EnclaveSpec::Step::iommu_remove_region(concrete),
        ),
    ensures
        post.state.invariant(),
        run_software_ops(pre.view(), post.view(), ops),
{
    reveal(EnclaveSpec::State::next_by);
    let trace = lemma_iommu_remove_region_refines(pre, concrete);
    trace.1
}

proof fn lemma_iommu_clear_refines(pre: EnclaveSoftwareSpec) -> (result: (
    EnclaveSoftwareSpec,
    Seq<SoftwareOp>,
))
    requires
        pre.state.invariant(),
        pre.state.zones.contains_key(root_zone_id()),
    ensures
        result.0.state.invariant(),
        result.0.state.zone_ids == pre.state.zone_ids,
        result.0.state.zones == pre.state.zones.insert(
            root_zone_id(),
            pre.state.zones[root_zone_id()].iommu_clear(),
        ),
        result.0.state.enclave_private_regions_view == pre.state.enclave_private_regions_view,
        result.0.state.shared_regions == pre.state.shared_regions,
        run_software_ops(pre.view(), result.0.view(), result.1),
    decreases pre.state.zones[root_zone_id()].iommu_mem_set.regions.len(),
{
    let zid = root_zone_id();
    let regions = pre.state.zones[zid].iommu_mem_set.regions;
    if regions.len() == 0 {
        regions.lemma_len0_is_empty();
        let mem_set = pre.state.zones[zid].iommu_mem_set;
        assert(pre.state.zones[zid].wf());
        assert(mem_set.mappings =~= Map::<SpecVAddr, SpecFrame>::empty()) by {
            assert forall|vaddr: SpecVAddr| !mem_set.mappings.contains_key(vaddr) by {
                if mem_set.mappings.contains_key(vaddr) {
                    let frame = mem_set.mappings[vaddr];
                    assert(mem_set.mappings.contains_pair(vaddr, frame));
                    let (stored, i) = choose|stored: MemoryRegion, i: nat|
                        mem_set.regions.contains(stored) && 0 <= i < stored.pages && vaddr
                            == stored.spec_page_vaddr(i) && frame == stored.spec_frame(i);
                    assert(false);
                }
            }
        }
        assert(pre.state.zones[zid].iommu_clear() == pre.state.zones[zid]);
        (pre, Seq::empty())
    } else {
        let concrete = regions.choose();
        let first = lemma_iommu_remove_region_refines(pre, concrete);
        let middle = first.0;
        reveal(EnclaveSpec::State::next_by);
        assert(middle.state.zone_ids == pre.state.zone_ids);
        assert(middle.state.zones == pre.state.zones.insert(
            zid,
            pre.state.zones[zid].iommu_remove_region(concrete),
        ));
        assert(middle.state.enclave_private_regions_view == pre.state.enclave_private_regions_view);
        assert(middle.state.shared_regions == pre.state.shared_regions);
        vstd::set::axiom_set_remove_len(regions, concrete);
        let rest = lemma_iommu_clear_refines(middle);
        let post = rest.0;
        assert(post.state.zones == pre.state.zones.insert(zid, pre.state.zones[zid].iommu_clear()));
        lemma_run_software_ops_concat(pre.view(), middle.view(), post.view(), first.1, rest.1);
        (post, first.1 + rest.1)
    }
}

proof fn lemma_iommu_clear_regions_step_refines(
    pre: EnclaveSoftwareSpec,
    post: EnclaveSoftwareSpec,
) -> (ops: Seq<SoftwareOp>)
    requires
        pre.state.invariant(),
        EnclaveSpec::State::next_by(
            pre.state,
            post.state,
            EnclaveSpec::Step::iommu_clear_regions(),
        ),
    ensures
        post.state.invariant(),
        run_software_ops(pre.view(), post.view(), ops),
{
    reveal(EnclaveSpec::State::next_by);
    let trace = lemma_iommu_clear_refines(pre);
    assert(trace.0.state == post.state);
    trace.1
}

impl super::SoftwareRefinement for EnclaveSoftwareSpec {
    type Step = EnclaveSpec::Step;

    open spec fn view(&self) -> SoftwareView {
        EnclaveSoftwareSpec::view(self)
    }

    open spec fn invariants(&self) -> bool {
        self.state.invariant()
    }

    open spec fn next(pre: Self, post: Self, step: Self::Step) -> bool {
        EnclaveSpec::State::next_by(pre.state, post.state, step)
    }

    proof fn invariants_imply_view_wf(&self) {
        lemma_enclave_projection_wf(*self);
    }

    proof fn step_refines(pre: Self, post: Self, step: Self::Step) -> (ops: Seq<SoftwareOp>) {
        match step {
            EnclaveSpec::Step::add_zone(zid) => { lemma_add_zone_step_refines(pre, post, zid)
            },
            EnclaveSpec::Step::remove_zone(zid) => {
                lemma_remove_zone_step_refines(pre, post, zid)
            },
            EnclaveSpec::Step::synchronize_enclave_private_regions_view(zid) => {
                lemma_synchronize_step_refines(pre, post, zid)
            },
            EnclaveSpec::Step::cpu_insert_normal_region(region) => {
                lemma_cpu_insert_normal_region_step_refines(pre, post, region)
            },
            EnclaveSpec::Step::cpu_insert_enclave_private_region(zid, region) => {
                lemma_cpu_insert_enclave_private_region_step_refines(pre, post, zid, region)
            },
            EnclaveSpec::Step::cpu_insert_enclave_shared_region(zid, region) => {
                lemma_cpu_insert_enclave_shared_region_step_refines(pre, post, zid, region)
            },
            EnclaveSpec::Step::cpu_remove_region(zid, region) => {
                lemma_cpu_remove_region_step_refines(pre, post, zid, region)
            },
            EnclaveSpec::Step::cpu_clear_enclave_regions(zid) => {
                lemma_cpu_clear_enclave_regions_step_refines(pre, post, zid)
            },
            EnclaveSpec::Step::iommu_insert_region(region) => {
                lemma_iommu_insert_region_step_refines(pre, post, region)
            },
            EnclaveSpec::Step::iommu_remove_region(region) => {
                lemma_iommu_remove_region_step_refines(pre, post, region)
            },
            EnclaveSpec::Step::iommu_clear_regions() => {
                lemma_iommu_clear_regions_step_refines(pre, post)
            },
            EnclaveSpec::Step::dummy_to_use_type_params(_) => {
                reveal(EnclaveSpec::State::next_by);
                assert(false);
                Seq::empty()
            },
        }
    }
}

} // verus!
