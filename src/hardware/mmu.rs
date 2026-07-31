//! Executable interfaces for stage-2 translation maintenance.
//!
//! [`MmuInstr`] describes CPU MMU operations and [`SmmuInstr`] describes IOMMU
//! operations. [`MmuHardware`] combines those operations with transitions of one
//! private [`MmuSpec`](crate::hardware::spec::MmuSpec) instance. `HvMem` creates
//! separate `MmuHardware` values for the CPU and IOMMU regimes.
use crate::hardware::spec::{MmuInstance, MmuSpec, MmuVmIdsToken, MmuVmState, MmuVmToken};
use crate::model::types::{GuestPage, S2Entry, VmId};
use core::marker::PhantomData;
use vstd::prelude::*;

verus! {

/// Zone-ID constraint shared by the CPU and IOMMU backends.
pub trait ZoneIdInstr {
    /// Whether the backend can represent `zone_id`.
    spec fn valid_zone_id(zone_id: usize) -> bool;
}

/// CPU stage-2 maintenance operations supplied by a platform backend.
pub trait MmuInstr: ZoneIdInstr {
    /// Invalidate one CPU stage-2 IPA for `zone_id` and wait for completion.
    /// `ipa_page` is the 4 KiB guest page number (`IPA >> 12`).
    fn issue_tlbi_s2_sync(zone_id: usize, ipa_page: usize)
        requires
            Self::valid_zone_id(zone_id),
    ;

    /// Issue the CPU-side synchronization operation used after page-table writes.
    fn issue_dsb_ish();
}

/// IOMMU stage-2 maintenance operations supplied by a platform backend.
pub trait SmmuInstr: ZoneIdInstr {
    /// Submit an IOMMU invalidation for one VM and guest page.
    fn issue_smmu_tlbi_s2(zone_id: usize, ipa_page: usize)
        requires
            Self::valid_zone_id(zone_id),
    ;

    /// Wait for previously submitted IOMMU maintenance commands.
    fn issue_smmu_sync();
}

/// A platform backend that implements both maintenance interfaces.
pub trait HardwareInstr: MmuInstr + SmmuInstr {

}

/// Concrete stage-2 hardware handle for one regime.
///
/// It owns one private state-machine instance. `HvMem` holds the VM registry token,
/// and each `Zone` holds its CPU or IOMMU VM token. The instance has no executable
/// mutable state, so operations use a shared reference to the handle.
pub struct MmuHardware<I> where I: HardwareInstr {
    /// State-machine instance used by this hardware regime.
    instance: Tracked<MmuInstance>,
    /// Phantom type parameter for the platform-specific instruction implementation.
    _phantom: PhantomData<I>,
}

impl<I: HardwareInstr> MmuHardware<I> {
    /// The `MmuSpec` instance this handle drives.
    pub closed spec fn inst_id(&self) -> InstanceId {
        self.instance@.id()
    }

    /// The handle has no mutable shard: well-formedness is structural.
    pub closed spec fn wf(&self) -> bool {
        true
    }

    /// Create a persistent MMU instance and return its empty VM registry token.
    pub fn new() -> (res: (Self, Tracked<MmuVmIdsToken>))
        ensures
            res.0.wf(),
            res.1@.instance_id() == res.0.inst_id(),
            res.1@.value() =~= Set::<VmId>::empty(),
    {
        let tracked (Tracked(inst), Tracked(vm_ids_tok), Tracked(_vms_tok)) =
            MmuSpec::Instance::initialize();
        (
            MmuHardware { instance: Tracked(inst), _phantom: PhantomData },
            Tracked(vm_ids_tok),
        )
    }

    /// Register a fresh VM and mint its empty compound shard token.
    pub proof fn add_vm(
        tracked &self,
        zone_id: usize,
        tracked registry: &mut MmuVmIdsToken,
    ) -> (tracked res: MmuVmToken)
        requires
            self.wf(),
            I::valid_zone_id(zone_id),
            old(registry).instance_id() == self.inst_id(),
            !old(registry).value().contains(VmId(zone_id as nat)),
        ensures
            self.wf(),
            registry.instance_id() == self.inst_id(),
            registry.value() == old(registry).value().insert(VmId(zone_id as nat)),
            res.instance_id() == self.inst_id(),
            res.key() == VmId(zone_id as nat),
            res.value() == MmuVmState::empty(),
            res.value().coherent(VmId(zone_id as nat)),
    {
        let tracked new_tok =
            self.instance.borrow().add_vm(VmId(zone_id as nat), registry);
        new_tok
    }

    /// Deregister a VM after both components of its shard are empty.
    pub proof fn remove_vm(
        tracked &self,
        zone_id: usize,
        tracked registry: &mut MmuVmIdsToken,
        tracked vm_tok: MmuVmToken,
    )
        requires
            self.wf(),
            I::valid_zone_id(zone_id),
            old(registry).instance_id() == self.inst_id(),
            old(registry).value().contains(VmId(zone_id as nat)),
            vm_tok.instance_id() == self.inst_id(),
            vm_tok.key() == VmId(zone_id as nat),
            vm_tok.value().s2map == Map::<GuestPage, S2Entry>::empty(),
            vm_tok.value().coherent(VmId(zone_id as nat)),
        ensures
            self.wf(),
            registry.instance_id() == self.inst_id(),
            registry.value() == old(registry).value().remove(VmId(zone_id as nat)),
    {
        assert(vm_tok.value().tlb =~= Map::<crate::model::types::TlbKey, crate::model::types::TlbEntry>::empty()) by {
            assert forall|key: crate::model::types::TlbKey|
                !vm_tok.value().tlb.contains_key(key) by {
                if vm_tok.value().tlb.contains_key(key) {
                    assert(vm_tok.value().s2map.contains_key(key.gpa));
                }
            }
        };
        assert(vm_tok.value() == MmuVmState::empty());
        self.instance.borrow().remove_vm(VmId(zone_id as nat), registry, vm_tok);
    }

    // ── CPU MMU operations ───────────────────────────────────────────────────────
    /// Synchronize a removed CPU mapping, invalidate its IPA, and update the VM
    /// token. `ipa_page` is the 4 KiB guest page number.
    pub fn unmap_dsb_tlbi(
        &self,
        vm_tok: Tracked<MmuVmToken>,
        ipa_page: usize,
        zone_id: usize,
    ) -> (res: Tracked<MmuVmToken>)
        requires
            self.wf(),
            I::valid_zone_id(zone_id),
            vm_tok@.instance_id() == self.inst_id(),
            vm_tok@.key() == VmId(zone_id as nat),
            vm_tok@.value().coherent(VmId(zone_id as nat)),
        ensures
            self.wf(),
            res@.instance_id() == self.inst_id(),
            res@.key() == VmId(zone_id as nat),
            res@.value().s2map
                == vm_tok@.value().s2map.remove(GuestPage(ipa_page as nat)),
            res@.value().tlb == vm_tok@.value().tlb.remove_keys(
                crate::hardware::spec::invalidation_targets(
                    VmId(zone_id as nat), GuestPage(ipa_page as nat),
                ),
            ),
            res@.value().coherent(VmId(zone_id as nat)),
    {
        let ghost gpa = GuestPage(ipa_page as nat);
        let tracked vm_state = vm_tok.get();
        I::issue_dsb_ish();
        I::issue_tlbi_s2_sync(zone_id, ipa_page);
        let tracked new_tok = self.instance.borrow().unmap_invalidate(
            VmId(zone_id as nat),
            gpa,
            vm_state,
        );
        Tracked(new_tok)
    }

    /// Synchronize a new CPU mapping and add it to the VM token.
    pub fn map_dsb(
        &self,
        vm_tok: Tracked<MmuVmToken>,
        ipa_page: usize,
        zone_id: usize,
        entry: Ghost<S2Entry>,
    ) -> (res: Tracked<MmuVmToken>)
        requires
            self.wf(),
            I::valid_zone_id(zone_id),
            vm_tok@.instance_id() == self.inst_id(),
            vm_tok@.key() == VmId(zone_id as nat),
            !vm_tok@.value().s2map.contains_key(GuestPage(ipa_page as nat)),
            vm_tok@.value().coherent(VmId(zone_id as nat)),
        ensures
            self.wf(),
            res@.instance_id() == self.inst_id(),
            res@.key() == VmId(zone_id as nat),
            res@.value().s2map == vm_tok@.value().s2map.insert(
                GuestPage(ipa_page as nat), entry@,
            ),
            res@.value().tlb == vm_tok@.value().tlb,
            res@.value().coherent(VmId(zone_id as nat)),
    {
        let ghost gpa = GuestPage(ipa_page as nat);
        let tracked vm_state = vm_tok.get();
        I::issue_dsb_ish();
        let tracked new_tok = self.instance.borrow().map(
            VmId(zone_id as nat), gpa, entry@, vm_state,
        );
        Tracked(new_tok)
    }

    // ── IOMMU operations ─────────────────────────────────────────────────────────
    /// Submit and complete an IOMMU invalidation, then remove the mapping and its
    /// cached entries from the VM token.
    pub fn iommu_unmap_invalidate(
        &self,
        vm_tok: Tracked<MmuVmToken>,
        ipa_page: usize,
        zone_id: usize,
    ) -> (res: Tracked<MmuVmToken>)
        requires
            self.wf(),
            I::valid_zone_id(zone_id),
            vm_tok@.instance_id() == self.inst_id(),
            vm_tok@.key() == VmId(zone_id as nat),
            vm_tok@.value().coherent(VmId(zone_id as nat)),
        ensures
            self.wf(),
            res@.instance_id() == self.inst_id(),
            res@.key() == VmId(zone_id as nat),
            res@.value().s2map
                == vm_tok@.value().s2map.remove(GuestPage(ipa_page as nat)),
            res@.value().tlb == vm_tok@.value().tlb.remove_keys(
                crate::hardware::spec::invalidation_targets(
                    VmId(zone_id as nat), GuestPage(ipa_page as nat),
                ),
            ),
            res@.value().coherent(VmId(zone_id as nat)),
    {
        let ghost gpa = GuestPage(ipa_page as nat);
        let tracked vm_state = vm_tok.get();
        I::issue_smmu_tlbi_s2(zone_id, ipa_page);
        I::issue_smmu_sync();
        let tracked new_tok = self.instance.borrow().unmap_invalidate(
            VmId(zone_id as nat),
            gpa,
            vm_state,
        );
        Tracked(new_tok)
    }

    /// Synchronize a new IOMMU mapping and add it to the VM token.
    pub fn iommu_map_sync(
        &self,
        vm_tok: Tracked<MmuVmToken>,
        ipa_page: usize,
        zone_id: usize,
        entry: Ghost<S2Entry>,
    ) -> (res: Tracked<MmuVmToken>)
        requires
            self.wf(),
            I::valid_zone_id(zone_id),
            vm_tok@.instance_id() == self.inst_id(),
            vm_tok@.key() == VmId(zone_id as nat),
            !vm_tok@.value().s2map.contains_key(GuestPage(ipa_page as nat)),
            vm_tok@.value().coherent(VmId(zone_id as nat)),
        ensures
            self.wf(),
            res@.instance_id() == self.inst_id(),
            res@.key() == VmId(zone_id as nat),
            res@.value().s2map == vm_tok@.value().s2map.insert(
                GuestPage(ipa_page as nat), entry@,
            ),
            res@.value().tlb == vm_tok@.value().tlb,
            res@.value().coherent(VmId(zone_id as nat)),
    {
        let ghost gpa = GuestPage(ipa_page as nat);
        let tracked vm_state = vm_tok.get();
        I::issue_smmu_sync();
        let tracked new_tok = self.instance.borrow().map(
            VmId(zone_id as nat), gpa, entry@, vm_state,
        );
        Tracked(new_tok)
    }
}

} // verus!
