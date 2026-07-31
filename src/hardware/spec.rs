//! Tokenized abstract state for a stage-2 translation regime.
//!
//! VeriHyMem creates one `MmuSpec` instance for the CPU MMU and another for the
//! IOMMU. Each instance records its registered VM IDs and one [`MmuVmState`] per
//! VM. A VM state contains the translations visible to the model and that VM's
//! cached TLB entries.
//!
//! The live-VM token is stored in `HvMem`. Each zone stores its own map-sharded VM
//! token. The executable instruction interfaces are defined in `hardware::mmu`.
use crate::model::types::{CpuId, GuestPage, S2Entry, TlbEntry, TlbKey, VmId};
use verus_state_machines_macros::tokenized_state_machine;
use vstd::prelude::*;

verus! {

/// All TLB entries for one VM and guest page.
pub open spec fn invalidation_targets(vm: VmId, gpa: GuestPage) -> Set<TlbKey> {
    Set::new(|k: TlbKey| k.vm == vm && k.gpa == gpa)
}

/// All stage-2 state owned by one VM shard.
pub ghost struct MmuVmState {
    /// MMU-reachable stage-2 translations for this VM.
    pub s2map: Map<GuestPage, S2Entry>,
    /// Cached translations belonging to this VM.
    pub tlb: Map<TlbKey, TlbEntry>,
}

impl MmuVmState {
    pub open spec fn empty() -> Self {
        MmuVmState { s2map: Map::empty(), tlb: Map::empty() }
    }

    /// Every cached entry belongs to this VM and agrees with its reachable map.
    pub open spec fn coherent(&self, vm: VmId) -> bool {
        forall|key: TlbKey| #[trigger] self.tlb.contains_key(key) ==> {
            &&& key.vm == vm
            &&& self.s2map.contains_key(key.gpa)
            &&& self.tlb[key].as_s2_entry() == self.s2map[key.gpa]
        }
    }
}

} // verus!

tokenized_state_machine! {
    MmuSpec {
        fields {
            /// Registered VMs. `HvMem` holds this token under its write lock.
            #[sharding(variable)]
            pub vm_ids: Set<VmId>,

            /// Mapping and TLB state for each VM. Each zone holds its own shard.
            #[sharding(map)]
            pub vms: Map<VmId, MmuVmState>,
        }

        // ── Invariants ─────────────────────────────────────────────────────────

        /// `vm_ids` is exactly the set of VM shards.
        #[invariant]
        pub fn inv_vm_ids(&self) -> bool {
            self.vms.dom() == self.vm_ids
        }

        /// Every cached entry belongs to its VM and agrees with `s2map`.
        #[invariant]
        pub fn inv_coherent(&self) -> bool {
            forall|vm: VmId| #[trigger] self.vms.contains_key(vm)
                ==> self.vms[vm].coherent(vm)
        }

        // ── Transitions ──────────────────────────────────────────────────────────

        /// Start with no registered VMs.
        init! {
            initialize() {
                init vm_ids = Set::empty();
                init vms = Map::empty();
            }
        }

        /// Register a VM and create its empty state.
        transition! {
            add_vm(vm: VmId) {
                require !pre.vm_ids.contains(vm);
                update vm_ids = pre.vm_ids.insert(vm);
                add vms += [vm => MmuVmState::empty()];
            }
        }

        /// Deregister a VM only after both its mapping and cache are empty.
        transition! {
            remove_vm(vm: VmId) {
                remove vms -= [vm => let state];
                require state.s2map == Map::<GuestPage, S2Entry>::empty();
                require state.tlb == Map::<TlbKey, TlbEntry>::empty();
                update vm_ids = pre.vm_ids.remove(vm);
            }
        }

        /// Model a hardware TLB fill from an existing translation.
        transition! {
            fill(cpu: CpuId, vm: VmId, gpa: GuestPage) {
                remove vms -= [vm => let state];
                require state.s2map.contains_key(gpa);
                let entry = state.s2map[gpa];
                add vms += [vm => MmuVmState {
                    s2map: state.s2map,
                    tlb: state.tlb.insert(
                        TlbKey::new(cpu, vm, gpa),
                        TlbEntry { page: entry.page, access: entry.access, generation: entry.generation },
                    ),
                }];
            }
        }

        /// Remove one translation and all matching cached entries.
        transition! {
            unmap_invalidate(vm: VmId, gpa: GuestPage) {
                remove vms -= [vm => let state];
                add vms += [vm => MmuVmState {
                    s2map: state.s2map.remove(gpa),
                    tlb: state.tlb.remove_keys(invalidation_targets(vm, gpa)),
                }];
            }
        }

        /// Add a translation while leaving the TLB unchanged.
        transition! {
            map(vm: VmId, gpa: GuestPage, entry: S2Entry) {
                remove vms -= [vm => let state];
                require !state.s2map.contains_key(gpa);
                add vms += [vm => MmuVmState {
                    s2map: state.s2map.insert(gpa, entry),
                    tlb: state.tlb,
                }];
            }
        }

        // ── Inductive proofs ──────────────────────────────────────────────────────

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) {
            assert(post.vms.dom() =~= post.vm_ids);
        }

        #[inductive(add_vm)]
        fn add_vm_inductive(pre: Self, post: Self, vm: VmId) {
            assert(post.vms.dom() =~= post.vm_ids);
        }

        #[inductive(remove_vm)]
        fn remove_vm_inductive(pre: Self, post: Self, vm: VmId) {
            assert(post.vms.dom() =~= post.vm_ids);
        }

        #[inductive(fill)]
        fn fill_inductive(pre: Self, post: Self, cpu: CpuId, vm: VmId, gpa: GuestPage) {
            let tkey0 = TlbKey::new(cpu, vm, gpa);
            assert forall|key: TlbKey| #[trigger] post.vms[vm].tlb.contains_key(key) implies {
                &&& key.vm == vm
                &&& post.vms[vm].s2map.contains_key(key.gpa)
                &&& post.vms[vm].tlb[key].as_s2_entry() == post.vms[vm].s2map[key.gpa]
            } by {
                if key == tkey0 { }
            };
        }

        #[inductive(unmap_invalidate)]
        fn unmap_invalidate_inductive(pre: Self, post: Self, vm: VmId, gpa: GuestPage) {
            assert(post.vms.dom() =~= post.vm_ids);
            assert forall|key: TlbKey| #[trigger] post.vms[vm].tlb.contains_key(key) implies {
                &&& key.vm == vm
                &&& post.vms[vm].s2map.contains_key(key.gpa)
                &&& post.vms[vm].tlb[key].as_s2_entry() == post.vms[vm].s2map[key.gpa]
            } by {
                assert(!invalidation_targets(vm, gpa).contains(key));
                assert(key.gpa != gpa);
            };
        }

        #[inductive(map)]
        fn map_inductive(pre: Self, post: Self, vm: VmId, gpa: GuestPage, entry: S2Entry) {
            assert(post.vms.dom() =~= post.vm_ids);
            assert forall|key: TlbKey| #[trigger] post.vms[vm].tlb.contains_key(key) implies {
                &&& key.vm == vm
                &&& post.vms[vm].s2map.contains_key(key.gpa)
                &&& post.vms[vm].tlb[key].as_s2_entry() == post.vms[vm].s2map[key.gpa]
            } by {
                assert(pre.vms[vm].s2map.contains_key(key.gpa));
                assert(key.gpa != gpa);
            };
        }
    }
}

// ── Token type aliases ─────────────────────────────────────────────────────────

/// `MmuSpec` instance token (shared by reference).
pub type MmuInstance = MmuSpec::Instance;

/// The live-VM registry token (variable-sharded; held under `HvMem`'s write lock).
pub type MmuVmIdsToken = MmuSpec::vm_ids;

/// One VM's complete MMU state token (map-sharded; held under that zone's lock).
pub type MmuVmToken = MmuSpec::vms;
