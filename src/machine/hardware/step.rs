use vstd::prelude::*;

use super::HardwareView;
use crate::machine::types::*;

verus! {

// ---------------------------------------------------------------------------
// Hardware-only state transitions
//
// Each `*_step` predicate relates two `HardwareView` snapshots.  `s1` is the
// pre-state; `s2` is the post-state.  Software state (`SoftwareView`) is absent —
// cross-cutting effects that span both views are composed in
// `refinement::machine`.
// ---------------------------------------------------------------------------
impl HardwareView {
    /// Hardware MMU silently fills the TLB with a hardware-reachable stage-2 entry.
    ///
    /// The fill reads `s1.s2map` (the walker-reachable map), so it can never cache a
    /// translation the walker cannot reach.
    pub open spec fn tlb_fill_step(
        s1: HardwareView,
        s2: HardwareView,
        cpu: CpuId,
        vm: VmId,
        gpa: GuestPage,
    ) -> bool {
        let tkey = TlbKey::new(cpu, vm, gpa);
        let skey = VmPageKey::new(vm, gpa);
        &&& s1.active_vm.contains_key(cpu) && s1.active_vm[cpu] == vm
        &&& s1.s2map.contains_key(skey)
        &&& s2.s2map == s1.s2map
        &&& s2.active_vm == s1.active_vm
        &&& s2.memory == s1.memory
        &&& s2.tlb == s1.tlb.insert(
            tkey,
            TlbEntry {
                page: s1.s2map[skey].page,
                access: s1.s2map[skey].access,
                generation: s1.s2map[skey].generation,
            },
        )
    }

    /// Atomic break-before-make unmap: drop `(vm, gpa)` from the hardware-reachable
    /// map **and** flush its cached TLB entries together.
    ///
    /// This bundles the completing `DSB ISH` (which makes the invalid PTE
    /// walker-visible, dropping the page from `s2map`) with the `TLBI IPAS2E1IS`
    /// broadcast (which clears the stale cached entries).  Bundling them keeps
    /// `tlb_safe` inductive: there is no intermediate state in which the page has
    /// left `s2map` while a cached entry survives.  Mirrors `MmuSpec.unmap_invalidate`.
    pub open spec fn unmap_invalidate_step(
        s1: HardwareView,
        s2: HardwareView,
        vm: VmId,
        gpa: GuestPage,
    ) -> bool {
        let skey = VmPageKey::new(vm, gpa);
        let targets = Set::new(|key: TlbKey| key.vm == vm && key.gpa == gpa);
        &&& s2.s2map == s1.s2map.remove(skey)
        &&& s2.tlb == s1.tlb.remove_keys(targets)
        &&& s2.active_vm == s1.active_vm
        &&& s2.memory == s1.memory
    }

    /// The map-side `DSB ISH`: make a freshly written PTE walker-reachable by adding
    /// `(vm, gpa) => entry` to the hardware-reachable map.  No `TLBI` — break-before-
    /// make on the map side needs none (the page was absent, so it had no cached
    /// entry), so the TLB is untouched.  Mirrors `MmuSpec.map`.
    pub open spec fn map_step(
        s1: HardwareView,
        s2: HardwareView,
        vm: VmId,
        gpa: GuestPage,
        entry: S2Entry,
    ) -> bool {
        let skey = VmPageKey::new(vm, gpa);
        // Break-before-make on the map side: the page must be currently unreachable,
        // so (by `tlb_safe`) it has no stale cached entry to disagree with `entry`.
        &&& !s1.s2map.contains_key(skey)
        &&& s2.s2map == s1.s2map.insert(skey, entry)
        &&& s2.tlb == s1.tlb
        &&& s2.active_vm == s1.active_vm
        &&& s2.memory == s1.memory
    }

    /// Schedule `vm` onto `cpu`.
    ///
    /// On AArch64: writing `VTTBR_EL2` before `ERET`.
    pub open spec fn context_switch_step(
        s1: HardwareView,
        s2: HardwareView,
        cpu: CpuId,
        vm: VmId,
    ) -> bool {
        &&& s2.active_vm == s1.active_vm.insert(cpu, vm)
        &&& s2.tlb == s1.tlb
        &&& s2.s2map == s1.s2map
        &&& s2.memory == s1.memory
    }

    /// Data Synchronization Barrier — no observable state change.
    ///
    /// The ordering guarantee is captured by the barrier consistency predicate
    /// in `machine::machine`; at the state-machine level DSB is a no-op.
    pub open spec fn dsb_step(s1: HardwareView, s2: HardwareView) -> bool {
        s2 == s1
    }

    /// Instruction Synchronization Barrier — no observable state change.
    pub open spec fn isb_step(s1: HardwareView, s2: HardwareView) -> bool {
        s2 == s1
    }

    /// Hardware reads a physical memory word (a backed address; no state change).
    pub open spec fn mem_read_step(s1: HardwareView, s2: HardwareView, pa: PhysWordAddr) -> bool {
        &&& s1.memory.contains_key(pa)
        &&& s2 == s1
    }

    /// Hardware writes `value` to a physical memory word.
    pub open spec fn mem_write_step(
        s1: HardwareView,
        s2: HardwareView,
        pa: PhysWordAddr,
        value: DataWord,
    ) -> bool {
        &&& s2.tlb == s1.tlb
        &&& s2.s2map == s1.s2map
        &&& s2.active_vm == s1.active_vm
        &&& s2.memory == s1.memory.insert(pa, value)
    }
}

} // verus!
