//! The sync bridge: a synced `MmuSpec`/`BudgetSpec` pair projects to a `wf`
//! `MachineState`.
//!
//! This is the **point-4 payoff** of the whole forcing story.  The implementation
//! drives the per-vm `MmuSpec` slice tokens to equal the `BudgetSpec` projection
//! (the lock invariant `s2map_tok.value() == pt_s2map_inner(mappings)`), i.e. the
//! hardware-reachable map agrees with the software-maintained map.  Aggregated over
//! all vms that is [`specs_synced`]; this module lifts it through the two view
//! projections to a `wf` machine state — `MmuSpec` supplies `tlb_safe` (its
//! invariant) and the sync clause, `BudgetSpec` the ownership/sharing/translation
//! clauses.  So every state the impl forces into sync is well-formed, hence secure.
use super::view::state_s2_map;
use crate::hv_mem::spec::budget::BudgetSpec;
use crate::machine::hardware::mmu::MmuSpec;
use crate::machine::hardware::refine::flatten_s2map;
use crate::machine::hardware::HardwareOps;
use crate::machine::machine::refine::lemma_synced_views_wf;
use crate::machine::machine::MachineState;
use crate::machine::software::SoftwareOps;
use crate::machine::types::*;
use vstd::prelude::*;

verus! {

/// The MMU and budget states are *synced*: the hardware-reachable map (flattened
/// `MmuSpec.s2map`) equals the software-maintained map (`BudgetSpec`'s projection).
/// This is the per-vm lock invariant aggregated over all vms.
pub open spec fn specs_synced(mmu: MmuSpec::State, budget: BudgetSpec::State) -> bool {
    flatten_s2map(mmu.s2map) == state_s2_map(budget)
}

/// **Synced specs refine a `wf` machine.** Reachable `MmuSpec` / `BudgetSpec` states
/// that are [`specs_synced`] project (via their views) to a `wf` `MachineState`.
pub proof fn lemma_specs_synced_implies_wf_machine(mmu: MmuSpec::State, budget: BudgetSpec::State)
    requires
        mmu.invariant(),
        budget.invariant(),
        specs_synced(mmu, budget),
    ensures
        MachineState::assemble(budget.view(), mmu.view()).wf(),
{
    // Each view is internally well-formed (from its own state machine's invariant).
    budget.inv_implies_wf();
    mmu.inv_implies_wf();
    // view-sync: the two projected stage-2 maps coincide (the `specs_synced` hyp).
    assert(mmu.view().s2map == budget.view().s2_map);
    // The MMU view schedules no vm, so the scheduler clause is vacuous.
    assert(mmu.view().active_vm == Map::<CpuId, VmId>::empty());
    lemma_synced_views_wf(budget.view(), mmu.view());
}

} // verus!
