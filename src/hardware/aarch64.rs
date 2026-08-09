//! AArch64 implementation of the CPU and IOMMU maintenance interfaces.
//!
//! The CPU methods execute AArch64 system instructions. The IOMMU methods are
//! placeholders that currently execute only `dsb ish`; SMMUv3 command-queue MMIO
//! support will replace them when the platform configuration is available.
use super::mmu::{HardwareInstr, MmuInstr, SmmuInstr, ZoneIdInstr};
use core::arch::asm;
use vstd::prelude::*;

verus! {

/// Zero-sized backend used as the instruction type of `MmuHardware`.
pub struct Aarch64Hw;

impl ZoneIdInstr for Aarch64Hw {
    open spec fn valid_zone_id(zone_id: usize) -> bool {
        // Jailhouse uses the architectural 8-bit VMID format.
        zone_id < 0x100
    }
}

impl MmuInstr for Aarch64Hw {
    #[verifier::external_body]
    fn issue_tlbi_s2_sync(zone_id: usize, ipa_page: usize) {
        // Select the VMID, invalidate the requested guest page, and restore the
        // previous VTTBR value. `IPAS2E1IS` takes IPA >> 12 in a register.
        unsafe {
            let old_vttbr: u64;
            asm!("mrs {old}, vttbr_el2", old = out(reg) old_vttbr);
            let target_vttbr = (old_vttbr & 0x0000_ffff_ffff_ffff) | (((zone_id as u64) & 0xff)
                << 48);
            asm!("msr vttbr_el2, {target}", target = in(reg) target_vttbr);
            asm!("isb");
            asm!("tlbi ipas2e1is, {x}", x = in(reg) ipa_page);
            asm!("dsb ish");
            asm!("msr vttbr_el2, {old}", old = in(reg) old_vttbr);
            asm!("isb");
        }
    }

    fn issue_tlbi_s2_range_sync(zone_id: usize, ipa_page: usize, _page_count: usize) {
        // Invalidating the aligned IPA of a block descriptor evicts the cached
        // block translation, regardless of its logical 4 KiB page count.
        Self::issue_tlbi_s2_sync(zone_id, ipa_page);
    }

    #[verifier::external_body]
    fn issue_dsb_ish() {
        // Order page-table writes in the inner-shareable domain.
        #[cfg(target_arch = "aarch64")]
        unsafe {
            asm!("dsb ish");
        }
    }
}

impl SmmuInstr for Aarch64Hw {
    #[verifier::external_body]
    fn issue_smmu_tlbi_s2(_zone_id: usize, _ipa_page: usize) {
        // Placeholder for an SMMUv3 CMD_TLBI_S2_IPA command.
        #[cfg(target_arch = "aarch64")]
        unsafe {
            asm!("dsb ish");
        }
    }

    fn issue_smmu_tlbi_s2_range(zone_id: usize, ipa_page: usize, _page_count: usize) {
        // Placeholder backend preserving the block-base contract expected by
        // a future SMMUv3 CMD_TLBI_S2_IPA implementation.
        Self::issue_smmu_tlbi_s2(zone_id, ipa_page);
    }

    #[verifier::external_body]
    fn issue_smmu_sync() {
        // Placeholder for an SMMUv3 CMD_SYNC command and completion wait.
        #[cfg(target_arch = "aarch64")]
        unsafe {
            asm!("dsb ish");
        }
    }
}

impl HardwareInstr for Aarch64Hw {

}

} // verus!
