use vstd::prelude::*;

use crate::machine::types::*;

verus! {

/// Machine-vocabulary description of a contiguous region assigned to a VM: the
/// region-granular argument of `insert_region` / `remove_region`.
///
/// Region page `i` backs physical page `phys_base + i` and guest page
/// `gpa_base + i`, all sharing one `access` and generation `0`.
#[derive(PartialEq, Eq, Structural, Copy, Clone)]
pub struct Region {
    /// Owning VM.
    pub vm: VmId,
    /// First guest page (page units).
    pub gpa_base: nat,
    /// First physical page (page units).
    pub phys_base: nat,
    /// Number of pages.
    pub count: nat,
    /// Uniform access permissions for the whole region.
    pub access: AccessPerms,
}

impl Region {
    /// Guest page of region page `i`.
    pub open spec fn guest_page(self, i: nat) -> GuestPage {
        GuestPage((self.gpa_base + i) as nat)
    }

    /// Physical page of region page `i`.
    pub open spec fn phys_page(self, i: nat) -> PhysPage {
        PhysPage((self.phys_base + i) as nat)
    }

    /// Physical pages backed by the region.
    pub open spec fn pages(self) -> Set<PhysPage> {
        Set::new(|p: PhysPage| self.phys_base <= p.0 < self.phys_base + self.count)
    }

    /// Stage-2 entries installed by the region: one per guest page.
    pub open spec fn entries(self) -> Map<VmPageKey, S2Entry> {
        Map::new(
            |k: VmPageKey| k.vm == self.vm && self.gpa_base <= k.gpa.0 < self.gpa_base + self.count,
            |k: VmPageKey|
                S2Entry {
                    page: PhysPage((self.phys_base + k.gpa.0 - self.gpa_base) as nat),
                    access: self.access,
                    generation: 0,
                },
        )
    }

    /// Well-formedness: a region spans at least one page.
    pub open spec fn wf(self) -> bool {
        self.count > 0
    }
}

} // verus!
