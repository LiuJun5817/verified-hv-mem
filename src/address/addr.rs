//! Address related structs, functions, and specifications.
use vstd::prelude::*;

verus! {

/// Representing virtual address.
pub struct VAddr(pub nat);

impl VAddr {
    /// If addr is aligned to `size` bytes.
    pub open spec fn aligned(self, size: nat) -> bool {
        self.0 % size == 0
    }

    /// If addr is in range `[base, base + size)`.
    pub open spec fn within(self, base: Self, size: nat) -> bool {
        base.0 <= self.0 < base.0 + size
    }

    /// If virtual region (base1, size1) and virtual region (base2, size2) overlap.
    pub open spec fn overlap(base1: Self, size1: nat, base2: Self, size2: nat) -> bool {
        overlap(base1.0, size1, base2.0, size2)
    }

    /// Offset `self` by `offset` bytes.
    pub open spec fn offset(self, offset: nat) -> VAddr {
        VAddr(self.0 + offset)
    }

    /// Convert to word index.
    pub open spec fn idx(self) -> VIdx {
        VIdx(self.0 / 8)
    }

    /// If virtual page base `vbase` maps to physical page base `pbase`, calculate the
    /// physical address that `self` maps to.
    pub open spec fn map(self, vbase: Self, pbase: PAddr) -> PAddr
        recommends
            self.0 >= vbase.0,
    {
        PAddr((self.0 - vbase.0) as nat + pbase.0)
    }
}

/// Representing physical address.
pub struct PAddr(pub nat);

impl PAddr {
    /// If addr is aligned to `size` bytes.
    pub open spec fn aligned(self, size: nat) -> bool {
        self.0 % size == 0
    }

    /// If addr is in range `[base, base + size)`.
    pub open spec fn within(self, base: Self, size: nat) -> bool {
        base.0 <= self.0 < base.0 + size
    }

    /// If physical region (base1, size1) and physical region (base2, size2) overlap.
    pub open spec fn overlap(base1: Self, size1: nat, base2: Self, size2: nat) -> bool {
        overlap(base1.0, size1, base2.0, size2)
    }

    /// Offset `self` by `offset` bytes.
    pub open spec fn offset(self, offset: nat) -> PAddr {
        PAddr(self.0 + offset)
    }

    /// Convert to word index.
    pub open spec fn idx(self) -> PIdx {
        PIdx(self.0 / 8)
    }
}

/// Index used to access virtual memory by 8-byte word.
pub struct VIdx(pub nat);

impl VIdx {
    /// Convert to virtual address.
    pub open spec fn addr(self) -> VAddr {
        VAddr(self.0 * 8)
    }

    /// Convert to int.
    pub open spec fn as_int(self) -> int {
        self.0 as int
    }
}

/// Index used to access physical memory by 8-byte word.
pub struct PIdx(pub nat);

impl PIdx {
    /// Convert to physical address.
    pub open spec fn addr(self) -> PAddr {
        PAddr(self.0 * 8)
    }

    /// Convert to int.
    pub open spec fn as_int(self) -> int {
        self.0 as int
    }
}

/// (EXEC-MODE) Physical Address.
#[derive(PartialEq, Eq, Clone, Copy)]
pub struct PAddrExec(pub usize);

impl PAddrExec {
    /// Convert to spec PAddr.
    pub open spec fn view(self) -> PAddr {
        PAddr(self.0 as nat)
    }
}

/// (EXEC-MODE) Virtual Address.
#[derive(PartialEq, Eq, Clone, Copy)]
pub struct VAddrExec(pub usize);

impl VAddrExec {
    /// Convert to spec VAddr.
    pub open spec fn view(self) -> VAddr {
        VAddr(self.0 as nat)
    }

    /// If addr is aligned to `size` bytes.
    pub fn aligned(self, size: usize) -> (res: bool)
        requires
            size > 0,
        ensures
            res == self@.aligned(size as nat),
    {
        self.0 % size == 0
    }
}

/// If region (base1, size1) and region (base2, size2) overlap.
pub open spec(checked) fn overlap(base1: nat, size1: nat, base2: nat, size2: nat) -> bool {
    if base1 <= base2 {
        base2 < base1 + size1
    } else {
        base1 < base2 + size2
    }
}

} // verus!
