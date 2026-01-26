use super::addr::{PAddr, SpecPAddr, SpecVAddr, VAddr};
use vstd::prelude::*;

verus! {

/// Page & Block size supported by VMSA-v8.
///
/// - For 4KB granule, support: 4K, 2M, 1G, 512G.
/// - For 16KB granule, support: 16K, 32M, 64G.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum FrameSize {
    /// 4 KiB
    Size4K,
    /// 16 KiB
    Size16K,
    /// 2 MiB
    Size2M,
    /// 32 MiB
    Size32M,
    /// 1 GiB
    Size1G,
    /// 64 GiB
    Size64G,
    /// 512 GiB
    Size512G,
}

impl FrameSize {
    /// Convert to nat.
    pub open spec fn as_nat(self) -> nat {
        match self {
            FrameSize::Size4K => 0x1000,
            FrameSize::Size16K => 0x4000,
            FrameSize::Size2M => 0x200000,
            FrameSize::Size32M => 0x2000000,
            FrameSize::Size1G => 0x40000000,
            FrameSize::Size64G => 0x1000000000,
            FrameSize::Size512G => 0x8000000000,
        }
    }

    /// Convert to usize.
    pub const fn as_usize(self) -> (res: usize)
        ensures
            self.as_nat() == res as nat,
    {
        match self {
            FrameSize::Size4K => 0x1000,
            FrameSize::Size16K => 0x4000,
            FrameSize::Size2M => 0x200000,
            FrameSize::Size32M => 0x2000000,
            FrameSize::Size1G => 0x40000000,
            FrameSize::Size64G => 0x1000000000,
            FrameSize::Size512G => 0x8000000000,
        }
    }
}

/// Frame attributes. Defination consistent with `hvisor::memory::MemFlags`.
#[derive(PartialEq, Eq, Clone, Copy)]
pub struct MemAttr {
    /// Whether the memory is readable.
    pub readable: bool,
    /// Whether the memory is writable.
    pub writable: bool,
    /// Whether the memory is executable.
    pub executable: bool,
    /// Whether the memory is user accessible.
    pub user_accessible: bool,
    /// Whether the memory is used for device mapping.
    pub device: bool,
}

impl MemAttr {
    /// Constructor.
    pub fn new(
        readable: bool,
        writable: bool,
        executable: bool,
        user_accessible: bool,
        device: bool,
    ) -> (res: Self)
        ensures
            res == Self::spec_new(readable, writable, executable, user_accessible, device),
    {
        Self { readable, writable, executable, user_accessible, device }
    }

    /// Spec-mode constructor.
    pub open spec fn spec_new(
        readable: bool,
        writable: bool,
        executable: bool,
        user_accessible: bool,
        device: bool,
    ) -> Self {
        Self { readable, writable, executable, user_accessible, device }
    }

    /// Default attributes for a frame.
    ///
    /// readable/writable/executable/user_accessible/non-device.
    pub fn default() -> (res: Self)
        ensures
            res == Self::spec_default(),
    {
        Self::new(true, true, true, true, false)
    }

    /// Spec-mode default attributes for a frame.
    ///
    /// readable/writable/executable/user_accessible/non-device.
    pub open spec fn spec_default() -> Self {
        Self::spec_new(true, true, true, true, false)
    }
}

/// Represents a physical memory frame (Page or Block).
pub struct SpecFrame {
    /// The base address of the frame.
    pub base: SpecPAddr,
    /// The size of the frame in bytes.
    pub size: FrameSize,
    /// The attributes of the frame.
    pub attr: MemAttr,
}

/// (EXEC-MODE) represents a physical memory frame (Page or Block).
pub struct Frame {
    /// The base address of the frame.
    pub base: PAddr,
    /// The size of the frame in bytes.
    pub size: FrameSize,
    /// The attributes of the frame.
    pub attr: MemAttr,
}

impl Frame {
    /// Convert to Frame.
    pub open spec fn view(self) -> SpecFrame {
        SpecFrame { base: self.base@, size: self.size, attr: self.attr }
    }
}

/// Page size in bytes (4KB).
pub const PAGE_SIZE: usize = 0x1000;

/// A memory region represents a contiguous range of virtual addresses with specific properties.
pub struct MemoryRegion {
    /// The starting virtual address of the region.
    pub start: VAddr,
    /// The number of 4KB pages in the region.
    pub pages: usize,
    /// The memory attributes of the region.
    pub attr: MemAttr,
    /// The mapping strategy for the region.
    pub mapper: Mapper,
}

impl MemoryRegion {
    /// Spec-mode validation check.
    pub open spec fn spec_valid(self) -> bool {
        &&& 0 < self.pages <= usize::MAX / PAGE_SIZE
        &&& self.start@.aligned(PAGE_SIZE as nat)
        &&& self.start@.0 <= usize::MAX as nat - (self.pages as nat * PAGE_SIZE as nat)
        &&& self.mapper.valid(self.start@.0 + (self.pages as nat * PAGE_SIZE as nat))
    }

    /// Check if the region is within valid virtual address space.
    pub fn valid(&self) -> (res: bool)
        ensures
            res == self.spec_valid(),
    {
        if self.pages == 0 || self.pages > usize::MAX / PAGE_SIZE {
            return false;
        }
        if !self.start.aligned(PAGE_SIZE) {
            return false;
        }
        if self.start.0 > usize::MAX - self.pages * PAGE_SIZE {
            return false;
        }
        match self.mapper {
            Mapper::Offset(off) => {
                let max_vaddr = self.start.0 + self.pages * PAGE_SIZE;
                off <= usize::MAX - max_vaddr && off % PAGE_SIZE == 0
            },
            Mapper::Fixed(paddr) => paddr % PAGE_SIZE == 0,
        }
    }

    /// Calculate the end virtual address of the region.
    pub fn end(&self) -> (res: VAddr)
        requires
            self.spec_valid(),
        ensures
            res@ == self.start@.offset(self.pages as nat * PAGE_SIZE as nat),
    {
        VAddr(self.start.0 + self.pages * PAGE_SIZE)
    }

    /// Spec-mode overlap check.
    pub open spec fn spec_overlaps(self, other: MemoryRegion) -> bool {
        SpecVAddr::overlap(
            self.start@,
            self.pages as nat * PAGE_SIZE as nat,
            other.start@,
            other.pages as nat * PAGE_SIZE as nat,
        )
    }

    /// If two regions overlap.
    pub fn overlaps(&self, other: &MemoryRegion) -> (res: bool)
        requires
            self.spec_valid(),
            other.spec_valid(),
        ensures
            res == self.spec_overlaps(*other),
    {
        if self.start.0 <= other.start.0 {
            self.start.0 + self.pages * PAGE_SIZE > other.start.0
        } else {
            other.start.0 + other.pages * PAGE_SIZE > self.start.0
        }
    }

    /// Lemma: overlaps is symmetric.
    pub proof fn lemma_overlaps_symmetric(self, other: MemoryRegion)
        requires
            self.spec_valid(),
            other.spec_valid(),
        ensures
            self.spec_overlaps(other) == other.spec_overlaps(self),
    {
    }
}

/// The mapping strategy for a memory region.
#[derive(Clone, Copy, Debug)]
pub enum Mapper {
    Offset(usize),
    Fixed(usize),
}

impl Mapper {
    pub open spec fn valid(self, max_vaddr: nat) -> bool {
        match self {
            Self::Offset(off) => off <= usize::MAX as nat - max_vaddr && off % PAGE_SIZE == 0,
            Self::Fixed(paddr) => paddr % PAGE_SIZE == 0,
        }
    }

    pub fn map(&self, vaddr: VAddr) -> (res: PAddr)
        requires
            self.valid(vaddr.0 as nat),
        ensures
            vaddr.0 % PAGE_SIZE == 0 ==> res.0 % PAGE_SIZE == 0,
    {
        match self {
            Self::Offset(off) => PAddr(vaddr.0 + *off),
            Self::Fixed(paddr) => PAddr(*paddr),
        }
    }
}

} // verus!
