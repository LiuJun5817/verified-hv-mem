use vstd::prelude::*;
use super::addr::{PAddr, PAddrExec};

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
pub struct Frame {
    /// The base address of the frame.
    pub base: PAddr,
    /// The size of the frame in bytes.
    pub size: FrameSize,
    /// The attributes of the frame.
    pub attr: MemAttr,
}

/// (EXEC-MODE) represents a physical memory frame (Page or Block).
pub struct FrameExec {
    /// The base address of the frame.
    pub base: PAddrExec,
    /// The size of the frame in bytes.
    pub size: FrameSize,
    /// The attributes of the frame.
    pub attr: MemAttr,
}

impl FrameExec {
    /// Convert to Frame.
    pub open spec fn view(self) -> Frame {
        Frame { base: self.base@, size: self.size, attr: self.attr }
    }
}

} // verus!