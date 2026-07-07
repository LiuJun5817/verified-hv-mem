#![feature(prelude_import)]
#[macro_use]
extern crate std;
#[prelude_import]
use std::prelude::rust_2021::*;
use vstd::prelude::*;
pub mod address {
    pub mod addr {
        //! Address related structs, functions, and specifications.
        use vstd::prelude::*;
        /// Representing virtual address.
        pub struct SpecVAddr(pub nat);
        impl SpecVAddr {}
        /// Representing physical address.
        pub struct SpecPAddr(pub nat);
        impl SpecPAddr {}
        /// Index used to access virtual memory by 8-byte word.
        pub struct VIdx(pub nat);
        impl VIdx {}
        /// Index used to access physical memory by 8-byte word.
        pub struct PIdx(pub nat);
        impl PIdx {}
        /// (EXEC-MODE) Physical Address.
        pub struct PAddr(pub usize);
        #[automatically_derived]
        impl ::core::marker::StructuralPartialEq for PAddr {}
        #[automatically_derived]
        impl ::core::cmp::PartialEq for PAddr {
            #[inline]
            fn eq(&self, other: &PAddr) -> bool {
                self.0 == other.0
            }
        }
        #[automatically_derived]
        impl ::core::cmp::Eq for PAddr {
            #[inline]
            #[doc(hidden)]
            #[coverage(off)]
            fn assert_receiver_is_total_eq(&self) -> () {
                let _: ::core::cmp::AssertParamIsEq<usize>;
            }
        }
        #[automatically_derived]
        #[doc(hidden)]
        unsafe impl ::core::clone::TrivialClone for PAddr {}
        #[automatically_derived]
        impl ::core::clone::Clone for PAddr {
            #[inline]
            fn clone(&self) -> PAddr {
                let _: ::core::clone::AssertParamIsClone<usize>;
                *self
            }
        }
        #[automatically_derived]
        impl ::core::marker::Copy for PAddr {}
        impl PAddr {
            /// If addr is aligned to `size` bytes.
            pub fn aligned(self, size: usize) -> bool {
                self.0 % size == 0
            }
        }
        /// (EXEC-MODE) Virtual Address.
        pub struct VAddr(pub usize);
        #[automatically_derived]
        impl ::core::marker::StructuralPartialEq for VAddr {}
        #[automatically_derived]
        impl ::core::cmp::PartialEq for VAddr {
            #[inline]
            fn eq(&self, other: &VAddr) -> bool {
                self.0 == other.0
            }
        }
        #[automatically_derived]
        impl ::core::cmp::Eq for VAddr {
            #[inline]
            #[doc(hidden)]
            #[coverage(off)]
            fn assert_receiver_is_total_eq(&self) -> () {
                let _: ::core::cmp::AssertParamIsEq<usize>;
            }
        }
        #[automatically_derived]
        #[doc(hidden)]
        unsafe impl ::core::clone::TrivialClone for VAddr {}
        #[automatically_derived]
        impl ::core::clone::Clone for VAddr {
            #[inline]
            fn clone(&self) -> VAddr {
                let _: ::core::clone::AssertParamIsClone<usize>;
                *self
            }
        }
        #[automatically_derived]
        impl ::core::marker::Copy for VAddr {}
        impl VAddr {
            /// If addr is aligned to `size` bytes.
            pub fn aligned(self, size: usize) -> bool {
                self.0 % size == 0
            }
        }
    }
    pub mod frame {
        use vstd::prelude::*;
        use super::addr::{PAddr, SpecPAddr, SpecVAddr, VAddr};
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
        impl Frame {}
        /// Page & Block size supported by VMSA-v8.
        ///
        /// - For 4KB granule, support: 4K, 2M, 1G, 512G.
        /// - For 16KB granule, support: 16K, 32M, 64G.
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
        #[automatically_derived]
        #[doc(hidden)]
        unsafe impl ::core::clone::TrivialClone for FrameSize {}
        #[automatically_derived]
        impl ::core::clone::Clone for FrameSize {
            #[inline]
            fn clone(&self) -> FrameSize {
                *self
            }
        }
        #[automatically_derived]
        impl ::core::marker::Copy for FrameSize {}
        #[automatically_derived]
        impl ::core::marker::StructuralPartialEq for FrameSize {}
        #[automatically_derived]
        impl ::core::cmp::PartialEq for FrameSize {
            #[inline]
            fn eq(&self, other: &FrameSize) -> bool {
                let __self_discr = ::core::intrinsics::discriminant_value(self);
                let __arg1_discr = ::core::intrinsics::discriminant_value(other);
                __self_discr == __arg1_discr
            }
        }
        #[automatically_derived]
        impl ::core::cmp::Eq for FrameSize {
            #[inline]
            #[doc(hidden)]
            #[coverage(off)]
            fn assert_receiver_is_total_eq(&self) -> () {}
        }
        impl FrameSize {
            /// Convert to usize.
            pub const fn as_usize(self) -> usize {
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
        #[automatically_derived]
        impl ::core::marker::StructuralPartialEq for MemAttr {}
        #[automatically_derived]
        impl ::core::cmp::PartialEq for MemAttr {
            #[inline]
            fn eq(&self, other: &MemAttr) -> bool {
                self.readable == other.readable && self.writable == other.writable
                    && self.executable == other.executable
                    && self.user_accessible == other.user_accessible
                    && self.device == other.device
            }
        }
        #[automatically_derived]
        impl ::core::cmp::Eq for MemAttr {
            #[inline]
            #[doc(hidden)]
            #[coverage(off)]
            fn assert_receiver_is_total_eq(&self) -> () {
                let _: ::core::cmp::AssertParamIsEq<bool>;
            }
        }
        #[automatically_derived]
        #[doc(hidden)]
        unsafe impl ::core::clone::TrivialClone for MemAttr {}
        #[automatically_derived]
        impl ::core::clone::Clone for MemAttr {
            #[inline]
            fn clone(&self) -> MemAttr {
                let _: ::core::clone::AssertParamIsClone<bool>;
                *self
            }
        }
        #[automatically_derived]
        impl ::core::marker::Copy for MemAttr {}
        impl MemAttr {
            /// Constructor.
            pub fn new(
                readable: bool,
                writable: bool,
                executable: bool,
                user_accessible: bool,
                device: bool,
            ) -> Self {
                Self {
                    readable,
                    writable,
                    executable,
                    user_accessible,
                    device,
                }
            }
            /// Default attributes for a frame.
            ///
            /// readable/writable/executable/user_accessible/non-device.
            pub fn default() -> Self {
                Self::new(true, true, true, true, false)
            }
        }
        /// Memory type tags consistent with HvConfigMemoryRegion.mem_type.
        pub enum MemType {
            Ram,
            Io,
            VirtIo,
        }
        #[automatically_derived]
        #[doc(hidden)]
        unsafe impl ::core::clone::TrivialClone for MemType {}
        #[automatically_derived]
        impl ::core::clone::Clone for MemType {
            #[inline]
            fn clone(&self) -> MemType {
                *self
            }
        }
        #[automatically_derived]
        impl ::core::marker::Copy for MemType {}
        #[automatically_derived]
        impl ::core::marker::StructuralPartialEq for MemType {}
        #[automatically_derived]
        impl ::core::cmp::PartialEq for MemType {
            #[inline]
            fn eq(&self, other: &MemType) -> bool {
                let __self_discr = ::core::intrinsics::discriminant_value(self);
                let __arg1_discr = ::core::intrinsics::discriminant_value(other);
                __self_discr == __arg1_discr
            }
        }
        #[automatically_derived]
        impl ::core::cmp::Eq for MemType {
            #[inline]
            #[doc(hidden)]
            #[coverage(off)]
            fn assert_receiver_is_total_eq(&self) -> () {}
        }
        impl MemType {
            /// Convert to MemAttr.
            ///
            /// TODO: need further check.
            pub fn to_attr(&self) -> MemAttr {
                match self {
                    MemType::Ram => MemAttr::new(true, true, true, true, false),
                    MemType::Io => MemAttr::new(true, true, false, true, true),
                    MemType::VirtIo => MemAttr::new(true, true, false, true, true),
                }
            }
        }
    }
    pub mod region {
        use vstd::prelude::*;
        use super::{
            addr::{PAddr, SpecPAddr, SpecVAddr, VAddr},
            frame::MemAttr,
        };
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
            /// Check if the region is within valid virtual address space.
            pub fn valid(&self) -> bool {
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
                    Mapper::Offset(off) => off % PAGE_SIZE == 0,
                    Mapper::Fixed(paddr) => paddr % PAGE_SIZE == 0,
                }
            }
            /// Calculate the end virtual address of the region.
            pub fn end(&self) -> VAddr {
                VAddr(self.start.0 + self.pages * PAGE_SIZE)
            }
            /// If two regions overlap in virtual address space.
            pub fn overlaps_vmem(&self, other: &MemoryRegion) -> bool {
                if self.start.0 <= other.start.0 {
                    self.start.0 + self.pages * PAGE_SIZE > other.start.0
                } else {
                    other.start.0 + other.pages * PAGE_SIZE > self.start.0
                }
            }
            /// If two regions overlap in physical address space.
            pub fn overlaps_pmem(&self, other: &MemoryRegion) -> bool {
                let self_start = self.mapper.map(self.start);
                let self_end = self.mapper.map(self.end());
                let other_start = other.mapper.map(other.start);
                let other_end = other.mapper.map(other.end());
                if self_start.0 <= other_start.0 {
                    self_end.0 > other_start.0
                } else {
                    other_end.0 > self_start.0
                }
            }
        }
        /// The mapping strategy for a memory region.
        pub enum Mapper {
            Offset(usize),
            Fixed(usize),
        }
        #[automatically_derived]
        #[doc(hidden)]
        unsafe impl ::core::clone::TrivialClone for Mapper {}
        #[automatically_derived]
        impl ::core::clone::Clone for Mapper {
            #[inline]
            fn clone(&self) -> Mapper {
                let _: ::core::clone::AssertParamIsClone<usize>;
                *self
            }
        }
        #[automatically_derived]
        impl ::core::marker::Copy for Mapper {}
        #[automatically_derived]
        impl ::core::fmt::Debug for Mapper {
            #[inline]
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
                match self {
                    Mapper::Offset(__self_0) => {
                        ::core::fmt::Formatter::debug_tuple_field1_finish(
                            f,
                            "Offset",
                            &__self_0,
                        )
                    }
                    Mapper::Fixed(__self_0) => {
                        ::core::fmt::Formatter::debug_tuple_field1_finish(
                            f,
                            "Fixed",
                            &__self_0,
                        )
                    }
                }
            }
        }
        impl Mapper {
            pub fn map(&self, vaddr: VAddr) -> PAddr {
                match self {
                    Self::Offset(off) => PAddr(vaddr.0.wrapping_sub(*off)),
                    Self::Fixed(paddr) => PAddr(*paddr),
                }
            }
        }
    }
}
pub mod bitmap_allocator {
    pub mod bitmap_impl {
        use vstd::{prelude::*, seq_lib::*};
        use super::bitmap_trait::*;
        use core::ops::Range;
        pub trait BitAllocView {
            /// The bitmap has a total of CAP bits, numbered from 0 to CAP-1 inclusively.
            fn cap() -> usize;
            /// The default value. Workaround for `const fn new() -> Self`.
            fn default() -> Self
            where
                Self: Sized;
            /// Find a index not less than a given key, where the bit is free.
            fn next(&self, key: usize) -> Option<usize>;
            /// Whether there are free bits remaining
            fn any(&self) -> bool;
            /// Whether a specific bit is free
            fn test(&self, key: usize) -> bool;
            /// Finds a contiguous block of `size` free bits within the bitmap, respecting `align_log2`.
            /// Returns the base index of the found block, or `None` if no such block exists.
            fn find_contiguous(
                &self,
                capacity: usize,
                size: usize,
                align_log2: usize,
            ) -> Option<usize>;
        }
        /// Allocator of a bitmap, able to allocate / free bits.
        pub trait BitAlloc: BitAllocView {
            /// Allocate a free bit.
            fn alloc(&mut self) -> Option<usize>;
            /// Allocates a contiguous block of `size` bits with specified `align_log2` alignment.
            /// Returns `Some(base_index)` if successful, `None` if no suitable block is found.
            fn alloc_contiguous(
                &mut self,
                size: usize,
                align_log2: usize,
            ) -> Option<usize>;
            /// Free an allocated bit.
            fn dealloc(&mut self, key: usize);
            /// Mark bits in the range as val
            fn set_range_to(&mut self, range: Range<usize>, val: bool);
            /// Mark bits in the range as unallocated (available)
            fn insert(&mut self, range: Range<usize>);
            /// Reverse of insert
            fn remove(&mut self, range: Range<usize>);
        }
        /// Represents a 16-bit bitmap allocator.
        pub struct BitAlloc16 {
            pub bits: u16,
        }
        #[automatically_derived]
        #[doc(hidden)]
        unsafe impl ::core::clone::TrivialClone for BitAlloc16 {}
        #[automatically_derived]
        impl ::core::clone::Clone for BitAlloc16 {
            #[inline]
            fn clone(&self) -> BitAlloc16 {
                let _: ::core::clone::AssertParamIsClone<u16>;
                *self
            }
        }
        #[automatically_derived]
        impl ::core::marker::Copy for BitAlloc16 {}
        /// Implement the bit allocator by segment tree algorithm.
        pub struct BitAllocCascade16<T: BitAllocView> {
            pub bitset: BitAlloc16,
            pub sub: [T; 16],
        }
        #[automatically_derived]
        impl<T: ::core::marker::Copy + BitAllocView> ::core::marker::Copy
        for BitAllocCascade16<T> {}
        /// A bitmap of 256 bits
        pub type BitAlloc256 = BitAllocCascade16<BitAlloc16>;
        /// A bitmap of 4K bits
        pub type BitAlloc4K = BitAllocCascade16<BitAlloc256>;
        /// A bitmap of 64K bits
        pub type BitAlloc64K = BitAllocCascade16<BitAlloc4K>;
        /// A bitmap of 1M bits
        pub type BitAlloc1M = BitAllocCascade16<BitAlloc64K>;
        impl<T: BitAllocView + Copy> Clone for BitAllocCascade16<T> {
            fn clone(&self) -> Self {
                *self
            }
        }
        impl<T: BitAllocView + std::marker::Copy> BitAllocView for BitAllocCascade16<T> {
            fn cap() -> usize {
                (T::cap() * 16) as usize
            }
            /// Creates a new `BitAllocCascade16` with all bits set to 0.
            fn default() -> Self {
                BitAllocCascade16 {
                    bitset: BitAlloc16 { bits: 0 },
                    sub: [T::default(); 16],
                }
            }
            /// Checks if there are any free bits (bits set to 1) in the bitmap.
            fn any(&self) -> bool {
                self.bitset.any()
            }
            /// Tests if a specific bit at `index` is free (1) or allocated (0).
            fn test(&self, key: usize) -> bool {
                let seq_index: usize = key / T::cap();
                {};
                let bit_index: usize = key % T::cap();
                let res = self.sub[seq_index].test(bit_index);
                {};
                res
            }
            /// Finds the next free bit (1) starting from `key` (inclusive).
            /// Returns `Some(index)` of the next free bit, or `None` if no free bits are found.
            fn next(&self, key: usize) -> Option<usize> {
                let idx: usize = key / T::cap();
                {};
                {};
                let mut i = idx;
                {};
                let mut result: Option<usize> = None;
                let mut curr_key = T::cap() * idx;
                {};
                while i < 16 {
                    if self.bitset.get_bit(i as u16) {
                        let base_key = if i == idx {
                            {};
                            key - T::cap() * idx
                        } else {
                            0
                        };
                        let child = self.sub[i].next(base_key);
                        if child.is_some() {
                            {};
                            {};
                            {};
                            curr_key = T::cap() * i + child.unwrap();
                            {};
                            {};
                            {};
                            {}
                            {};
                            result = Some(curr_key);
                            {};
                            break;
                        } else {
                            {};
                            {}
                            {};
                        }
                    } else {
                        {};
                        {};
                        {}
                        {};
                        {}
                        {};
                    }
                    {};
                    let old_i = i;
                    {};
                    let next_end = T::cap() * (old_i + 1);
                    {};
                    {};
                    i += 1;
                    {};
                    {};
                    curr_key = T::cap() * i;
                    {};
                    {};
                    {};
                }
                result
            }
            /// Finds a contiguous block of `size` free bits within the bitmap, respecting `align_log2`.
            /// Returns the base index of the found block, or `None` if no such block exists.
            fn find_contiguous(
                &self,
                capacity: usize,
                size: usize,
                align_log2: usize,
            ) -> Option<usize> {
                {};
                if (capacity < (1usize << align_log2)) || !self.any() {
                    return None;
                }
                {};
                {};
                let mut base: usize = 0;
                {};
                let mut offset: usize = base;
                let mut res: Option<usize> = None;
                while offset < capacity {
                    if let Some(next) = self.next(offset) {
                        {};
                        {};
                        {};
                        {};
                        if next != offset {
                            {};
                            {};
                            {};
                            {};
                            {};
                            {};
                            {}
                            base = (((((next - 1) as usize) >> align_log2) + 1) as usize)
                                << align_log2;
                            {}
                            {};
                            {};
                            {}
                            offset = base;
                            {};
                            {};
                            {}
                            {};
                            {};
                            {}
                            continue;
                        }
                        {};
                    } else {
                        {};
                        {};
                        {}
                        return None;
                    }
                    {};
                    {};
                    offset += 1;
                    {};
                    if offset - base == size {
                        {};
                        {};
                        res = Some(base);
                        return res;
                    }
                }
                None
            }
        }
        impl<T: BitAlloc + std::marker::Copy> BitAlloc for BitAllocCascade16<T> {
            fn alloc(&mut self) -> Option<usize> {
                if !self.any() {
                    {};
                    {}
                    {};
                    {};
                    return None;
                }
                let i = self.bitset.bits.trailing_zeros() as usize;
                {};
                {};
                {}
                {};
                {};
                {}
                {};
                {};
                {};
                {};
                let mut child = self.sub[i];
                let res_is_some = child.alloc();
                self.sub[i] = child;
                {};
                {};
                let res = res_is_some.unwrap() + i * T::cap();
                let bv_old: u16 = self.bitset.bits;
                let bv_new: u16 = {
                    if self.sub[i].any() {
                        bv_old | 1u16 << i
                    } else {
                        bv_old & (!(1u16 << i))
                    }
                };
                {};
                self.bitset.bits = bv_new;
                {};
                {};
                {};
                {};
                {};
                {};
                {};
                {};
                {};
                {};
                {};
                {};
                {}
                {};
                {};
                {};
                {};
                Some(res as usize)
            }
            /// Allocates a contiguous block of `size` bits with specified `align_log2` alignment.
            /// Returns `Some(base_index)` if successful, `None` if no suitable block is found.
            fn alloc_contiguous(
                &mut self,
                size: usize,
                align_log2: usize,
            ) -> Option<usize> {
                {};
                {};
                if let Some(base) = self.find_contiguous(Self::cap(), size, align_log2) {
                    let start = base;
                    let end = base + size;
                    self.remove(start..end);
                    Some(base)
                } else {
                    None
                }
            }
            fn dealloc(&mut self, key: usize) {
                let i: usize = key / T::cap();
                {};
                let bit_index: usize = key % T::cap();
                let mut child = self.sub[i];
                child.dealloc(bit_index);
                {};
                {};
                self.sub[i] = child;
                self.bitset.set_bit(i as u16, true);
                {};
                {};
                {};
                {};
                {};
                {};
                {};
                {};
                {};
                {};
                {};
                {};
                {};
                {};
                {};
                {}
                {}
            }
            fn set_range_to(&mut self, range: Range<usize>, val: bool) {
                let st = range.start;
                let ed = range.end;
                let first = st / T::cap();
                let last = (ed - 1) / T::cap();
                let n = last + 1;
                let mut i = first;
                let mut current_end = st;
                {};
                {};
                while i < n {
                    let begin = if i == st / T::cap() { st % T::cap() } else { 0 };
                    let stop = if i == (ed - 1) / T::cap() {
                        if ed % T::cap() == 0 { T::cap() } else { ed % T::cap() }
                    } else {
                        T::cap()
                    };
                    let mut child = self.sub[i];
                    {}
                    if val {
                        child.insert(begin..stop);
                    } else {
                        child.remove(begin..stop);
                    }
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    self.sub[i] = child;
                    self.bitset.set_bit(i as u16, self.sub[i].any());
                    {};
                    {};
                    {};
                    {};
                    {}
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    current_end = stop + i * T::cap();
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    {};
                    i += 1;
                    if i == n {
                        if ed % T::cap() == 0 {
                            {};
                            {};
                        } else {
                            {};
                            {};
                        }
                    } else {
                        {};
                    }
                    {};
                }
            }
            fn insert(&mut self, range: Range<usize>) {
                self.set_range_to(range, true);
            }
            fn remove(&mut self, range: Range<usize>) {
                self.set_range_to(range, false);
            }
        }
        impl<T: BitAllocView + std::marker::Copy> BitAllocCascade16<T> {}
        impl BitAlloc16 {
            /// Gets the boolean value of a specific bit at `index`.
            fn get_bit(&self, index: u16) -> bool {
                { ((self.bits >> index as u16) & 0x1u16) == 1u16 }
            }
            /// Extracts a range of bits from the bitmap as a u16 value.
            fn get_bits(&self, range: Range<u16>) -> u16 {
                let bv_gets = {
                    let bitlen = 16u16;
                    let bits = (self.bits << (bitlen - range.end))
                        >> (bitlen - range.end);
                    bits >> range.start
                };
                {};
                bv_gets
            }
            /// Sets the boolean value of a specific bit at `index`.
            fn set_bit(&mut self, index: u16, bit: bool) {
                let bit_index: u16 = index % 16;
                let bv_old: u16 = self.bits;
                let bv_new: u16 = {
                    if bit {
                        bv_old | 1u16 << bit_index as u16
                    } else {
                        bv_old & (!(1u16 << bit_index as u16))
                    }
                };
                {};
                self.bits = bv_new;
                {};
            }
            /// Sets a range of bits in the bitmap to a given u16 value.
            fn set_bits(&mut self, range: Range<u16>, value: u16) {
                let bv_old: u16 = self.bits;
                let bv_new: u16 = {
                    let bitlen = 16;
                    let mask = !(!0u16 << (bitlen - range.end) >> (bitlen - range.end)
                        >> range.start << range.start);
                    (bv_old & mask) | (value << range.start)
                };
                {}
                self.bits = bv_new;
                {};
            }
        }
        impl BitAllocView for BitAlloc16 {
            /// The maximum capacity of the bitmap (16 bits).
            fn cap() -> usize {
                16
            }
            /// Creates a new `BitmapAllocator16` with all bits set to 0 (all free).
            fn default() -> Self {
                BitAlloc16 { bits: 0 }
            }
            /// Checks if there are any free bits (bits set to 1) in the bitmap.
            fn any(&self) -> bool {
                self.bits != 0
            }
            /// Tests if a specific bit at `index` is free (1) or allocated (0).
            fn test(&self, key: usize) -> bool {
                let res = self.get_bit(key as u16);
                res
            }
            /// Finds the next free bit (1) starting from `key` (inclusive).
            /// Returns `Some(index)` of the next free bit, or `None` if no free bits are found.
            fn next(&self, key: usize) -> Option<usize> {
                let n = u16::BITS as u16;
                let mut result = None;
                let mut i = key as u16;
                {};
                while i < n {
                    if self.get_bit(i) {
                        result = Some(i as usize);
                        break;
                    }
                    i += 1;
                }
                result
            }
            /// Finds a contiguous block of `size` free bits within the bitmap, respecting `align_log2`.
            /// Returns the base index of the found block, or `None` if no such block exists.
            fn find_contiguous(
                &self,
                capacity: usize,
                size: usize,
                align_log2: usize,
            ) -> Option<usize> {
                {};
                if (capacity < (1usize << align_log2)) || !self.any() {
                    return None;
                }
                {};
                {};
                let mut base: usize = 0;
                {};
                let mut offset: usize = base;
                let mut res: Option<usize> = None;
                while offset < capacity {
                    if let Some(next) = self.next(offset) {
                        {};
                        {};
                        {};
                        {};
                        if next != offset {
                            {};
                            {};
                            {};
                            {};
                            {};
                            {};
                            {}
                            base = (((((next - 1) as usize) >> align_log2) + 1) as usize)
                                << align_log2;
                            {}
                            {};
                            {};
                            {}
                            offset = base;
                            {};
                            {};
                            {}
                            {};
                            {};
                            {}
                            continue;
                        }
                        {};
                    } else {
                        {};
                        {};
                        {}
                        return None;
                    }
                    {};
                    {};
                    offset += 1;
                    {};
                    if offset - base == size {
                        {};
                        {};
                        res = Some(base);
                        return res;
                    }
                }
                None
            }
        }
        impl BitAlloc for BitAlloc16 {
            /// Allocates a single free bit (represented by 1) and sets it to 0 (allocated).
            /// Returns `Some(index)` if successful, `None` if no free bits are available.
            fn alloc(&mut self) -> Option<usize> {
                if !self.any() {
                    return None;
                }
                let i = self.bits.trailing_zeros() as u16;
                {};
                {};
                {}
                {};
                let bv_old: u16 = self.bits;
                let bv_new: u16 = {
                    if false { bv_old | 1u16 << i } else { bv_old & (!(1u16 << i)) }
                };
                {};
                self.bits = bv_new;
                {}
                {};
                Some(i as usize)
            }
            /// Allocates a contiguous block of `size` bits with specified `align_log2` alignment.
            /// Returns `Some(base_index)` if successful, `None` if no suitable block is found.
            fn alloc_contiguous(
                &mut self,
                size: usize,
                align_log2: usize,
            ) -> Option<usize> {
                {};
                {};
                {};
                if let Some(base) = self.find_contiguous(Self::cap(), size, align_log2) {
                    let start = base;
                    let end = base + size;
                    self.remove(start..end);
                    Some(base)
                } else {
                    None
                }
            }
            /// Deallocates a single bit at `index` by setting it to 1 (free).
            fn dealloc(&mut self, key: usize) {
                self.set_bit(key as u16, true);
                {};
                {};
            }
            /// Marks a range of bits as allocated (sets them to 0).
            fn set_range_to(&mut self, range: Range<usize>, val: bool) {
                if val {
                    self.insert(range);
                } else {
                    self.remove(range);
                }
            }
            /// Marks a range of bits as free (sets them to 1).
            fn insert(&mut self, range: Range<usize>) {
                let width = (range.end - range.start) as u16;
                {};
                let insert_val = 0xffffu16 >> ((16 - width) as u16);
                {};
                let range_u16 = (range.start as u16)..(range.end as u16);
                self.set_bits(range_u16, insert_val);
                {};
                {}
            }
            /// Marks a range of bits as allocated (sets them to 0).
            fn remove(&mut self, range: Range<usize>) {
                let value: u16 = 0;
                let width: u16 = (range.end - range.start) as u16;
                {};
                {};
                let range_u16 = (range.start as u16)..(range.end as u16);
                self.set_bits(range_u16, value);
                {};
                {}
            }
        }
        impl BitmapAllocator for BitAlloc1M {
            fn cap() -> usize {
                <Self as BitAllocView>::cap()
            }
            fn default() -> Self {
                <Self as BitAllocView>::default()
            }
            fn alloc(&mut self) -> Option<usize> {
                <Self as BitAlloc>::alloc(self)
            }
            fn alloc_contiguous(
                &mut self,
                size: usize,
                align_log2: usize,
            ) -> Option<usize> {
                <Self as BitAlloc>::alloc_contiguous(self, size, align_log2)
            }
            fn dealloc(&mut self, key: usize) {
                <Self as BitAlloc>::dealloc(self, key)
            }
            fn insert(&mut self, range: Range<usize>) {
                <Self as BitAlloc>::insert(self, range)
            }
        }
        fn main() {}
    }
    pub mod bitmap_trait {
        use vstd::{prelude::*, seq_lib::*};
        use core::ops::Range;
        /// Allocator that uses a bitmap to track resource usage (0: allocated, 1: free).
        pub trait BitmapAllocator {
            /// The bitmap has a total of CAP bits, numbered from 0 to CAP-1 inclusively.
            fn cap() -> usize;
            /// The default value. Workaround for `const fn new() -> Self`.
            fn default() -> Self
            where
                Self: Sized;
            /// Allocate a free bit.
            fn alloc(&mut self) -> Option<usize>;
            /// Allocates a contiguous block of `size` bits with specified `align_log2` alignment.
            /// Returns `Some(base_index)` if successful, `None` if no suitable block is found.
            fn alloc_contiguous(
                &mut self,
                size: usize,
                align_log2: usize,
            ) -> Option<usize>;
            /// Free an allocated bit.
            fn dealloc(&mut self, key: usize);
            /// Mark a range as free.
            fn insert(&mut self, range: Range<usize>);
        }
    }
}
pub mod global_allocator {
    //! Tokenized state machine for the global frame allocator.
    //!
    //! `AllocSpec` tracks which frame IDs belong to the free pool and which have been
    //! handed out to each client.  Using `#[sharding(map)]` on `client_sets` means
    //! every client independently holds a `AllocSpec::client_sets` token whose value
    //! is exactly the set of frames that client currently owns.  The Instance
    //! invariants (`inv_free_clients_disjoint` and `inv_clients_disjoint`) then
    //! guarantee, at the type level, that no two clients ever hold the same frame.
    use core::marker::PhantomData;
    use verus_state_machines_macros::tokenized_state_machine;
    use vstd::cell::{CellId, PCell};
    use vstd::invariant::InvariantPredicate;
    use vstd::prelude::*;
    use vstd::tokens::InstanceId;
    use crate::address::{
        addr::{PAddr, SpecPAddr},
        frame::Frame,
    };
    use crate::bitmap_allocator::{
        bitmap_trait::BitmapAllocator, bitmap_impl::BitAlloc1M,
    };
    use crate::sync::mutex::{Mutex, MutexGuard};
    /// Frame ID
    pub type FrameID = nat;
    /// Unique Identifier allocated by the global allocator.
    pub struct ClientID;
    #[allow(unused_parens)]
    pub mod AllocSpec {
        use super::*;
        use ::vstd::tokens::ValueToken;
        use ::vstd::tokens::KeyValueToken;
        use ::vstd::tokens::CountToken;
        use ::vstd::tokens::MonotonicCountToken;
        use ::vstd::tokens::ElementToken;
        use ::vstd::tokens::SimpleToken;
        pub struct State {
            pub cap: FrameID,
            pub free_set: Set<FrameID>,
            pub registered: Set<ClientID>,
            pub client_sets: ::vstd::map::Map<ClientID, Set<FrameID>>,
        }
        #[allow(non_camel_case_types)]
        pub enum Step {
            init_free_set(FrameID),
            register_client(ClientID),
            alloc(ClientID, FrameID),
            alloc_contiguous(ClientID, FrameID, FrameID),
            dealloc_contiguous(ClientID, FrameID, FrameID),
            dealloc(ClientID, FrameID),
            dummy_to_use_type_params(State),
        }
        #[allow(non_camel_case_types)]
        pub enum Config {
            initialize(FrameID),
            dummy_to_use_type_params(State),
        }
        pub mod show {
            use super::*;
            use bool as init_free_set;
            use bool as register_client;
            use bool as alloc;
            use bool as alloc_contiguous;
            use bool as dealloc_contiguous;
            use bool as dealloc;
            use bool as initialize;
        }
        pub mod take_step {
            use super::*;
            use bool as initialize;
            use bool as init_free_set;
            use bool as register_client;
            use bool as alloc;
            use bool as alloc_contiguous;
            use bool as dealloc_contiguous;
            use bool as dealloc;
        }
        #[allow(non_camel_case_types)]
        pub struct Instance {
            send_sync: ::vstd::state_machine_internal::SyncSendIfSyncSend<()>,
            state: ::core::option::Option<::vstd::prelude::Ghost<State>>,
            location: ::vstd::prelude::int,
        }
        #[allow(non_camel_case_types)]
        pub struct free_set {
            dummy_instance: Instance,
            no_copy: ::vstd::state_machine_internal::NoCopy,
        }
        impl free_set {}
        impl ::vstd::tokens::ValueToken<Set<FrameID>> for free_set {}
        impl ::vstd::tokens::UniqueValueToken<Set<FrameID>> for free_set {}
        #[allow(non_camel_case_types)]
        pub struct registered {
            dummy_instance: Instance,
            no_copy: ::vstd::state_machine_internal::NoCopy,
        }
        impl registered {}
        impl ::vstd::tokens::ValueToken<Set<ClientID>> for registered {}
        impl ::vstd::tokens::UniqueValueToken<Set<ClientID>> for registered {}
        #[allow(non_camel_case_types)]
        pub struct client_sets {
            dummy_instance: Instance,
            no_copy: ::vstd::state_machine_internal::NoCopy,
        }
        impl client_sets {}
        impl ::vstd::tokens::KeyValueToken<ClientID, Set<FrameID>> for client_sets {}
        impl ::vstd::tokens::UniqueKeyValueToken<ClientID, Set<FrameID>>
        for client_sets {}
        #[allow(type_alias_bounds)]
        #[allow(non_camel_case_types)]
        pub type client_sets_map = ::vstd::tokens::MapToken<
            ClientID,
            Set<FrameID>,
            client_sets,
        >;
        impl Instance {
            pub fn id(&self) -> ::vstd::tokens::InstanceId {
                ::core::panicking::panic("not implemented")
            }
            pub fn cap(&self) -> FrameID {
                ::core::panicking::panic("not implemented")
            }
        }
        impl ::core::clone::Clone for Instance {
            fn clone(&self) -> Self {
                ::core::panicking::panic("not implemented");
            }
        }
        impl ::core::marker::Copy for Instance {}
        impl State {}
    }
    pub type AllocInstance = AllocSpec::Instance;
    pub type FreeSetToken = AllocSpec::free_set;
    pub type RegisteredToken = AllocSpec::registered;
    pub type ClientToken = AllocSpec::client_sets;
    pub type GbAlloc = GlobalAllocator<BitAlloc1M>;
    /// Frame Size: 4 KiB (4096 bytes).
    pub const FRAME_SIZE: usize = 4096;
    /// Permission to access a 4K Frame
    pub type Frame4KPerm = vstd::simple_pptr::PointsTo<[u8; 4096]>;
    /// Ghost state held inside the allocator.
    /// Concurrent use: wrap this in a `Mutex` so only one thread can `alloc`/`dealloc`
    /// at a time.  Clients hold their own `ClientToken` independently (outside the lock).
    pub struct AllocatorState {
        pub inst: AllocInstance,
        pub free_tok: FreeSetToken,
        pub reg_tok: RegisteredToken,
        pub free_perms: Map<FrameID, Frame4KPerm>,
    }
    impl AllocatorState {}
    /// Ghost state held by a registered client.
    ///
    /// Core invariant: `client_tok.value() == frame_perms.dom()`.
    /// The `AllocSpec` Instance guarantees this set is *disjoint* from every other
    /// client's set — no external model or lock is required to prove that.
    pub struct ClientState {
        pub client_tok: ClientToken,
        pub frame_perms: Map<FrameID, Frame4KPerm>,
    }
    impl ClientState {}
    /// The tracked value stored inside the Mutex.
    ///
    /// * `allocator_state` — AllocSpec ghost tokens + free-frame physical permissions.
    /// * `bitmap_perm`  — Permission to read/write the exec bitmap via `PCell`.
    ///
    /// Holding the Mutex gives exclusive access to both.
    pub struct MutexContent<A: BitmapAllocator> {
        pub allocator_state: AllocatorState,
        pub bitmap_perm: vstd::cell::PointsTo<A>,
    }
    /// Key stored in the Mutex: pairs the AllocSpec instance ID with the PCell's
    /// identity so the mutex invariant can enforce that `bitmap_perm` belongs to
    /// `GlobalAllocator::bitmap` — eliminating the need for an external `assume`.
    pub struct AllocKey {
        pub inst_id: InstanceId,
        pub cell_id: CellId,
    }
    pub struct AllocMutexPred<A: BitmapAllocator>(PhantomData<A>);
    impl<A: BitmapAllocator> InvariantPredicate<AllocKey, MutexContent<A>>
    for AllocMutexPred<A> {}
    /// A concurrent global frame allocator implementation using a bitmap allocator and a spinlock
    /// mutex for synchronization.
    ///
    /// The state is split into two parts:
    ///
    ///   Mutex<AllocKey, MutexContent<A>, AllocMutexPred>
    ///       .allocator_state: AllocatorState   (ghost/tracked tokens)      ← protected by
    ///       .bitmap_perm:  PointsTo<A>      (PCell permission)               spinlock
    ///
    ///   PCell<A>   (exec bitmap)     ← accessed only while lock held
    ///
    /// When a thread holds the Mutex it also holds the `PointsTo<A>` token, which
    /// it uses to borrow the PCell's exec value via take()/put().
    ///
    /// Clients hold their own ClientState token completely outside the lock, so
    /// `Client::borrow_frame` is always lock-free (no CAS, no syscall).
    ///
    /// ```text
    /// Thread 0              Thread 1              Client (any thread)
    ///   alloc()               alloc()               borrow_frame()
    ///     lock ──────────┐      lock (spins)          no lock needed ✓
    ///     PCell::take()  │      ...
    ///     bitmap.alloc() │
    ///     PCell::put()   │
    ///     ghost update   │
    ///     unlock ────────┘
    ///                           lock ──────────┐
    ///                           ...            │
    ///                           unlock ────────┘
    /// ```
    pub struct GlobalAllocator<A: BitmapAllocator> {
        /// Base address of the managed physical memory region.
        pub base: PAddr,
        /// Spinlock: protects `MutexContent<A>` (ghost state + PCell permission).
        pub mutex: Mutex<AllocKey, MutexContent<A>, AllocMutexPred<A>>,
        /// Exec bitmap — write-accessed only while `mutex` is held.
        pub bitmap: PCell<A>,
    }
    impl<A: BitmapAllocator> GlobalAllocator<A> {
        /// Calculate the frame ID from a physical address.
        pub fn paddr_to_fid(&self, addr: PAddr) -> usize {
            (addr.0 - self.base.0) / FRAME_SIZE
        }
        /// Calculate the physical address from a frame ID.
        pub fn fid_to_paddr(&self, fid: usize) -> PAddr {
            PAddr(self.base.0 + fid * FRAME_SIZE)
        }
        /// Create a default allocator. The bitmap and free pool both start empty.
        pub fn default(base: PAddr) -> Self {
            let bitmap = A::default();
            let (bitmap_cell, verus_tmp_bitmap_perm) = PCell::new(bitmap);
            let key = Ghost::assume_new_fallback(|| ::core::panicking::panic(
                "internal error: entered unreachable code",
            ));
            {}
            let mutex = Mutex::new(
                key,
                Tracked::assume_new_fallback(|| ::core::panicking::panic(
                    "internal error: entered unreachable code",
                )),
            );
            let res = GlobalAllocator {
                base,
                mutex,
                bitmap: bitmap_cell,
            };
            {}
            res
        }
        /// Initialize the empty allocator by marking `[0, size)` as free.
        pub fn init(
            &self,
            size: usize,
            verus_tmp_free_perms: Tracked<Map<FrameID, Frame4KPerm>>,
        ) {
            let guard = self.mutex.lock();
            let MutexGuard { handle: handle, token: token } = guard;
            let mut bitmap = self
                .bitmap
                .take(
                    Tracked::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                );
            if size > 0 {
                bitmap.insert(0usize..size);
            }
            self.bitmap
                .put(
                    Tracked::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                    bitmap,
                );
            {}
            self.mutex
                .unlock(MutexGuard {
                    handle,
                    token: Tracked::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                });
        }
        /// Register a new client (acquires the lock briefly).
        pub fn register_client(&self) -> Tracked<ClientState> {
            let guard = self.mutex.lock();
            let MutexGuard { handle: handle, token: token } = guard;
            {}
            self.mutex
                .unlock(MutexGuard {
                    handle,
                    token: Tracked::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                });
            Tracked::assume_new_fallback(|| ::core::panicking::panic(
                "internal error: entered unreachable code",
            ))
        }
        /// Allocate one free frame and transfer ownership to `client`.
        ///
        /// Requires the free pool to be non-empty (the design assumes infinitely
        /// many physical frames exist at the model level).  The lock is held
        /// **only for the duration of this call**; clients can call `borrow_frame`
        /// at any time without any lock.
        pub fn alloc(
            &self,
            verus_tmp_client: Tracked<ClientState>,
        ) -> (PAddr, Tracked<ClientState>) {
            let guard = self.mutex.lock();
            let MutexGuard { handle: handle, token: token } = guard;
            let mut bitmap = self
                .bitmap
                .take(
                    Tracked::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                );
            {};
            let idx = bitmap.alloc().unwrap();
            self.bitmap
                .put(
                    Tracked::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                    bitmap,
                );
            {}
            let frame = self.fid_to_paddr(idx);
            self.mutex
                .unlock(MutexGuard {
                    handle,
                    token: Tracked::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                });
            (
                frame,
                Tracked::assume_new_fallback(|| ::core::panicking::panic(
                    "internal error: entered unreachable code",
                )),
            )
        }
        /// Return `frame` from `client` back to the free pool.
        pub fn dealloc(
            &self,
            verus_tmp_client: Tracked<ClientState>,
            frame: PAddr,
        ) -> Tracked<ClientState> {
            let fid = self.paddr_to_fid(frame);
            let guard = self.mutex.lock();
            let MutexGuard { handle: handle, token: token } = guard;
            let mut bitmap = self
                .bitmap
                .take(
                    Tracked::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                );
            {}
            bitmap.dealloc(fid);
            self.bitmap
                .put(
                    Tracked::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                    bitmap,
                );
            {}
            self.mutex
                .unlock(MutexGuard {
                    handle,
                    token: Tracked::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                });
            Tracked::assume_new_fallback(|| ::core::panicking::panic(
                "internal error: entered unreachable code",
            ))
        }
        /// Remove `count` frames starting at `start` from `client`
        /// and return them to the free pool.
        pub fn dealloc_contiguous(
            &self,
            verus_tmp_client: Tracked<ClientState>,
            start: PAddr,
            count: usize,
        ) -> Tracked<ClientState> {
            let start_fid = self.paddr_to_fid(start);
            let end_fid = start_fid + count;
            let guard = self.mutex.lock();
            let MutexGuard { handle: handle, token: token } = guard;
            let mut bitmap = self
                .bitmap
                .take(
                    Tracked::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                );
            bitmap.insert(start_fid..end_fid);
            self.bitmap
                .put(
                    Tracked::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                    bitmap,
                );
            {}
            self.mutex
                .unlock(MutexGuard {
                    handle,
                    token: Tracked::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                });
            Tracked::assume_new_fallback(|| ::core::panicking::panic(
                "internal error: entered unreachable code",
            ))
        }
        /// Allocate `count` contiguous free frames with `2^align_log2` frame alignment.
        pub fn alloc_contiguous(
            &self,
            verus_tmp_client: Tracked<ClientState>,
            count: usize,
            align_log2: usize,
        ) -> (PAddr, Tracked<ClientState>) {
            let guard = self.mutex.lock();
            let MutexGuard { handle: handle, token: token } = guard;
            let mut bitmap = self
                .bitmap
                .take(
                    Tracked::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                );
            let alloc_res = bitmap.alloc_contiguous(count, align_log2);
            {};
            let idx = alloc_res.unwrap();
            self.bitmap
                .put(
                    Tracked::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                    bitmap,
                );
            {}
            let frame = self.fid_to_paddr(idx);
            self.mutex
                .unlock(MutexGuard {
                    handle,
                    token: Tracked::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                });
            (
                frame,
                Tracked::assume_new_fallback(|| ::core::panicking::panic(
                    "internal error: entered unreachable code",
                )),
            )
        }
    }
    pub fn init_allocator(alloc: &GbAlloc, size: usize) {
        alloc
            .init(
                size,
                Tracked::assume_new_fallback(|| ::core::panicking::panic(
                    "internal error: entered unreachable code",
                )),
            );
    }
}
pub mod sync {
    //! Cocurrent data structures and synchronization primitives.
    pub mod mutex {
        use core::marker::PhantomData;
        use verus_state_machines_macros::tokenized_state_machine;
        use vstd::atomic_ghost::*;
        use vstd::invariant::InvariantPredicate;
        use vstd::multiset::*;
        use vstd::prelude::*;
        #[allow(unused_parens)]
        pub mod MutexToks {
            use super::*;
            use ::vstd::tokens::ValueToken;
            use ::vstd::tokens::KeyValueToken;
            use ::vstd::tokens::CountToken;
            use ::vstd::tokens::MonotonicCountToken;
            use ::vstd::tokens::ElementToken;
            use ::vstd::tokens::SimpleToken;
            pub struct State<K, V, Pred: InvariantPredicate<K, V>> {
                pub k: K,
                pub pred: PhantomData<Pred>,
                pub storage: ::core::option::Option<V>,
                pub locked: bool,
                pub owner: ::core::option::Option<()>,
                pub pending: ::vstd::multiset::Multiset<()>,
            }
            #[allow(non_camel_case_types)]
            pub enum Step<K, V, Pred: InvariantPredicate<K, V>> {
                acquire_start(),
                acquire_end(),
                release(V),
                dummy_to_use_type_params(State<K, V, Pred>),
            }
            #[allow(non_camel_case_types)]
            pub enum Config<K, V, Pred: InvariantPredicate<K, V>> {
                initialize(K, V),
                dummy_to_use_type_params(State<K, V, Pred>),
            }
            pub mod show {
                use super::*;
                use bool as acquire_start;
                use bool as acquire_end;
                use bool as release;
                use bool as initialize;
            }
            pub mod take_step {
                use super::*;
                use bool as initialize;
                use bool as acquire_start;
                use bool as acquire_end;
                use bool as release;
            }
            #[allow(non_camel_case_types)]
            pub struct Instance<K, V, Pred: InvariantPredicate<K, V>> {
                send_sync: ::vstd::state_machine_internal::SyncSendIfSyncSend<(V)>,
                state: ::core::option::Option<::vstd::prelude::Ghost<State<K, V, Pred>>>,
                location: ::vstd::prelude::int,
            }
            #[allow(non_camel_case_types)]
            pub struct locked<K, V, Pred: InvariantPredicate<K, V>> {
                dummy_instance: Instance<K, V, Pred>,
                no_copy: ::vstd::state_machine_internal::NoCopy,
            }
            impl<K, V, Pred: InvariantPredicate<K, V>> locked<K, V, Pred> {}
            impl<K, V, Pred: InvariantPredicate<K, V>> ::vstd::tokens::ValueToken<bool>
            for locked<K, V, Pred> {}
            impl<
                K,
                V,
                Pred: InvariantPredicate<K, V>,
            > ::vstd::tokens::UniqueValueToken<bool> for locked<K, V, Pred> {}
            #[allow(non_camel_case_types)]
            pub struct owner<K, V, Pred: InvariantPredicate<K, V>> {
                dummy_instance: Instance<K, V, Pred>,
                no_copy: ::vstd::state_machine_internal::NoCopy,
            }
            impl<K, V, Pred: InvariantPredicate<K, V>> owner<K, V, Pred> {}
            impl<K, V, Pred: InvariantPredicate<K, V>> ::vstd::tokens::ValueToken<()>
            for owner<K, V, Pred> {}
            impl<
                K,
                V,
                Pred: InvariantPredicate<K, V>,
            > ::vstd::tokens::UniqueValueToken<()> for owner<K, V, Pred> {}
            #[allow(non_camel_case_types)]
            pub struct pending<K, V, Pred: InvariantPredicate<K, V>> {
                dummy_instance: Instance<K, V, Pred>,
                no_copy: ::vstd::state_machine_internal::NoCopy,
            }
            impl<K, V, Pred: InvariantPredicate<K, V>> pending<K, V, Pred> {}
            impl<K, V, Pred: InvariantPredicate<K, V>> ::vstd::tokens::ElementToken<()>
            for pending<K, V, Pred> {}
            #[allow(type_alias_bounds)]
            #[allow(non_camel_case_types)]
            pub type pending_multiset<K, V, Pred: InvariantPredicate<K, V>> = ::vstd::tokens::MultisetToken<
                (),
                pending<K, V, Pred>,
            >;
            impl<K, V, Pred: InvariantPredicate<K, V>> Instance<K, V, Pred> {
                pub fn id(&self) -> ::vstd::tokens::InstanceId {
                    ::core::panicking::panic("not implemented")
                }
                pub fn k(&self) -> K {
                    ::core::panicking::panic("not implemented")
                }
                pub fn pred(&self) -> PhantomData<Pred> {
                    ::core::panicking::panic("not implemented")
                }
            }
            impl<K, V, Pred: InvariantPredicate<K, V>> ::core::clone::Clone
            for Instance<K, V, Pred> {
                fn clone(&self) -> Self {
                    ::core::panicking::panic("not implemented");
                }
            }
            impl<K, V, Pred: InvariantPredicate<K, V>> ::core::marker::Copy
            for Instance<K, V, Pred> {}
            impl<K, V, Pred: InvariantPredicate<K, V>> State<K, V, Pred> {}
        }
        type MutexInstance<K, V, Pred> = MutexToks::Instance<K, V, Pred>;
        type MutexLockedToken<K, V, Pred> = MutexToks::locked<K, V, Pred>;
        type MutexOwnerToken<K, V, Pred> = MutexToks::owner<K, V, Pred>;
        /// A mutex protecting an object of type `V` with invariant `Pred`.
        /// The mutex is identified by a key of type `K`.
        pub struct Mutex<K, V, Pred: InvariantPredicate<K, V>> {
            pub locked: AtomicBool<
                FieldType_Mutex_inst<K, V, Pred>,
                MutexLockedToken<K, V, Pred>,
                InvariantPredicate_auto_Mutex_locked,
            >,
            pub inst: Tracked<MutexInstance<K, V, Pred>>,
            pub k: Ghost<K>,
        }
        pub type FieldType_Mutex_locked<K, V, Pred> = AtomicBool<
            FieldType_Mutex_inst<K, V, Pred>,
            MutexLockedToken<K, V, Pred>,
            InvariantPredicate_auto_Mutex_locked,
        >;
        pub type FieldType_Mutex_inst<K, V, Pred> = Tracked<MutexInstance<K, V, Pred>>;
        pub type FieldType_Mutex_k<K> = Ghost<K>;
        pub struct InvariantPredicate_auto_Mutex_locked {}
        impl<
            K,
            V,
            Pred: InvariantPredicate<K, V>,
        > ::vstd::atomic_ghost::AtomicInvariantPredicate<
            FieldType_Mutex_inst<K, V, Pred>,
            bool,
            MutexLockedToken<K, V, Pred>,
        > for InvariantPredicate_auto_Mutex_locked {}
        impl<K, V, Pred: InvariantPredicate<K, V>> Mutex<K, V, Pred> {}
        /// A guard object representing ownership of the mutex. The guard holds the owner token and
        /// the protected value.
        pub struct MutexGuard<K, V, Pred: InvariantPredicate<K, V>> {
            pub handle: Tracked<MutexOwnerToken<K, V, Pred>>,
            pub token: Tracked<V>,
        }
        impl<K, V, Pred: InvariantPredicate<K, V>> MutexGuard<K, V, Pred> {}
        impl<K, V, Pred: InvariantPredicate<K, V>> Mutex<K, V, Pred> {
            /// Create a new mutex protecting the value `val` with invariant `Pred`.
            /// The mutex is identified by the key `k`.
            pub fn new(verus_tmp_k: Ghost<K>, verus_tmp_val: Tracked<V>) -> Self {
                let inst = Tracked::assume_new_fallback(|| ::core::panicking::panic(
                    "internal error: entered unreachable code",
                ));
                let locked = AtomicBool::new(
                    Ghost::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                    false,
                    Tracked::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                );
                Mutex {
                    locked,
                    inst,
                    k: Ghost::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                }
            }
            /// Acquire the mutex, returning a guard object that holds the protected value. This method spins
            /// until it can acquire the mutex.
            pub fn lock(&self) -> MutexGuard<K, V, Pred> {
                {
                    let atomic = &(&self.locked);
                    #[allow(unexpected_cfgs)]
                    {
                        {
                            {
                                {}
                                {}
                            }
                        }
                    };
                };
                loop {
                    let result = {
                        let result;
                        let atomic = &(&self.locked);
                        let operand1 = false;
                        let operand2 = true;
                        #[allow(unexpected_cfgs)]
                        {
                            {
                                {
                                    result = atomic
                                        .patomic
                                        .compare_exchange(
                                            Tracked::assume_new_fallback(|| ::core::panicking::panic(
                                                "internal error: entered unreachable code",
                                            )),
                                            operand1,
                                            operand2,
                                        );
                                    {}
                                    {}
                                }
                            }
                        };
                        result
                    };
                    if result.is_ok() {
                        return MutexGuard {
                            handle: Tracked::assume_new_fallback(|| ::core::panicking::panic(
                                "internal error: entered unreachable code",
                            )),
                            token: Tracked::assume_new_fallback(|| ::core::panicking::panic(
                                "internal error: entered unreachable code",
                            )),
                        };
                    }
                }
            }
            /// Release the mutex by consuming the guard. The protected value is returned to the mutex.
            pub fn unlock(&self, guard: MutexGuard<K, V, Pred>) {
                {
                    let atomic = &(&self.locked);
                    #[allow(unexpected_cfgs)]
                    {
                        {
                            {
                                atomic
                                    .patomic
                                    .store(
                                        Tracked::assume_new_fallback(|| ::core::panicking::panic(
                                            "internal error: entered unreachable code",
                                        )),
                                        false,
                                    );
                                {}
                                {}
                            }
                        }
                    };
                };
            }
        }
    }
    pub mod rwlock {
        use core::marker::PhantomData;
        use verus_state_machines_macros::tokenized_state_machine;
        use vstd::atomic_ghost::*;
        use vstd::cell::CellId;
        use vstd::cell::PCell;
        use vstd::cell::PointsTo;
        use vstd::invariant;
        use vstd::invariant::{AtomicInvariant, InvariantPredicate};
        use vstd::multiset::*;
        use vstd::open_atomic_invariant;
        use vstd::prelude::*;
        use vstd::rwlock::RwLock as VerusRwLock;
        #[allow(unused_parens)]
        pub mod RwLockToks {
            use super::*;
            use ::vstd::tokens::ValueToken;
            use ::vstd::tokens::KeyValueToken;
            use ::vstd::tokens::CountToken;
            use ::vstd::tokens::MonotonicCountToken;
            use ::vstd::tokens::ElementToken;
            use ::vstd::tokens::SimpleToken;
            pub struct State<K, V, Pred: InvariantPredicate<K, V>> {
                pub k: K,
                pub pred: PhantomData<Pred>,
                pub flag_exc: bool,
                pub flag_rc: nat,
                pub flag_real_rc: nat,
                pub storage: ::core::option::Option<V>,
                pub pending_writer: ::core::option::Option<()>,
                pub writer: ::core::option::Option<()>,
                pub pending_reader: ::vstd::multiset::Multiset<()>,
                pub mock_reader: ::vstd::multiset::Multiset<()>,
                pub reader: ::vstd::multiset::Multiset<V>,
            }
            #[allow(non_camel_case_types)]
            pub enum Step<K, V, Pred: InvariantPredicate<K, V>> {
                acquire_read_start(),
                acquire_read_end(),
                inc_real_rc(),
                acquire_read_abandon(),
                acquire_exc_start(),
                acquire_exc_end(),
                release_exc(V),
                dec_real_rc(V),
                release_shared(),
                dummy_to_use_type_params(State<K, V, Pred>),
            }
            #[allow(non_camel_case_types)]
            pub enum Config<K, V, Pred: InvariantPredicate<K, V>> {
                initialize(K, V),
                dummy_to_use_type_params(State<K, V, Pred>),
            }
            pub mod show {
                use super::*;
                use bool as acquire_read_start;
                use bool as acquire_read_end;
                use bool as inc_real_rc;
                use bool as acquire_read_abandon;
                use bool as acquire_exc_start;
                use bool as acquire_exc_end;
                use bool as release_exc;
                use bool as dec_real_rc;
                use bool as release_shared;
                use bool as initialize;
            }
            pub mod take_step {
                use super::*;
                use bool as initialize;
                use bool as acquire_read_start;
                use bool as acquire_read_end;
                use bool as inc_real_rc;
                use bool as acquire_read_abandon;
                use bool as acquire_exc_start;
                use bool as acquire_exc_end;
                use bool as release_exc;
                use bool as dec_real_rc;
                use bool as release_shared;
            }
            #[allow(non_camel_case_types)]
            pub struct Instance<K, V, Pred: InvariantPredicate<K, V>> {
                send_sync: ::vstd::state_machine_internal::SyncSendIfSyncSend<(V)>,
                state: ::core::option::Option<::vstd::prelude::Ghost<State<K, V, Pred>>>,
                location: ::vstd::prelude::int,
            }
            #[allow(non_camel_case_types)]
            pub struct flag_exc<K, V, Pred: InvariantPredicate<K, V>> {
                dummy_instance: Instance<K, V, Pred>,
                no_copy: ::vstd::state_machine_internal::NoCopy,
            }
            impl<K, V, Pred: InvariantPredicate<K, V>> flag_exc<K, V, Pred> {}
            impl<K, V, Pred: InvariantPredicate<K, V>> ::vstd::tokens::ValueToken<bool>
            for flag_exc<K, V, Pred> {}
            impl<
                K,
                V,
                Pred: InvariantPredicate<K, V>,
            > ::vstd::tokens::UniqueValueToken<bool> for flag_exc<K, V, Pred> {}
            #[allow(non_camel_case_types)]
            pub struct flag_rc<K, V, Pred: InvariantPredicate<K, V>> {
                dummy_instance: Instance<K, V, Pred>,
                no_copy: ::vstd::state_machine_internal::NoCopy,
            }
            impl<K, V, Pred: InvariantPredicate<K, V>> flag_rc<K, V, Pred> {}
            impl<K, V, Pred: InvariantPredicate<K, V>> ::vstd::tokens::ValueToken<nat>
            for flag_rc<K, V, Pred> {}
            impl<
                K,
                V,
                Pred: InvariantPredicate<K, V>,
            > ::vstd::tokens::UniqueValueToken<nat> for flag_rc<K, V, Pred> {}
            #[allow(non_camel_case_types)]
            pub struct flag_real_rc<K, V, Pred: InvariantPredicate<K, V>> {
                dummy_instance: Instance<K, V, Pred>,
                no_copy: ::vstd::state_machine_internal::NoCopy,
            }
            impl<K, V, Pred: InvariantPredicate<K, V>> flag_real_rc<K, V, Pred> {}
            impl<K, V, Pred: InvariantPredicate<K, V>> ::vstd::tokens::ValueToken<nat>
            for flag_real_rc<K, V, Pred> {}
            impl<
                K,
                V,
                Pred: InvariantPredicate<K, V>,
            > ::vstd::tokens::UniqueValueToken<nat> for flag_real_rc<K, V, Pred> {}
            #[allow(non_camel_case_types)]
            pub struct pending_writer<K, V, Pred: InvariantPredicate<K, V>> {
                dummy_instance: Instance<K, V, Pred>,
                no_copy: ::vstd::state_machine_internal::NoCopy,
            }
            impl<K, V, Pred: InvariantPredicate<K, V>> pending_writer<K, V, Pred> {}
            impl<K, V, Pred: InvariantPredicate<K, V>> ::vstd::tokens::ValueToken<()>
            for pending_writer<K, V, Pred> {}
            impl<
                K,
                V,
                Pred: InvariantPredicate<K, V>,
            > ::vstd::tokens::UniqueValueToken<()> for pending_writer<K, V, Pred> {}
            #[allow(non_camel_case_types)]
            pub struct writer<K, V, Pred: InvariantPredicate<K, V>> {
                dummy_instance: Instance<K, V, Pred>,
                no_copy: ::vstd::state_machine_internal::NoCopy,
            }
            impl<K, V, Pred: InvariantPredicate<K, V>> writer<K, V, Pred> {}
            impl<K, V, Pred: InvariantPredicate<K, V>> ::vstd::tokens::ValueToken<()>
            for writer<K, V, Pred> {}
            impl<
                K,
                V,
                Pred: InvariantPredicate<K, V>,
            > ::vstd::tokens::UniqueValueToken<()> for writer<K, V, Pred> {}
            #[allow(non_camel_case_types)]
            pub struct pending_reader<K, V, Pred: InvariantPredicate<K, V>> {
                dummy_instance: Instance<K, V, Pred>,
                no_copy: ::vstd::state_machine_internal::NoCopy,
            }
            impl<K, V, Pred: InvariantPredicate<K, V>> pending_reader<K, V, Pred> {}
            impl<K, V, Pred: InvariantPredicate<K, V>> ::vstd::tokens::ElementToken<()>
            for pending_reader<K, V, Pred> {}
            #[allow(type_alias_bounds)]
            #[allow(non_camel_case_types)]
            pub type pending_reader_multiset<K, V, Pred: InvariantPredicate<K, V>> = ::vstd::tokens::MultisetToken<
                (),
                pending_reader<K, V, Pred>,
            >;
            #[allow(non_camel_case_types)]
            pub struct mock_reader<K, V, Pred: InvariantPredicate<K, V>> {
                dummy_instance: Instance<K, V, Pred>,
                no_copy: ::vstd::state_machine_internal::NoCopy,
            }
            impl<K, V, Pred: InvariantPredicate<K, V>> mock_reader<K, V, Pred> {}
            impl<K, V, Pred: InvariantPredicate<K, V>> ::vstd::tokens::ElementToken<()>
            for mock_reader<K, V, Pred> {}
            #[allow(type_alias_bounds)]
            #[allow(non_camel_case_types)]
            pub type mock_reader_multiset<K, V, Pred: InvariantPredicate<K, V>> = ::vstd::tokens::MultisetToken<
                (),
                mock_reader<K, V, Pred>,
            >;
            #[allow(non_camel_case_types)]
            pub struct reader<K, V, Pred: InvariantPredicate<K, V>> {
                dummy_instance: Instance<K, V, Pred>,
                no_copy: ::vstd::state_machine_internal::NoCopy,
            }
            impl<K, V, Pred: InvariantPredicate<K, V>> reader<K, V, Pred> {}
            impl<K, V, Pred: InvariantPredicate<K, V>> ::vstd::tokens::ElementToken<V>
            for reader<K, V, Pred> {}
            #[allow(type_alias_bounds)]
            #[allow(non_camel_case_types)]
            pub type reader_multiset<K, V, Pred: InvariantPredicate<K, V>> = ::vstd::tokens::MultisetToken<
                V,
                reader<K, V, Pred>,
            >;
            impl<K, V, Pred: InvariantPredicate<K, V>> Instance<K, V, Pred> {
                pub fn id(&self) -> ::vstd::tokens::InstanceId {
                    ::core::panicking::panic("not implemented")
                }
                pub fn k(&self) -> K {
                    ::core::panicking::panic("not implemented")
                }
                pub fn pred(&self) -> PhantomData<Pred> {
                    ::core::panicking::panic("not implemented")
                }
            }
            impl<K, V, Pred: InvariantPredicate<K, V>> ::core::clone::Clone
            for Instance<K, V, Pred> {
                fn clone(&self) -> Self {
                    ::core::panicking::panic("not implemented");
                }
            }
            impl<K, V, Pred: InvariantPredicate<K, V>> ::core::marker::Copy
            for Instance<K, V, Pred> {}
            impl<K, V, Pred: InvariantPredicate<K, V>> State<K, V, Pred> {}
        }
        use crate::bitmap_allocator::bitmap_trait::BitmapAllocator;
        type RwInstance<K, V, Pred> = RwLockToks::Instance<K, V, Pred>;
        type RwExcToken<K, V, Pred> = RwLockToks::flag_exc<K, V, Pred>;
        type RwRcToken<K, V, Pred> = RwLockToks::flag_rc<K, V, Pred>;
        type RwRealRcToken<K, V, Pred> = RwLockToks::flag_real_rc<K, V, Pred>;
        pub type RwWriterToken<K, V, Pred> = RwLockToks::writer<K, V, Pred>;
        type RwMockReaderToken<K, V, Pred> = RwLockToks::mock_reader<K, V, Pred>;
        pub type RwReaderToken<K, V, Pred> = RwLockToks::reader<K, V, Pred>;
        type RwPendingWriterToken<K, V, Pred> = RwLockToks::pending_writer<K, V, Pred>;
        type RwPendingReaderToken<K, V, Pred> = RwLockToks::pending_reader<K, V, Pred>;
        /// An RwLock parameterised by a ghost key `K` and a predicate `Pred`.
        ///
        /// `Pred::inv(k, v)` must hold whenever `v` is stored inside the lock.
        /// This mirrors the `Mutex<K,V,Pred>` design: whoever releases the write
        /// lock must prove the predicate, and whoever acquires the write lock
        /// receives a value that already satisfies it.
        pub struct RwLock<K, V, Pred: InvariantPredicate<K, V>> {
            pub exc: AtomicBool<
                FieldType_RwLock_inst<K, V, Pred>,
                RwExcToken<K, V, Pred>,
                InvariantPredicate_auto_RwLock_exc,
            >,
            pub rc: AtomicU64<
                FieldType_RwLock_inst<K, V, Pred>,
                RwRcToken<K, V, Pred>,
                InvariantPredicate_auto_RwLock_rc,
            >,
            pub real_rc: AtomicU64<
                FieldType_RwLock_inst<K, V, Pred>,
                RwRealRcToken<K, V, Pred>,
                InvariantPredicate_auto_RwLock_real_rc,
            >,
            pub inst: Tracked<RwInstance<K, V, Pred>>,
            /// Ghost key; matches `inst@.k()` (enforced by `predicate` below).
            pub k: Ghost<K>,
        }
        pub type FieldType_RwLock_exc<K, V, Pred> = AtomicBool<
            FieldType_RwLock_inst<K, V, Pred>,
            RwExcToken<K, V, Pred>,
            InvariantPredicate_auto_RwLock_exc,
        >;
        pub type FieldType_RwLock_rc<K, V, Pred> = AtomicU64<
            FieldType_RwLock_inst<K, V, Pred>,
            RwRcToken<K, V, Pred>,
            InvariantPredicate_auto_RwLock_rc,
        >;
        pub type FieldType_RwLock_real_rc<K, V, Pred> = AtomicU64<
            FieldType_RwLock_inst<K, V, Pred>,
            RwRealRcToken<K, V, Pred>,
            InvariantPredicate_auto_RwLock_real_rc,
        >;
        pub type FieldType_RwLock_inst<K, V, Pred> = Tracked<RwInstance<K, V, Pred>>;
        pub type FieldType_RwLock_k<K> = Ghost<K>;
        pub struct InvariantPredicate_auto_RwLock_exc {}
        impl<
            K,
            V,
            Pred: InvariantPredicate<K, V>,
        > ::vstd::atomic_ghost::AtomicInvariantPredicate<
            FieldType_RwLock_inst<K, V, Pred>,
            bool,
            RwExcToken<K, V, Pred>,
        > for InvariantPredicate_auto_RwLock_exc {}
        pub struct InvariantPredicate_auto_RwLock_rc {}
        impl<
            K,
            V,
            Pred: InvariantPredicate<K, V>,
        > ::vstd::atomic_ghost::AtomicInvariantPredicate<
            FieldType_RwLock_inst<K, V, Pred>,
            u64,
            RwRcToken<K, V, Pred>,
        > for InvariantPredicate_auto_RwLock_rc {}
        pub struct InvariantPredicate_auto_RwLock_real_rc {}
        impl<
            K,
            V,
            Pred: InvariantPredicate<K, V>,
        > ::vstd::atomic_ghost::AtomicInvariantPredicate<
            FieldType_RwLock_inst<K, V, Pred>,
            u64,
            RwRealRcToken<K, V, Pred>,
        > for InvariantPredicate_auto_RwLock_real_rc {}
        impl<K, V, Pred: InvariantPredicate<K, V>> RwLock<K, V, Pred> {}
        impl<K, V, Pred: InvariantPredicate<K, V>> RwLock<K, V, Pred> {
            /// Create a new `RwLock` protecting value `t` under key `k` with predicate `Pred`.
            ///
            /// Mirrors `Mutex::new`: the caller must prove `Pred::inv(k, t)` up front;
            /// thereafter `storage_inv` in the state machine guarantees the predicate
            /// holds for the stored value at all times.
            pub fn new(verus_tmp_k: Ghost<K>, verus_tmp_t: Tracked<V>) -> Self {
                let inst = Tracked::assume_new_fallback(|| ::core::panicking::panic(
                    "internal error: entered unreachable code",
                ));
                let exc = AtomicBool::new(
                    Ghost::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                    false,
                    Tracked::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                );
                let rc = AtomicU64::new(
                    Ghost::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                    0u64,
                    Tracked::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                );
                let real_rc = AtomicU64::new(
                    Ghost::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                    0u64,
                    Tracked::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                );
                RwLock {
                    exc,
                    rc,
                    real_rc,
                    inst,
                    k: Ghost::assume_new_fallback(|| ::core::panicking::panic(
                        "internal error: entered unreachable code",
                    )),
                }
            }
            pub fn lock_write(&self) -> RwWriteGuard<K, V, Pred> {
                let mut done = false;
                while !done {
                    let result = {
                        let result;
                        let atomic = &(&self.exc);
                        let operand1 = false;
                        let operand2 = true;
                        #[allow(unexpected_cfgs)]
                        {
                            {
                                {
                                    result = atomic
                                        .patomic
                                        .compare_exchange(
                                            Tracked::assume_new_fallback(|| ::core::panicking::panic(
                                                "internal error: entered unreachable code",
                                            )),
                                            operand1,
                                            operand2,
                                        );
                                    {}
                                    {}
                                }
                            }
                        };
                        result
                    };
                    done = result.is_ok();
                }
                let mut write_handle_opt: Option<RwWriteGuard<K, V, Pred>> = None;
                loop {
                    let result = {
                        let result;
                        let atomic = &(&self.rc);
                        #[allow(unexpected_cfgs)]
                        {
                            {
                                {
                                    result = atomic
                                        .patomic
                                        .load(
                                            Tracked::assume_new_fallback(|| ::core::panicking::panic(
                                                "internal error: entered unreachable code",
                                            )),
                                        );
                                    {}
                                    {}
                                }
                            }
                        };
                        result
                    };
                    if result == 0 {
                        {};
                        let _ = {
                            let atomic = &(&self.real_rc);
                            #[allow(unexpected_cfgs)]
                            {
                                {
                                    {
                                        {}
                                        {}
                                    }
                                }
                            };
                        };
                        let write_handle = RwWriteGuard {
                            handle: Tracked::assume_new_fallback(|| ::core::panicking::panic(
                                "internal error: entered unreachable code",
                            )),
                            token: Tracked::assume_new_fallback(|| ::core::panicking::panic(
                                "internal error: entered unreachable code",
                            )),
                        };
                        write_handle_opt = Some(write_handle);
                        break;
                    }
                }
                {};
                let write_handle = write_handle_opt.unwrap();
                write_handle
            }
            pub fn lock_read(&self) -> RwReadGuard<K, V, Pred> {
                let mut read_handle_opt: Option<RwReadGuard<K, V, Pred>> = None;
                loop {
                    let rc_val = {
                        let result;
                        let atomic = &(&self.rc);
                        #[allow(unexpected_cfgs)]
                        {
                            {
                                {
                                    result = atomic
                                        .patomic
                                        .load(
                                            Tracked::assume_new_fallback(|| ::core::panicking::panic(
                                                "internal error: entered unreachable code",
                                            )),
                                        );
                                    {}
                                    {}
                                }
                            }
                        };
                        result
                    };
                    if rc_val >= u64::MAX {
                        continue;
                    }
                    let result = {
                        let result;
                        let atomic = &(&self.rc);
                        let operand1 = rc_val;
                        let operand2 = rc_val + 1;
                        #[allow(unexpected_cfgs)]
                        {
                            {
                                {
                                    result = atomic
                                        .patomic
                                        .compare_exchange(
                                            Tracked::assume_new_fallback(|| ::core::panicking::panic(
                                                "internal error: entered unreachable code",
                                            )),
                                            operand1,
                                            operand2,
                                        );
                                    {}
                                    {}
                                }
                            }
                        };
                        result
                    };
                    if result.is_err() {
                        continue;
                    }
                    let result = {
                        let result;
                        let atomic = &(&self.exc);
                        #[allow(unexpected_cfgs)]
                        {
                            {
                                {
                                    result = atomic
                                        .patomic
                                        .load(
                                            Tracked::assume_new_fallback(|| ::core::panicking::panic(
                                                "internal error: entered unreachable code",
                                            )),
                                        );
                                    {}
                                    {}
                                }
                            }
                        };
                        result
                    };
                    if result == false {
                        loop {
                            let real_rc_val = {
                                let result;
                                let atomic = &(&self.real_rc);
                                #[allow(unexpected_cfgs)]
                                {
                                    {
                                        {
                                            result = atomic
                                                .patomic
                                                .load(
                                                    Tracked::assume_new_fallback(|| ::core::panicking::panic(
                                                        "internal error: entered unreachable code",
                                                    )),
                                                );
                                            {}
                                            {}
                                        }
                                    }
                                };
                                result
                            };
                            if real_rc_val >= u64::MAX {
                                continue;
                            }
                            let result = {
                                let result;
                                let atomic = &(&self.real_rc);
                                let operand1 = real_rc_val;
                                let operand2 = real_rc_val + 1;
                                #[allow(unexpected_cfgs)]
                                {
                                    {
                                        {
                                            result = atomic
                                                .patomic
                                                .compare_exchange(
                                                    Tracked::assume_new_fallback(|| ::core::panicking::panic(
                                                        "internal error: entered unreachable code",
                                                    )),
                                                    operand1,
                                                    operand2,
                                                );
                                            {}
                                            {}
                                        }
                                    }
                                };
                                result
                            };
                            match result {
                                Ok(_) => {
                                    {}
                                    let read_handle = RwReadGuard {
                                        handle: Tracked::assume_new_fallback(|| ::core::panicking::panic(
                                            "internal error: entered unreachable code",
                                        )),
                                    };
                                    read_handle_opt = Some(read_handle);
                                    break;
                                }
                                Err(_) => {}
                            }
                        }
                        break;
                    } else {
                        let _ = {
                            let result;
                            let atomic = &(&self.rc);
                            let operand = 1;
                            #[allow(unexpected_cfgs)]
                            {
                                {
                                    {
                                        {}
                                        result = atomic
                                            .patomic
                                            .fetch_sub(
                                                Tracked::assume_new_fallback(|| ::core::panicking::panic(
                                                    "internal error: entered unreachable code",
                                                )),
                                                operand,
                                            );
                                        {}
                                    }
                                }
                            };
                            result
                        };
                    }
                }
                read_handle_opt.unwrap()
            }
            /// Release the write lock.  The caller must prove `self.inv(guard.view())`
            /// (i.e. `Pred::inv(self.k@, value)`) so the state machine's `storage_inv`
            /// invariant is maintained — exactly as `Mutex::unlock` does.
            pub fn unlock_write(&self, guard: RwWriteGuard<K, V, Pred>) -> () {
                {
                    let atomic = &(&self.exc);
                    #[allow(unexpected_cfgs)]
                    {
                        {
                            {
                                atomic
                                    .patomic
                                    .store(
                                        Tracked::assume_new_fallback(|| ::core::panicking::panic(
                                            "internal error: entered unreachable code",
                                        )),
                                        false,
                                    );
                                {}
                                {}
                            }
                        }
                    };
                };
            }
            pub fn unlock_read(&self, guard: RwReadGuard<K, V, Pred>) -> () {
                let mock_handle = {
                    let result;
                    let atomic = &(&self.real_rc);
                    let operand = 1;
                    #[allow(unexpected_cfgs)]
                    {
                        {
                            {
                                {}
                                result = atomic
                                    .patomic
                                    .fetch_sub(
                                        Tracked::assume_new_fallback(|| ::core::panicking::panic(
                                            "internal error: entered unreachable code",
                                        )),
                                        operand,
                                    );
                                {}
                            }
                        }
                    };
                    result
                };
                {
                    let result;
                    let atomic = &(&self.rc);
                    let operand = 1;
                    #[allow(unexpected_cfgs)]
                    {
                        {
                            {
                                {}
                                result = atomic
                                    .patomic
                                    .fetch_sub(
                                        Tracked::assume_new_fallback(|| ::core::panicking::panic(
                                            "internal error: entered unreachable code",
                                        )),
                                        operand,
                                    );
                                {}
                            }
                        }
                    };
                    result
                };
            }
        }
        /// Write-lock guard carrying both the writer token and the withdrawn value.
        ///
        /// `view()` exposes the stored `V`; the caller must prove `rwlock.inv(guard.view())`
        /// before calling `unlock_write` (exactly mirroring `MutexGuard` + `Mutex::unlock`).
        pub struct RwWriteGuard<K, V, Pred: InvariantPredicate<K, V>> {
            pub handle: Tracked<RwWriterToken<K, V, Pred>>,
            pub token: Tracked<V>,
        }
        impl<K, V, Pred: InvariantPredicate<K, V>> RwWriteGuard<K, V, Pred> {}
        /// Read-lock guard carrying the reader token (a multiset element of type `V`).
        pub struct RwReadGuard<K, V, Pred: InvariantPredicate<K, V>> {
            pub handle: Tracked<RwReaderToken<K, V, Pred>>,
        }
        impl<K, V, Pred: InvariantPredicate<K, V>> RwReadGuard<K, V, Pred> {
            pub fn borrow(&self, rwlock: &RwLock<K, V, Pred>) -> Tracked<&V> {
                Tracked::assume_new_fallback(|| ::core::panicking::panic(
                    "internal error: entered unreachable code",
                ))
            }
        }
    }
}
const _: () = {
    if ::core::mem::size_of::<usize>() != 8 {
        {
            ::std::rt::begin_panic("does not have the expected size");
        };
    }
};
fn main() {}
