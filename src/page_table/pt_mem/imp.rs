//! Page table memory implementation using verified frame allocator.
use super::{PageTableMem, SpecPageTableMem, SpecTable};
use crate::{
    address::{
        addr::PAddr,
        frame::{Frame, FrameSize, PAGE_SIZE},
    },
    frame_allocator::frame_trait::{paddr_to_idx, FrameAllocator},
    page_table::pt_arch::PTArch,
};
use vstd::{invariant, prelude::*};

verus! {

broadcast use super::group_pt_mem_lemmas;

/// Describes a single page table.
pub struct Table {
    /// The base physical address of the page table.
    pub base: PAddr,
    /// Level of the page table.
    pub level: usize,
}

impl Table {
    /// View as a spec table.
    pub open spec fn view(self) -> SpecTable {
        SpecTable { base: self.base@, level: self.level as nat, size: FrameSize::Size4K }
    }
}

/// Page table memory implementation using a vector to store page tables.
/// 
/// Note: To prove the correctness of allocation and deallocation, the frame allocator must be owned
/// by the page table memory. We need to ensure that no other part of the system modifies the frame
/// allocator while the page table memory is using it. But this is inconsistent with our existing system.
pub struct VecPageTableMem<FA: FrameAllocator> {
    /// The page table architecture.
    pub arch: PTArch,
    /// Page tables allocated for this page table memory.
    pub tables: Vec<Table>,
    /// The frame allocator used to allocate frames for page tables.
    pub frame_alloc: FA,
}

impl<FA: FrameAllocator> PageTableMem for VecPageTableMem<FA> {
    open spec fn view(self) -> SpecPageTableMem {
        let tables = Seq::new(self.tables.len() as nat, |i| self.tables[i]@);
        SpecPageTableMem { arch: self.arch@, tables }
    }

    open spec fn invariants(self) -> bool {
        &&& self.frame_alloc.wf()
        &&& self.view().wf()
        // Allocator uses 4KB pages.
        &&& FA::spec_page_size() == PAGE_SIZE
        // All tables are within the frame allocator's managed memory.
        &&& forall|i: int|
            0 <= i < self.tables.len() ==> #[trigger] paddr_to_idx(self.frame_alloc.base(), self.tables[i].base@, PAGE_SIZE)
                < FA::cap_pages()
        // All tables are recorded in the frame allocator.
        &&& forall|i: int|
            0 <= i < self.tables.len() ==> #[trigger] self.frame_alloc.view()[paddr_to_idx(
                    self.frame_alloc.base(),
                    self.tables[i].base@,
                    PAGE_SIZE,
                ) as int]
    }

    fn root(&self) -> (res: PAddr) {
        self.tables[0].base
    }

    #[verifier::external_body]
    fn read(&self, base: PAddr, index: usize) -> (res: u64) {
        // Note: requires raw pointer access, which is not verifiable.
        unsafe { (base.0 as *const u64).offset(index as isize).read_volatile() }
    }

    #[verifier::external_body]
    fn write(&mut self, base: PAddr, index: usize, val: u64) {
        // Note: requires raw pointer access, which is not verifiable.
        unsafe { (base.0 as *mut u64).offset(index as isize).write_volatile(val) }
    }

    #[verifier::external_body]
    fn is_table_empty(&self, base: PAddr) -> bool {
        // Note: requires raw pointer access, which is not verifiable.
        let table = self.tables.iter().find(|t| t.base == base).unwrap();
        let contents = unsafe { core::slice::from_raw_parts(base.0 as *const u8, PAGE_SIZE) };
        contents.iter().all(|&b| b == 0)
    }

    fn alloc_table(&mut self, level: usize) -> (PAddr, FrameSize) {
        let alloc_res = self.frame_alloc.alloc();
        // TODO: handle out-of-memory failure
        assume(alloc_res is Some);
        let addr = alloc_res.unwrap();
        self.tables.push(Table { base: addr, level });
        proof { assume(false); } // TODO: prove invariants
        (addr, FrameSize::Size4K)
    }

    fn dealloc_table(&mut self, base: PAddr) {
        let mut i = 0;
        while i < self.tables.len()
            invariant
                0 <= i <= self.tables.len(),
                self.invariants(),
            decreases self.tables.len() - i,
        {
            if self.tables[i].base.0 == base.0 {
                break ;
            }
            i += 1;
        }
        proof { assume(false); } // TODO: prove invariants
        if i < self.tables.len() {
            self.frame_alloc.dealloc(base);
            self.tables.remove(i);
        }
    }

    proof fn lemma_invariants_implies_wf(self) {
    }
}

} // verus!
