use spin::Once;
// use std::vec::Vec;
use vstd::prelude::Tracked;

use verified_hv_mem::{
    address::{addr::PAddr, region::PAGE_SIZE},
    global_allocator::{ClientState, GbAlloc},
};

static GB_ALLOCATOR: Once<GbAlloc> = Once::new();

pub fn init_global_allocator(base:usize) -> &'static GbAlloc {
    GB_ALLOCATOR.call_once(|| GbAlloc::default(PAddr(base)))
}

pub fn gb_allocator() -> &'static GbAlloc {
    GB_ALLOCATOR.get().expect("GB_ALLOCATOR is not initialized")
}

/// A safe wrapper for physical frame allocation.
#[derive(Debug)]
pub struct Frame {
    start_paddr: usize,
    frame_count: usize,
}

#[allow(dead_code)]
impl Frame {
    /// Allocate one physical frame.
    pub fn new(client: Tracked<ClientState>) -> (Self, Tracked<ClientState>) {
        let (start_paddr, client) = gb_allocator().alloc(client);
        (
            Self {
                start_paddr: start_paddr.0,
                frame_count: 1,
            },
            client,
        )
    }

    /// Allocate one physical frame and fill with zero.
    pub fn new_zero(client: Tracked<ClientState>) -> (Self, Tracked<ClientState>) {
        let (mut f, client) = Self::new(client);
        f.clear();
        (f, client)
    }

    /// Allocate contiguous physical frames.
    pub fn new_contiguous(
        client: Tracked<ClientState>,
        frame_count: usize,
        align_log2: usize,
    ) -> (Self, Tracked<ClientState>) {
        let (start_paddr, client) = gb_allocator().alloc_contiguous(client, frame_count, align_log2);
        (
            Self {
                start_paddr: start_paddr.0,
                frame_count,
            },
            client,
        )
    }

    /// allocate contigugous frames, and you can specify the alignment, set the lower `align_log2` bits to 0.
    pub fn new_contiguous_with_base(client: Tracked<ClientState>, frame_count: usize, align_log2: usize) -> (Self, Tracked<ClientState>) {
        let align_mask = (1 << align_log2) - 1;
        let mut client = client;
        // Create a vector to keep track of attempted frames
        let mut attempted_frames = Vec::new();
        loop {
            let (frame, next_client) = Frame::new_contiguous(client, frame_count, 0);
            if frame.start_paddr() & align_mask == 0 {
                // info!(
                //     "new contiguous success!!! start_paddr:0x{:x}",
                //     frame.start_paddr()
                // );
                return (frame, next_client);
            } else {
                let start_paddr = frame.start_paddr();
                let next_aligned_addr = (start_paddr + align_mask) & !align_mask; // up_align
                let temp_frame_count = (next_aligned_addr - start_paddr) / PAGE_SIZE;
                let reclaimed_client = gb_allocator().dealloc_contiguous(
                    next_client,
                    PAddr(frame.start_paddr),
                    frame.frame_count,
                );
                let (padding_frame, next_client) =
                    Frame::new_contiguous(reclaimed_client, temp_frame_count, 0);
                attempted_frames.push(padding_frame);
                client = next_client;
            }
        }
    }

    pub fn dealloc(self, client: Tracked<ClientState>) -> Tracked<ClientState> {
        assert_eq!(self.frame_count, 1, "only single-frame dealloc is supported");
        gb_allocator().dealloc(client, PAddr(self.start_paddr))
    }    

    /// Constructs a frame from a raw physical address without automatically calling the destructor.
    ///
    /// # Safety
    ///
    /// This function is unsafe because the user must ensure that this is an available physical
    /// frame.
    pub unsafe fn from_paddr(start_paddr: usize) -> Self {
        Self {
            start_paddr,
            frame_count: 0,
        }
    }

    pub fn new_16(client: Tracked<ClientState>) -> (Self, Tracked<ClientState>) {
        Self::new_contiguous_with_base(client, 4, 14)
    }

    /// Get the start physical address of this frame.
    pub fn start_paddr(&self) -> usize {
        self.start_paddr
    }

    /// Get the total size (in bytes) of this frame.
    pub fn size(&self) -> usize {
        self.frame_count * PAGE_SIZE
    }

    /// convert to raw a pointer.
    pub fn as_ptr(&self) -> *const u8 {
        self.start_paddr as *const u8
    }

    /// convert to a mutable raw pointer.
    pub fn as_mut_ptr(&self) -> *mut u8 {
        self.start_paddr as *mut u8
    }

    /// Fill `self` with `byte`.
    pub fn fill(&mut self, byte: u8) {
        let ptr = self.as_mut_ptr();
        for i in 0..self.size() {
            unsafe {
                *ptr.add(i) = byte;
            }
        }
    }

    /// Fill `self` with zero.
    pub fn clear(&mut self) {
        self.fill(0)
    }

    /// Forms a slice that can read data.
    pub fn as_slice(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.size()) }
    }

    /// Forms a mutable slice that can write data.
    pub fn as_slice_mut(&mut self) -> &mut [u8] {
        unsafe { core::slice::from_raw_parts_mut(self.as_mut_ptr(), self.size()) }
    }

    pub fn copy_data_from(&mut self, data: &[u8]) {
        let len = data.len();
        assert!(data.len() <= self.size());
        self.as_slice_mut()[..len].copy_from_slice(data);
    }
}

/// Initialize the physical frame allocator.
pub fn init() {
    init_global_allocator(0x1000);
    gb_allocator().init(0x1000, Tracked::assume_new());
}

fn main() {
    // test code

    // init();
    // let gb_alloc = gb_allocator();

    // assert_eq!(gb_alloc.base.0, 0x1000);

    // let (frame0, client) = Frame::new(Tracked::assume_new());
    // assert_eq!(frame0.start_paddr(), 0x1000);
    // println!("after alloc: frame = 0x{:x}", frame0.start_paddr());

    // let (frame1, client1) = Frame::new(Tracked::assume_new());
    // assert_eq!(frame1.start_paddr(), 0x2000);
    // println!("after alloc: frame = 0x{:x}", frame1.start_paddr());

    // let released_paddr = frame0.start_paddr();
    // let client = frame0.dealloc(client1);
    // println!("after dealloc: released frame = 0x{:x}", released_paddr);

    // let (frame2, mut client) = Frame::new(client);
    // assert_eq!(frame2.start_paddr(), 0x1000);
    // println!("after realloc: frame = 0x{:x}", frame2.start_paddr());

    // let align_log2 = 13;
    // let (aligned_frame, next_client) = Frame::new_contiguous_with_base(client, 1, align_log2);
    // client = next_client;
    // assert_eq!(aligned_frame.start_paddr(), 0x4000);
    // assert_eq!(aligned_frame.start_paddr() & ((1 << align_log2) - 1), 0);
    // println!(
    //     "aligned contiguous alloc: frame = 0x{:x}, align_log2 = {}",
    //     aligned_frame.start_paddr(),
    //     align_log2
    // );

    // let (frame16, next_client) = Frame::new_16(client);
    // client = next_client;
    // assert_eq!(frame16.start_paddr() & ((1 << 14) - 1), 0);
    // assert_eq!(frame16.size(), 4 * PAGE_SIZE);
    // println!(
    //     "new_16 alloc: frame = 0x{:x}, size = 0x{:x}",
    //     frame16.start_paddr(),
    //     frame16.size()
    // );

    // let mut frames: Vec<Frame> = Vec::new();
    // for i in 0..5 {
    //     let (frame, next_client) = Frame::new(client);
    //     client = next_client;
    //     println!("frame batch 1 [{}]: start = 0x{:x}", i, frame.start_paddr());
    //     frames.push(frame);
    // }
    // frames.clear();
    // for i in 0..5 {
    //     let (frame, next_client) = Frame::new(client);
    //     client = next_client;
    //     println!("frame batch 2 [{}]: start = 0x{:x}", i, frame.start_paddr());
    //     frames.push(frame);
    // }
    // drop(frames);
    // println!("frame allocator test passed");

    // println!("global GB_ALLOCATOR ready at base = 0x{:x}", gb_alloc.base.0);
}
