//! Page table memory read/write utilities and permission assumptions.
use vstd::prelude::*;
use vstd::simple_pptr::PointsTo;

verus! {

use crate::global_allocator::*;

/// A single page table, which contains a fixed number of `u64` entries. The type parameter `N` is the
/// number of entries in the table.
#[derive(Clone, Copy)]
pub struct Table<const N: usize> {
    pub entries: [u64; N],
}

impl<const N: usize> Table<N> {
    /// View the entries of the table as a sequence.
    pub open spec fn view(&self) -> Seq<u64> {
        self.entries.view()
    }

    /// Returns whether all entries in the table are zero.
    pub open spec fn spec_is_empty(&self) -> bool {
        forall|i| 0 <= i < N ==> self.view()[i] == 0
    }

    /// Setting all entries to zero.
    pub fn clear(&mut self)
        ensures
            forall|i| 0 <= i < N ==> self.view()[i] == 0,
    {
        for i in 0..N
            invariant
                0 <= i <= N,
                forall|j| 0 <= j < i ==> self.view()[j] == 0,
        {
            let ghost old_self = *self;
            self.entries[i] = 0;
            assert forall|j| 0 <= j < i implies self.view()[j] == 0 by {
                assert(self.view()[j] == old_self.view()[j]);
            }
        }
    }

    /// Returns the value of the entry at the given index.
    pub fn index(&self, index: usize) -> (res: u64)
        requires
            0 <= index < N,
        ensures
            res == self.view()[index as int],
    {
        self.entries[index]
    }

    /// Set the value of the entry at the given index.
    pub fn set(&mut self, index: usize, value: u64)
        requires
            0 <= index < N,
        ensures
            self@ == old(self)@.update(index as int, value),
    {
        self.entries[index] = value;
    }
}

/// A 4K byte page table with 512 entries.
pub type Table512 = Table<512>;

/// Permission for a 4K byte page table, which points to a `Table512`.
pub type Table512Perm = PointsTo<Table512>;

/// Update one entry in place through the table's hypervisor virtual address.
///
/// Trusted seam: the exclusive permission identifies a valid, initialized table.
/// The raw store changes exactly one entry; the postcondition records that update
/// while preserving every other entry and the permission's address.
#[verifier::external_body]
#[inline(always)]
pub(super) fn write_table512_entry(
    hva: usize,
    index: usize,
    value: u64,
    Tracked(perm): Tracked<&mut Table512Perm>,
)
    requires
        old(perm).addr() == hva,
        old(perm).is_init(),
        index < 512,
    ensures
        perm.addr() == old(perm).addr(),
        perm.is_init(),
        perm.mem_contents().value()@ == old(perm).mem_contents().value()@.update(index as int, value),
{
    let table_ptr = hva as *mut Table512;
    // SAFETY: `perm` grants exclusive access to the initialized table, and the
    // index is in bounds. Address the field directly without copying the table.
    unsafe {
        core::ptr::addr_of_mut!((*table_ptr).entries[index]).write(value);
    }
}

/// Clear a table in place through its hypervisor virtual address.
///
/// Trusted seam: the exclusive permission identifies a valid, aligned table at
/// `hva`. The raw write clears that allocation, and the postcondition reflects
/// the new contents in the permission. All-zero bytes are valid for its `u64` entries.
#[verifier::external_body]
#[inline(always)]
pub(super) fn clear_table512(hva: usize, Tracked(perm): Tracked<&mut Table512Perm>)
    requires
        old(perm).addr() == hva,
        old(perm).is_init(),
    ensures
        perm.addr() == old(perm).addr(),
        perm.is_init(),
        perm.mem_contents().value().spec_is_empty(),
{
    let table_ptr = hva as *mut Table512;
    // SAFETY: `perm` grants exclusive access to this initialized table. Zero one
    // whole table (4096 bytes) directly, without copying it onto the stack.
    unsafe {
        core::ptr::write_bytes(table_ptr, 0, 1);
    }
}

/// Convert a `Frame4KPerm` reference to a `Table512Perm` reference.
///
/// Trusted seam: this permission conversion reinterprets the same 4K allocation
/// as either `[u8; 4096]` or `Table512` (`[u64; 512]`). This is safe only because
/// both views have the same size and represent the same initialized memory.
#[verifier::external_body]
pub(super) proof fn frame4k_perm_ref_to_table512_perm_ref(
    tracked frame_perm: &Frame4KPerm,
) -> (tracked table_perm: &Table512Perm)
    ensures
        table_perm.addr() == frame_perm.addr(),
        table_perm.is_init() == frame_perm.is_init(),
        table_perm.mem_contents().value()@ == frame4k_to_u64_seq(frame_perm),
{
    let tracked table_perm: Tracked<&Table512Perm> = Tracked::assume_new();
    table_perm@
}

/// Convert a `Frame4KPerm` to a `Table512Perm`.
///
/// Trusted seam: this transfers ownership of the same 4K allocation from the raw
/// frame view to the page-table view. The conversion relies on `Frame4KPerm` and
/// `Table512Perm` having the same allocation size.
#[verifier::external_body]
pub(super) proof fn frame4k_perm_to_table512_perm(
    tracked frame_perm: Frame4KPerm,
) -> (tracked table_perm: Table512Perm)
    ensures
        table_perm.addr() == frame_perm.addr(),
        table_perm.is_init() == frame_perm.is_init(),
        table_perm.mem_contents().value()@ == frame4k_to_u64_seq(&frame_perm),
{
    let tracked table_perm: Tracked<Table512Perm> = Tracked::assume_new();
    table_perm@
}

/// Convert a `Table512Perm` to a `Frame4KPerm`.
///
/// Trusted seam: this is the inverse ownership conversion for the same 4K
/// allocation, relying on the same-size representation of `Table512` and
/// `[u8; 4096]`.
#[verifier::external_body]
pub(super) proof fn table512_perm_to_frame4k_perm(
    tracked table_perm: Table512Perm,
) -> (tracked frame_perm: Frame4KPerm)
    ensures
        frame_perm.addr() == table_perm.addr(),
        frame_perm.is_init() == table_perm.is_init(),
        frame4k_to_u64_seq(&frame_perm) == table_perm.mem_contents().value()@,
{
    let tracked frame_perm: Tracked<Frame4KPerm> = Tracked::assume_new();
    frame_perm@
}

/// Interpret the contents of a `Frame4KPerm` as a sequence of `u64` entries.
pub uninterp spec fn frame4k_to_u64_seq(perm: &Frame4KPerm) -> Seq<u64>;

/// Lemma. The sequence returned by `frame4k_to_u64_seq` has length 512.
pub(super) broadcast proof fn lemma_frame4k_to_u64_seq(perm: &Frame4KPerm)
    ensures
        #[trigger] frame4k_to_u64_seq(perm).len() == 512,
        frame_is_empty(perm) == forall|i: int| 0 <= i < 512 ==> frame4k_to_u64_seq(perm)[i] == 0,
{
    admit();
}

} // verus!
