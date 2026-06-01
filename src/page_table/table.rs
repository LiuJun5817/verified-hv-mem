//! Page table memory read/write utilities and permission assumptions.
use crate::global_allocator::{Frame4KPerm, frame_is_empty};
use vstd::prelude::*;
use vstd::simple_pptr::PointsTo;

verus! {

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

/// Convert a `Frame4KPerm` referenceto a `Table512Perm` reference. Assume safety.
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

/// Convert a `Table512Perm` to a `Frame4KPerm`. Assume safety.
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

/// Convert a `Table512Perm` to a `Frame4KPerm`. Assume safety.
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
