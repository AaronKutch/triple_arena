use core::mem;

use InternalEntry::*;

use crate::Ptr;

/// Internal entry for an `Arena`.
#[derive(Clone)]
pub(crate) enum InternalEntry<P: Ptr, T> {
    /// A free entry with no `T`. The `usize` points to the next free entry,
    /// except if it points to the self entry in which case it is the last free
    /// entry.
    Free(P::Inx),
    /// An entry allocated for a `(P::Gen, T)` pair in the arena.
    Allocated(P::Gen, T),
}

impl<P: Ptr, T> InternalEntry<P, T> {
    #[inline]
    pub fn replace_free_with_allocated(&mut self, gen: P::Gen, t: T) -> Option<P::Inx> {
        let free = mem::replace(self, Allocated(gen, t));
        if let Free(free) = free {
            Some(free)
        } else {
            None
        }
    }

    // no `replace_allocated_with_free`, it is too easy to introduce invariant
    // breakage
}
