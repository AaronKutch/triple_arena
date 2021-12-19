use core::mem;

use InternalEntry::*;

use crate::PtrTrait;

/// Internal entry for an `Arena`.
#[derive(Clone)]
pub(crate) enum InternalEntry<T, P: PtrTrait> {
    /// A free entry with no `T`. The `usize` points to the next free entry,
    /// except if it points to the self entry in which case it is the last free
    /// entry.
    Free(usize),
    /// An entry allocated for a `(P, T)` pair in the arena.
    Allocated(P, T),
}

impl<T, P: PtrTrait> InternalEntry<T, P> {
    #[inline]
    pub fn replace_free_with_allocated(&mut self, gen_element: (P, T)) -> Option<usize> {
        let free = mem::replace(self, Allocated(gen_element.0, gen_element.1));
        if let Free(free) = free {
            Some(free)
        } else {
            None
        }
    }

    // no `replace_allocated_with_free`, it is too easy to introduce invariant
    // breakage
}
