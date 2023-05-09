//! Iterators for `Arena`

use core::{mem, slice};

use InternalEntry::*;

use crate::{Arena, ChainArena, InternalEntry, Link, Ptr, PtrInx};

/// All the iterators here can return values in arbitrary order
impl<P: Ptr, T> Arena<P, T> {
    /// Iteration over all valid `P` in the arena
    pub fn ptrs(&self) -> Ptrs<P, T> {
        Ptrs {
            ptr: P::Inx::new(0),
            iter: self.m.iter(),
        }
    }

    /// Iteration over `&T`
    pub fn vals(&self) -> Vals<P, T> {
        Vals {
            ptr: P::Inx::new(0),
            iter: self.m.iter(),
        }
    }

    /// Mutable iteration over `&mut T`
    pub fn vals_mut(&mut self) -> ValsMut<P, T> {
        ValsMut {
            ptr: P::Inx::new(0),
            iter_mut: self.m.iter_mut(),
        }
    }

    /// Iteration over `(P, &T)` tuples
    pub fn iter(&self) -> Iter<P, T> {
        Iter {
            ptr: P::Inx::new(0),
            iter: self.m.iter(),
        }
    }

    /// Mutable iteration over `(P, &mut T)` tuples
    pub fn iter_mut(&mut self) -> IterMut<P, T> {
        IterMut {
            ptr: P::Inx::new(0),
            iter_mut: self.m.iter_mut(),
        }
    }

    /// By-value iteration over `(P, T)` tuples. Consumes all `T` in
    /// `self`, but retains capacity.
    ///
    /// Note: When the `Drain` struct is dropped, any remaining iterations will
    /// be consumed and dropped like normal. If the `Drain` struct is leaked
    /// (such as with [mem::forget]), unspecified behavior will result.
    pub fn drain(&mut self) -> Drain<P, T> {
        // prep the length and root to be how they need to be when `Drain` is dropped or
        // leaked
        if self.m.is_empty() {
            self.freelist_root = None;
        } else {
            self.freelist_root = Some(P::Inx::new(0));
        }
        self.len = 0;
        self.inc_gen();
        Drain {
            ptr: P::Inx::new(0),
            arena: self,
        }
    }

    // This is needed for the `impl IntoIterator for Arena<T, P>` trait

    /// By-value iteration with `(P, T)` tuples. Consumes all `T` and
    /// capacity.
    pub fn capacity_drain(self) -> CapacityDrain<P, T> {
        CapacityDrain {
            ptr: P::Inx::new(0),
            arena: self,
        }
    }

    /// Returns a `P` intended for use with [Arena::next_ptr] in a loop. Note
    /// that the `P` can be invalid and the boolean true if the arena is empty.
    #[must_use]
    pub fn first_ptr(&self) -> (P, bool) {
        if self.is_empty() {
            (P::invalid(), true)
        } else {
            for (i, e) in self.m.iter().enumerate() {
                if let Allocated(g, _) = e {
                    return (P::_from_raw(P::Inx::new(i), *g), false)
                }
            }
            unreachable!()
        }
    }

    /// Used to avoid borrowing conflicts in complicated iterative algorithms.
    /// This function does exactly one of two things depending on if a next
    /// valid `P` exists in the iteration sequence: updates `p` to the
    /// next valid `P` if one exists, or updates `b` to `true` otherwise.
    ///
    /// The motivation of this function is that often in algorithms being
    /// applied to the whole `Arena`, the user will need to call
    /// `.ptrs().collect()` and allocate just to avoid borrowing conflicts
    /// between the iteration and arbitrary mutations on the arena. In a
    /// typical structure such as a `Vec`, you can do
    ///
    /// ```text
    /// let mut i = 0;
    /// loop {
    ///     if i >= vec.len() {
    ///         break
    ///     }
    ///     ... vec.get(i) ...
    ///     ... vec.get_mut(i) ...
    ///     ... vec.get(any_i) ...
    ///     ... vec.get_mut(any_i) ...
    ///
    ///     i += 1;
    /// }
    /// ```
    ///
    /// This function allows an analogous loop strategy:
    ///
    /// ```text
    /// // a boolean is used for the termination condition to account for
    /// // non-generation-counter cases where all possible `Ptr`s would be valid
    /// let (mut p, mut b) = arena.first_ptr();
    /// loop {
    ///     if b {
    ///         break
    ///     }
    ///     ... arena.get(p) ...
    ///     ... arena.get_mut(p) ...
    ///     ... arena.get(any_ptr) ...
    ///     ... arena.get_mut(any_ptr) ...
    ///     // any kind of invalidation operation is ok (including the current `p`,
    ///     // it will not break `next_ptr` or prevent the loop from witnessing a
    ///     // continuously valid element inserted from before the loop began),
    ///     ... arena.remove(p) ...
    ///     // but note that new elements from insertions done during the loop, can
    ///     // both be encountered or not encountered before the loop terminates.
    ///     ... let p_inserted = arena.insert(node) ...
    ///
    ///     arena.next_ptr(&mut p, &mut b);
    /// }
    /// ```
    pub fn next_ptr(&self, p: &mut P, b: &mut bool) {
        for i in P::Inx::get(p.inx()).checked_add(1).unwrap()..self.m.len() {
            if let Allocated(g, _) = self.m.get(i).unwrap() {
                *p = P::_from_raw(P::Inx::new(i), *g);
                return
            }
        }
        *b = true;
    }
}

impl<PLink: Ptr, T> ChainArena<PLink, T> {
    /// Iteration over all valid `PLink`s in the arena
    pub fn ptrs(&self) -> Ptrs<PLink, Link<PLink, T>> {
        self.a.ptrs()
    }

    /// Iteration over `&Link<PLink, T>`
    pub fn vals(&self) -> Vals<PLink, Link<PLink, T>> {
        self.a.vals()
    }

    /// Mutable iteration over `Link<PLink, &mut T>`
    pub fn vals_mut(&mut self) -> ValsLinkMut<PLink, T> {
        ValsLinkMut {
            iter_mut: self.a.vals_mut(),
        }
    }

    /// Iteration over `(PLink, &Link<PLink, T>)` tuples
    pub fn iter(&self) -> Iter<PLink, Link<PLink, T>> {
        self.a.iter()
    }

    /// Mutable iteration over `(PLink, Link<PLink, &mut T>)` tuples
    pub fn iter_mut(&mut self) -> IterLinkMut<PLink, T> {
        IterLinkMut {
            iter_mut: self.a.iter_mut(),
        }
    }

    /// Same as [Arena::drain]
    pub fn drain(&mut self) -> Drain<PLink, Link<PLink, T>> {
        self.a.drain()
    }

    /// Same as [Arena::capacity_drain]
    pub fn capacity_drain(self) -> CapacityDrain<PLink, Link<PLink, T>> {
        self.a.capacity_drain()
    }

    /// Same as [Arena::first_ptr]
    #[must_use]
    pub fn first_ptr(&self) -> (PLink, bool) {
        self.a.first_ptr()
    }

    /// Same as [Arena::next_ptr]
    pub fn next_ptr(&self, p: &mut PLink, b: &mut bool) {
        self.a.next_ptr(p, b);
    }
}

// Note: we are wrapping around slice iterators because `IterMut` in particular
// would otherwise be difficult to implement safely. There are redundant
// counters but they should be optimized away.

/// An iterator over the valid `P`s of an `Arena`
pub struct Ptrs<'a, P: Ptr, T> {
    ptr: P::Inx,
    iter: slice::Iter<'a, InternalEntry<P, T>>,
}

impl<'a, P: Ptr, T> Iterator for Ptrs<'a, P, T> {
    type Item = P;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(next) = self.iter.next() {
            let inx = self.ptr;
            self.ptr = P::Inx::new(P::Inx::get(self.ptr).wrapping_add(1));
            if let Allocated(g, _) = next {
                return Some(P::_from_raw(inx, *g))
            }
        }
        None
    }
}

/// An iterator over `&T` in an `Arena`
pub struct Vals<'a, P: Ptr, T> {
    ptr: P::Inx,
    iter: slice::Iter<'a, InternalEntry<P, T>>,
}

impl<'a, P: Ptr, T> Iterator for Vals<'a, P, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(next) = self.iter.next() {
            self.ptr = P::Inx::new(P::Inx::get(self.ptr).wrapping_add(1));
            if let Allocated(_, t) = next {
                return Some(t)
            }
        }
        None
    }
}

/// A mutable iterator over `&mut T` in an `Arena`
pub struct ValsMut<'a, P: Ptr, T> {
    ptr: P::Inx,
    iter_mut: slice::IterMut<'a, InternalEntry<P, T>>,
}

impl<'a, P: Ptr, T> Iterator for ValsMut<'a, P, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(next) = self.iter_mut.next() {
            self.ptr = P::Inx::new(P::Inx::get(self.ptr).wrapping_add(1));
            if let Allocated(_, t) = next {
                return Some(t)
            }
        }
        None
    }
}

/// An iterator over `Link<P, &mut T>` in a `ChainArena`
pub struct ValsLinkMut<'a, P: Ptr, T> {
    iter_mut: ValsMut<'a, P, Link<P, T>>,
}

impl<'a, P: Ptr, T> Iterator for ValsLinkMut<'a, P, T> {
    type Item = Link<P, &'a mut T>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_mut
            .next()
            .map(|link| Link::new(Link::prev_next(link), &mut link.t))
    }
}

/// An iterator over `(P, &T)` in an `Arena`
pub struct Iter<'a, P: Ptr, T> {
    ptr: P::Inx,
    iter: slice::Iter<'a, InternalEntry<P, T>>,
}

impl<'a, P: Ptr, T> Iterator for Iter<'a, P, T> {
    type Item = (P, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(next) = self.iter.next() {
            let inx = self.ptr;
            self.ptr = P::Inx::new(P::Inx::get(self.ptr).wrapping_add(1));
            if let Allocated(g, t) = next {
                return Some((P::_from_raw(inx, *g), t))
            }
        }
        None
    }
}

impl<'a, P: Ptr, T> IntoIterator for &'a Arena<P, T> {
    type IntoIter = Iter<'a, P, T>;
    type Item = (P, &'a T);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// A mutable iterator over `(P, &mut T)` in an `Arena`
pub struct IterMut<'a, P: Ptr, T> {
    ptr: P::Inx,
    iter_mut: slice::IterMut<'a, InternalEntry<P, T>>,
}

impl<'a, P: Ptr, T> Iterator for IterMut<'a, P, T> {
    type Item = (P, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(next) = self.iter_mut.next() {
            let inx = self.ptr;
            self.ptr = P::Inx::new(P::Inx::get(self.ptr).wrapping_add(1));
            if let Allocated(g, t) = next {
                return Some((P::_from_raw(inx, *g), t))
            }
        }
        None
    }
}

/// A mutable iterator over `(P, Link<P, &mut T>)` in a `ChainArena`
pub struct IterLinkMut<'a, P: Ptr, T> {
    iter_mut: IterMut<'a, P, Link<P, T>>,
}

impl<'a, P: Ptr, T> Iterator for IterLinkMut<'a, P, T> {
    type Item = (P, Link<P, &'a mut T>);

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_mut
            .next()
            .map(|(p, link)| (p, Link::new(Link::prev_next(link), &mut link.t)))
    }
}

impl<'a, P: Ptr, T> IntoIterator for &'a mut Arena<P, T> {
    type IntoIter = IterMut<'a, P, T>;
    type Item = (P, &'a mut T);

    /// This returns an `IterMut`. Use `Arena::drain` for by-value consumption.
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// A draining iterator over `(P, T)` in an `Arena`
pub struct Drain<'a, P: Ptr, T> {
    ptr: P::Inx,
    arena: &'a mut Arena<P, T>,
}

impl<'a, P: Ptr, T> Iterator for Drain<'a, P, T> {
    type Item = (P, T);

    fn next(&mut self) -> Option<Self::Item> {
        let len = self.arena.m.len();
        while let Some(tmp) = self.arena.m_get_mut(self.ptr) {
            let inx = self.ptr;
            self.ptr = P::Inx::new(P::Inx::get(self.ptr).wrapping_add(1));
            let freelist_node = if self.ptr == P::Inx::new(len) {
                Free(inx)
            } else {
                // set last free to point to itself
                Free(self.ptr)
            };
            let allocation = mem::replace(tmp, freelist_node);
            if let Allocated(g, t) = allocation {
                return Some((P::_from_raw(inx, g), t))
            }
        }
        None
    }
}

/// A capacity draining iterator over `(P, T)` in an `Arena`
pub struct CapacityDrain<P: Ptr, T> {
    ptr: P::Inx,
    arena: Arena<P, T>,
}

impl<T, P: Ptr> Iterator for CapacityDrain<P, T> {
    type Item = (P, T);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(tmp) = self.arena.m_get_mut(self.ptr) {
            let inx = self.ptr;
            self.ptr = P::Inx::new(P::Inx::get(self.ptr).wrapping_add(1));
            // the freelist no longer matters because the `Arena` is guaranteed to be
            // dropped or never accessed outside of this iterator again.
            let allocation = mem::replace(tmp, Free(P::Inx::new(0)));
            if let Allocated(g, t) = allocation {
                return Some((P::_from_raw(inx, g), t))
            }
        }
        None
    }
}

impl<P: Ptr, T> IntoIterator for Arena<P, T> {
    type IntoIter = CapacityDrain<P, T>;
    type Item = (P, T);

    fn into_iter(self) -> Self::IntoIter {
        self.capacity_drain()
    }
}

impl<P: Ptr, T> FromIterator<T> for Arena<P, T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut a = Arena::new();
        for t in iter {
            a.insert(t);
        }
        a
    }
}

impl<'a, P: Ptr, T> IntoIterator for &'a ChainArena<P, T> {
    type IntoIter = Iter<'a, P, Link<P, T>>;
    type Item = (P, &'a Link<P, T>);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, P: Ptr, T> IntoIterator for &'a mut ChainArena<P, T> {
    type IntoIter = IterLinkMut<'a, P, T>;
    type Item = (P, Link<P, &'a mut T>);

    /// This returns an `IterMut`. Use `ChainArena::drain` for by-value
    /// consumption.
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}
