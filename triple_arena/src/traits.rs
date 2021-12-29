use core::{
    borrow::Borrow,
    fmt, mem,
    ops::{Index, IndexMut},
    slice,
};

use InternalEntry::*;

use crate::{Arena, InternalEntry, Ptr, PtrTrait};

impl<P: PtrTrait, T> Arena<P, T> {
    /// Immutable reference iteration with `(Ptr<P>, &T)` tuples
    pub fn iter(&self) -> Iter<P, T> {
        Iter {
            ptr: 0,
            iter: self.m.iter(),
        }
    }

    /// Mutable reference iteration with `(Ptr<P>, &mut T)` tuples
    pub fn iter_mut(&mut self) -> IterMut<P, T> {
        IterMut {
            ptr: 0,
            iter_mut: self.m.iter_mut(),
        }
    }

    /// By-value iteration with `(Ptr<P>, T)` tuples. Consumes all `T` in
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
            self.freelist_root = Some(0);
        }
        self.len = 0;
        self.inc_gen();
        Drain {
            ptr: 0,
            arena: self,
        }
    }

    // This is needed for the `impl IntoIterator for Arena<T, P>` trait

    /// By-value iteration with `(Ptr<P>, T)` tuples. Consumes all `T` and
    /// capacity.
    pub fn total_drain(self) -> TotalDrain<P, T> {
        TotalDrain {
            ptr: 0,
            arena: self,
        }
    }
}

impl<T, P: PtrTrait> Default for Arena<P, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P: PtrTrait, T, B: Borrow<Ptr<P>>> Index<B> for Arena<P, T> {
    type Output = T;

    fn index(&self, inx: B) -> &T {
        let p: Ptr<P> = *inx.borrow();
        self.get(p).expect("indexed arena with invalidated pointer")
    }
}

impl<P: PtrTrait, T, B: Borrow<Ptr<P>>> IndexMut<B> for Arena<P, T> {
    fn index_mut(&mut self, inx: B) -> &mut T {
        let p: Ptr<P> = *inx.borrow();
        self.get_mut(p)
            .expect("indexed arena with invalidated pointer")
    }
}

// Note: we are wrapping around slice iterators because `IterMut` in particular
// would otherwise be difficult to implement safely. There are redundant
// counters but they should be optimized away.

pub struct Iter<'a, P: PtrTrait, T> {
    ptr: usize,
    iter: slice::Iter<'a, InternalEntry<P, T>>,
}

impl<'a, P: PtrTrait, T> Iterator for Iter<'a, P, T> {
    type Item = (Ptr<P>, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(next) = self.iter.next() {
            let inx = self.ptr;
            self.ptr += 1;
            if let Allocated(p, t) = next {
                return Some((Ptr::from_raw(inx, PtrTrait::get(p)), t))
            }
        }
        None
    }
}

impl<'a, P: PtrTrait, T> IntoIterator for &'a Arena<P, T> {
    type IntoIter = Iter<'a, P, T>;
    type Item = (Ptr<P>, &'a T);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub struct IterMut<'a, P: PtrTrait, T> {
    ptr: usize,
    iter_mut: slice::IterMut<'a, InternalEntry<P, T>>,
}

impl<'a, P: PtrTrait, T> Iterator for IterMut<'a, P, T> {
    type Item = (Ptr<P>, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(next) = self.iter_mut.next() {
            let inx = self.ptr;
            self.ptr += 1;
            if let Allocated(p, t) = next {
                return Some((Ptr::from_raw(inx, PtrTrait::get(p)), t))
            }
        }
        None
    }
}

impl<'a, P: PtrTrait, T> IntoIterator for &'a mut Arena<P, T> {
    type IntoIter = IterMut<'a, P, T>;
    type Item = (Ptr<P>, &'a mut T);

    /// This returns an `IterMut`. Use `Arena::drain` for by-value consumption.
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

pub struct Drain<'a, P: PtrTrait, T> {
    ptr: usize,
    arena: &'a mut Arena<P, T>,
}

impl<'a, P: PtrTrait, T> Iterator for Drain<'a, P, T> {
    type Item = (Ptr<P>, T);

    fn next(&mut self) -> Option<Self::Item> {
        let len = self.arena.m.len();
        while let Some(tmp) = self.arena.m.get_mut(self.ptr) {
            let inx = self.ptr;
            self.ptr += 1;
            let freelist_node = if self.ptr == len {
                Free(inx)
            } else {
                // set last free to point to itself
                Free(self.ptr)
            };
            let allocation = mem::replace(tmp, freelist_node);
            if let Allocated(p, t) = allocation {
                return Some((Ptr::from_raw(inx, PtrTrait::get(&p)), t))
            }
        }
        None
    }
}

pub struct TotalDrain<P: PtrTrait, T> {
    ptr: usize,
    arena: Arena<P, T>,
}

impl<T, P: PtrTrait> Iterator for TotalDrain<P, T> {
    type Item = (Ptr<P>, T);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(tmp) = self.arena.m.get_mut(self.ptr) {
            let inx = self.ptr;
            self.ptr += 1;
            // the freelist no longer matters because the `Arena` is guaranteed to be
            // dropped or never accessed outside of this iterator again.
            let allocation = mem::replace(tmp, Free(0));
            if let Allocated(p, t) = allocation {
                return Some((Ptr::from_raw(inx, PtrTrait::get(&p)), t))
            }
        }
        None
    }
}

impl<P: PtrTrait, T> IntoIterator for Arena<P, T> {
    type IntoIter = TotalDrain<P, T>;
    type Item = (Ptr<P>, T);

    fn into_iter(self) -> Self::IntoIter {
        self.total_drain()
    }
}

impl<P: PtrTrait, T> FromIterator<T> for Arena<P, T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut a = Arena::new();
        for t in iter {
            a.insert(t);
        }
        a
    }
}

impl<P: PtrTrait, T: fmt::Debug> fmt::Debug for Arena<P, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}