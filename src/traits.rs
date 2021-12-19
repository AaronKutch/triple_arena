use core::{
    borrow::Borrow,
    fmt,
    ops::{Index, IndexMut},
    slice,
};

use InternalEntry::*;

use crate::{Arena, InternalEntry, Ptr, PtrTrait};

impl<T, P: PtrTrait> Arena<T, P> {
    /// Immutable reference iteration with `(Ptr<P>, &T)` tuples
    pub fn iter(&self) -> Iter<'_, T, P> {
        Iter {
            ptr: 0,
            iter: self.m.iter(),
        }
    }

    /// Mutable reference iteration with `(Ptr<P>, &mut T)` tuples
    pub fn iter_mut(&mut self) -> IterMut<'_, T, P> {
        IterMut {
            ptr: 0,
            iter_mut: self.m.iter_mut(),
        }
    }

    /// By-value iteration with `(Ptr<P>, T)` tuples. Consumes all `T` in `self`
    /// and zeroes capacity.
    pub fn drain(&mut self) -> Drain<'_, T, P> {
        self.len = 0;
        self.freelist_root = None;
        Drain {
            ptr: 0,
            drain: self.m.drain(..),
        }
    }
}

impl<T, P: PtrTrait> Default for Arena<T, P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, P: PtrTrait, B: Borrow<Ptr<P>>> Index<B> for Arena<T, P> {
    type Output = T;

    fn index(&self, inx: B) -> &T {
        let p: Ptr<P> = *inx.borrow();
        self.get(p).expect("indexed arena with invalidated pointer")
    }
}

impl<T, P: PtrTrait, B: Borrow<Ptr<P>>> IndexMut<B> for Arena<T, P> {
    fn index_mut(&mut self, inx: B) -> &mut T {
        let p: Ptr<P> = *inx.borrow();
        self.get_mut(p)
            .expect("indexed arena with invalidated pointer")
    }
}

// Note: we are wrapping around slice iterators because `IterMut` in particular
// would otherwise be difficult to implement safely. There are redundant
// counters but they should be optimized away.

pub struct Iter<'a, T, P: PtrTrait> {
    ptr: usize,
    iter: slice::Iter<'a, InternalEntry<T, P>>,
}

impl<'a, T, P: PtrTrait> Iterator for Iter<'a, T, P> {
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

impl<'a, T, P: PtrTrait> IntoIterator for &'a Arena<T, P> {
    type IntoIter = Iter<'a, T, P>;
    type Item = (Ptr<P>, &'a T);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub struct IterMut<'a, T, P: PtrTrait> {
    ptr: usize,
    iter_mut: slice::IterMut<'a, InternalEntry<T, P>>,
}

impl<'a, T, P: PtrTrait> Iterator for IterMut<'a, T, P> {
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

impl<'a, T, P: PtrTrait> IntoIterator for &'a mut Arena<T, P> {
    type IntoIter = IterMut<'a, T, P>;
    type Item = (Ptr<P>, &'a mut T);

    /// This returns an `IterMut`. Use `Arena::drain` for by-value consumption.
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

pub struct Drain<'a, T, P: PtrTrait> {
    ptr: usize,
    drain: alloc::vec::Drain<'a, InternalEntry<T, P>>,
}

impl<'a, T, P: PtrTrait> Iterator for Drain<'a, T, P> {
    type Item = (Ptr<P>, T);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(next) = self.drain.next() {
            let inx = self.ptr;
            self.ptr += 1;
            if let Allocated(p, t) = next {
                return Some((Ptr::from_raw(inx, PtrTrait::get(&p)), t))
            }
        }
        None
    }
}

impl<T, P: PtrTrait> FromIterator<T> for Arena<T, P> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut a = Arena::new();
        for t in iter {
            a.insert(t);
        }
        a
    }
}

impl<T: fmt::Debug, P: PtrTrait> fmt::Debug for Arena<T, P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}
