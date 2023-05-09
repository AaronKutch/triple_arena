use crate::{
    iterators::{self},
    surject::{PVal, Val},
    Arena, Link, Ptr, SurjectArena,
};

/// All the iterators here can return values in arbitrary order
impl<P: Ptr, T> SurjectArena<P, T> {
    /// Iteration over all valid `P` in the arena
    pub fn ptrs(&self) -> Ptrs<P> {
        Ptrs {
            iter: self.keys.ptrs(),
        }
    }

    /// Iteration over `&T`
    pub fn vals(&self) -> Vals<T> {
        Vals {
            iter: self.vals.vals(),
        }
    }

    /// Mutable iteration over `&mut T`
    pub fn vals_mut(&mut self) -> ValsMut<T> {
        ValsMut {
            iter_mut: self.vals.vals_mut(),
        }
    }

    /// Iteration over `(P, &T)` tuples. For each surject with multiple `P`
    /// pointing to the same `T`, the `T` side is repeated multiple times (but
    /// remember this can be out of order)
    pub fn iter(&self) -> Iter<P, T> {
        Iter {
            iter: self.keys.iter(),
            vals: &self.vals,
        }
    }

    /*
    /// Mutable iteration over `(P, &mut T)` tuples
    pub fn iter_mut(&mut self) -> IterMut<P, T> {
        IterMut {
            iter: self.keys.iter(),
            vals_mut: &mut self.vals,
        }
    }
    */

    // we cannot possibly implement by-value `T` stuff

    /// Same as [Arena::first_ptr]
    #[must_use]
    pub fn first_ptr(&self) -> (P, bool) {
        self.keys.first_ptr()
    }

    /// Same as [Arena::next_ptr]
    pub fn next_ptr(&self, p: &mut P, b: &mut bool) {
        self.keys.next_ptr(p, b)
    }
}

// we need custom iterators like this because the `T` is required in the
// generics, and if we used the underlying `ChainArena` it would bring in the
// wrong things

/// An iterator over the valid `P`s of a `SurjectArena`
pub struct Ptrs<'a, P: Ptr> {
    iter: iterators::Ptrs<'a, P, Link<P, PVal>>,
}

impl<'a, P: Ptr> Iterator for Ptrs<'a, P> {
    type Item = P;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

/// An iterator over `&T` in a `SurjectArena`
pub struct Vals<'a, T> {
    iter: iterators::Vals<'a, PVal, Val<T>>,
}

impl<'a, T> Iterator for Vals<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|v| &v.t)
    }
}

/// A mutable iterator over `&mut T` in a `SurjectArena`
pub struct ValsMut<'a, T> {
    iter_mut: iterators::ValsMut<'a, PVal, Val<T>>,
}

impl<'a, T> Iterator for ValsMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_mut.next().map(|v| &mut v.t)
    }
}

/// An iterator over `(P, &T)` in a `SurjectArena`
pub struct Iter<'a, P: Ptr, T> {
    iter: iterators::Iter<'a, P, Link<P, PVal>>,
    vals: &'a Arena<PVal, Val<T>>,
}

impl<'a, P: Ptr, T> Iterator for Iter<'a, P, T> {
    type Item = (P, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        let (p, p_val) = self.iter.next()?;
        Some((p, &self.vals.get(p_val.t).unwrap().t))
    }
}

// TODO we are running into the `IterMut` problem
/*
/// An iterator over `(P, &mut T)` in a `SurjectArena`
pub struct IterMut<'a, P: Ptr, T> {
    iter: iterators::Iter<'a, P, Link<P, PVal>>,
    vals_mut: &'a mut Arena<PVal, Val<T>>,
}

impl<'a, P: Ptr, T> Iterator for IterMut<'a, P, T> {
    type Item = (P, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        let (p, p_val) = self.iter.next()?;
        let tmp = &mut self.vals_mut.get_mut(p_val.t).unwrap().t;
        Some((p, tmp))
    }
}
*/
