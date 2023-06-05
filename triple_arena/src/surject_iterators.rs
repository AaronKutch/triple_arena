use crate::{
    iterators::{self},
    surject::{Key, PVal, Val},
    Arena, Link, Ptr, SurjectArena,
};

/// All the iterators here can return values in arbitrary order
impl<P: Ptr, K, V> SurjectArena<P, K, V> {
    /// Iteration over all valid `P` in the arena
    pub fn ptrs(&self) -> Ptrs<P, K> {
        Ptrs {
            iter: self.keys.ptrs(),
        }
    }

    /// Iteration over `&K`
    pub fn keys(&self) -> Keys<P, K> {
        Keys {
            iter: self.keys.vals(),
        }
    }

    /// Iteration over `&V`
    pub fn vals(&self) -> Vals<V> {
        Vals {
            iter: self.vals.vals(),
        }
    }

    /// Mutable iteration over `&mut K`
    pub fn keys_mut(&mut self) -> KeysMut<P, K> {
        KeysMut {
            iter_mut: self.keys.vals_mut(),
        }
    }

    /// Mutable iteration over `&mut V`
    pub fn vals_mut(&mut self) -> ValsMut<V> {
        ValsMut {
            iter_mut: self.vals.vals_mut(),
        }
    }

    /// Iteration over `(P, &K, &V)` tuples. For each surject with multiple `P`
    /// pointing to the same `V`, the same reference to the `V` is returned
    /// multiple times
    pub fn iter(&self) -> Iter<P, K, V> {
        Iter {
            iter: self.keys.iter(),
            vals: &self.vals,
        }
    }

    /// Iteration over `(P, &K, &V)` tuples in the surject that contains `p`.
    /// The same `&V` reference is used for all iterations.
    pub fn iter_surject(&self, p: P) -> IterSurject<P, K, V> {
        IterSurject {
            arena: self,
            surject_val: self.get_val(p),
            init: p,
            p,
            stop: !self.contains(p),
        }
    }

    /// Same as [Arena::first_ptr]
    #[must_use]
    pub fn first_ptr(&self) -> (P, bool) {
        self.keys.first_ptr()
    }

    /// Same as [Arena::next_ptr]
    pub fn next_ptr(&self, p: &mut P, b: &mut bool) {
        self.keys.next_ptr(p, b)
    }

    /// Same as [ChainArena::next_chain_ptr] except it explores a surject.
    ///
    /// ```text
    /// let init = ...;
    /// let mut p = init;
    /// let mut stop = !arena.contains(init);
    /// loop {
    ///     if stop {
    ///         break
    ///     }
    ///
    ///     // use `p` here, but be aware that the removal or insertion of
    ///     // elements within the surject of `init` is not supported
    ///
    ///     arena.next_surject_ptr(init, &mut p, &mut stop);
    /// }
    /// ```
    pub fn next_surject_ptr(&self, init: P, p: &mut P, stop: &mut bool) {
        let next = if let Some(link) = self.keys.get(*p) {
            Link::next(link).unwrap()
        } else {
            *stop = true;
            return
        };
        if next == init {
            // reached the end
            *stop = true;
            return
        }
        *p = next;
    }
}

// we need custom iterators like this because the `T` is required in the
// generics, and if we used the underlying `ChainArena` it would bring in the
// wrong things

/// An iterator over the valid `P`s of a `SurjectArena`
pub struct Ptrs<'a, P: Ptr, K> {
    iter: iterators::Ptrs<'a, P, Link<P, Key<K>>>,
}

impl<'a, P: Ptr, K> Iterator for Ptrs<'a, P, K> {
    type Item = P;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

/// An iterator over `&K` in a `SurjectArena`
pub struct Keys<'a, P: Ptr, K> {
    iter: iterators::Vals<'a, P, Link<P, Key<K>>>,
}

impl<'a, P: Ptr, K> Iterator for Keys<'a, P, K> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|k| &k.k)
    }
}

/// An iterator over `&V` in a `SurjectArena`
pub struct Vals<'a, V> {
    iter: iterators::Vals<'a, PVal, Val<V>>,
}

impl<'a, V> Iterator for Vals<'a, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|v| &v.v)
    }
}

/// A mutable iterator over `&mut K` in a `SurjectArena`
pub struct KeysMut<'a, P: Ptr, K> {
    iter_mut: iterators::ValsLinkMut<'a, P, Key<K>>,
}

impl<'a, P: Ptr, K> Iterator for KeysMut<'a, P, K> {
    type Item = &'a mut K;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_mut.next().map(|link| &mut link.t.k)
    }
}

/// A mutable iterator over `&mut V` in a `SurjectArena`
pub struct ValsMut<'a, V> {
    iter_mut: iterators::ValsMut<'a, PVal, Val<V>>,
}

impl<'a, V> Iterator for ValsMut<'a, V> {
    type Item = &'a mut V;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter_mut.next().map(|v| &mut v.v)
    }
}

/// An iterator over `(P, &K, &V)` in a `SurjectArena`
pub struct Iter<'a, P: Ptr, K, V> {
    iter: iterators::Iter<'a, P, Link<P, Key<K>>>,
    vals: &'a Arena<PVal, Val<V>>,
}

impl<'a, P: Ptr, K, V> Iterator for Iter<'a, P, K, V> {
    type Item = (P, &'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let (p, link) = self.iter.next()?;
        Some((p, &link.t.k, &self.vals.get(link.t.p_val).unwrap().v))
    }
}

/// An iterator over `(P, &K, &V)` in a `SurjectArena` surject
pub struct IterSurject<'a, P: Ptr, K, V> {
    arena: &'a SurjectArena<P, K, V>,
    surject_val: Option<&'a V>,
    init: P,
    p: P,
    stop: bool,
}

impl<'a, P: Ptr, K, V> Iterator for IterSurject<'a, P, K, V> {
    type Item = (P, &'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if self.stop {
            None
        } else {
            let p_res = self.p;
            self.arena
                .next_surject_ptr(self.init, &mut self.p, &mut self.stop);
            Some((
                p_res,
                self.arena.get_key(p_res).unwrap(),
                self.surject_val.unwrap(),
            ))
        }
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
