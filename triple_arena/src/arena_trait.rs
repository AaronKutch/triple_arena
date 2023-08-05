use crate::{
    chain_iterators, iterators, ord_iterators, surject_iterators, Advancer, Arena, ChainArena,
    Link, OrdArena, Ptr, SurjectArena,
};

/// A trait that encapsulates some common functions across the different arena
/// types. Intended for functions that want to be generic over the arenas.
pub trait ArenaTrait {
    /// The `Ptr` type
    type P: Ptr;
    /// The element type
    type E;
    type Adv: Advancer;

    fn new() -> Self;
    fn capacity(&self) -> usize;
    fn gen(&self) -> <<Self as ArenaTrait>::P as Ptr>::Gen;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn insert(&mut self, e: Self::E) -> Self::P;
    fn remove(&mut self, p: Self::P) -> Option<Self::E>;
    fn get(&self, p: Self::P) -> Option<&Self::E>;
    fn advancer(&self) -> Self::Adv;
    fn contains(&self, p: Self::P) -> bool;
    fn clear(&mut self);
    fn clear_and_shrink(&mut self);
}

impl<P: Ptr, T> ArenaTrait for Arena<P, T> {
    type Adv = iterators::PtrAdvancer<P, T>;
    type E = T;
    type P = P;

    fn new() -> Self {
        Self::new()
    }

    fn capacity(&self) -> usize {
        self.capacity()
    }

    fn gen(&self) -> P::Gen {
        self.gen()
    }

    fn len(&self) -> usize {
        self.len()
    }

    fn is_empty(&self) -> bool {
        self.is_empty()
    }

    fn insert(&mut self, e: Self::E) -> P {
        self.insert(e)
    }

    fn remove(&mut self, p: Self::P) -> Option<Self::E> {
        self.remove(p)
    }

    fn get(&self, p: Self::P) -> Option<&Self::E> {
        self.get(p)
    }

    fn advancer(&self) -> Self::Adv {
        self.advancer()
    }

    fn contains(&self, p: Self::P) -> bool {
        self.contains(p)
    }

    fn clear(&mut self) {
        self.clear()
    }

    fn clear_and_shrink(&mut self) {
        self.clear_and_shrink()
    }
}

impl<P: Ptr, T> ArenaTrait for ChainArena<P, T> {
    type Adv = chain_iterators::PtrAdvancer<P, T>;
    type E = Link<P, T>;
    type P = P;

    fn new() -> Self {
        Self::new()
    }

    fn capacity(&self) -> usize {
        self.capacity()
    }

    fn gen(&self) -> P::Gen {
        self.gen()
    }

    fn len(&self) -> usize {
        self.len()
    }

    fn is_empty(&self) -> bool {
        self.is_empty()
    }

    /// Uses [ChainArena::insert] with `link.prev_next()` and `link.t`
    fn insert(&mut self, link: Self::E) -> P {
        if let Ok(p) = self.insert(link.prev_next(), link.t) {
            p
        } else {
            unreachable!()
        }
    }

    fn remove(&mut self, p: Self::P) -> Option<Self::E> {
        self.remove(p)
    }

    fn get(&self, p: Self::P) -> Option<&Self::E> {
        self.get_link(p)
    }

    fn advancer(&self) -> Self::Adv {
        self.advancer()
    }

    fn contains(&self, p: Self::P) -> bool {
        self.contains(p)
    }

    fn clear(&mut self) {
        self.clear()
    }

    fn clear_and_shrink(&mut self) {
        self.clear_and_shrink()
    }
}

impl<P: Ptr, K> ArenaTrait for SurjectArena<P, K, ()> {
    type Adv = surject_iterators::PtrAdvancer<P, K, ()>;
    type E = K;
    type P = P;

    fn new() -> Self {
        Self::new()
    }

    fn capacity(&self) -> usize {
        self.capacity_keys()
    }

    fn gen(&self) -> P::Gen {
        self.gen()
    }

    fn len(&self) -> usize {
        self.len_keys()
    }

    fn is_empty(&self) -> bool {
        self.is_empty()
    }

    fn insert(&mut self, e: Self::E) -> P {
        self.insert(e, ())
    }

    fn remove(&mut self, p: Self::P) -> Option<Self::E> {
        self.remove_key(p).map(|tmp| tmp.0)
    }

    fn get(&self, p: Self::P) -> Option<&Self::E> {
        self.get_key(p)
    }

    fn advancer(&self) -> Self::Adv {
        self.advancer()
    }

    fn contains(&self, p: Self::P) -> bool {
        self.contains(p)
    }

    fn clear(&mut self) {
        self.clear()
    }

    fn clear_and_shrink(&mut self) {
        self.clear_and_shrink()
    }
}

impl<P: Ptr, K: Ord, V> ArenaTrait for OrdArena<P, K, V> {
    type Adv = ord_iterators::PtrAdvancer<P, K, V>;
    type E = (K, V);
    type P = P;

    fn new() -> Self {
        Self::new()
    }

    fn capacity(&self) -> usize {
        self.capacity()
    }

    fn gen(&self) -> P::Gen {
        self.gen()
    }

    fn len(&self) -> usize {
        self.len()
    }

    fn is_empty(&self) -> bool {
        self.is_empty()
    }

    /// Uses the hereditary insert
    fn insert(&mut self, e: Self::E) -> P {
        self.insert(e).0
    }

    fn remove(&mut self, p: Self::P) -> Option<Self::E> {
        self.remove(p).map(|link| link.t)
    }

    fn get(&self, p: Self::P) -> Option<&Self::E> {
        self.get(p)
    }

    fn advancer(&self) -> Self::Adv {
        self.advancer()
    }

    fn contains(&self, p: Self::P) -> bool {
        self.contains(p)
    }

    fn clear(&mut self) {
        self.clear()
    }

    fn clear_and_shrink(&mut self) {
        self.clear_and_shrink()
    }
}
