use crate::{
    arena_iterators, chain_iterators, ord_iterators, surject_iterators,
    utils::{chain_no_gen_iterators, ChainNoGenArena, LinkNoGen},
    Advancer, Arena, ChainArena, Link, OrdArena, Ptr, SurjectArena,
};

/// A trait that encapsulates some common functions across the different arena
/// types. Intended for functions that want to be generic over the arenas.
pub trait ArenaTrait {
    /// The `Ptr` type
    type P: Ptr;
    /// The element type
    type E;
    type GetRes<'a>
    where
        Self: 'a;
    type GetMutRes<'a>
    where
        Self: 'a;
    type Adv: Advancer;

    fn new() -> Self;
    fn capacity(&self) -> usize;
    fn generation(&self) -> <<Self as ArenaTrait>::P as Ptr>::Gen;
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn insert(&mut self, e: Self::E) -> Self::P;
    fn remove(&mut self, p: Self::P) -> Option<Self::E>;
    fn get(&self, p: Self::P) -> Option<Self::GetRes<'_>>;
    fn get_mut(&mut self, p: Self::P) -> Option<Self::GetMutRes<'_>>;
    fn advancer(&self) -> Self::Adv;
    fn contains(&self, p: Self::P) -> bool;
    fn clear(&mut self);
    fn clear_and_shrink(&mut self);
}

impl<P: Ptr, T> ArenaTrait for Arena<P, T> {
    type Adv = arena_iterators::PtrAdvancer<P, T>;
    type E = T;
    type GetMutRes<'a>
        = &'a mut Self::E
    where
        Self: 'a;
    type GetRes<'a>
        = &'a Self::E
    where
        Self: 'a;
    type P = P;

    fn new() -> Self {
        Self::new()
    }

    fn capacity(&self) -> usize {
        self.capacity()
    }

    fn generation(&self) -> P::Gen {
        self.generation()
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

    fn get_mut(&mut self, p: Self::P) -> Option<&mut Self::E> {
        self.get_mut(p)
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
    type GetMutRes<'a>
        = Link<P, &'a mut T>
    where
        Self: 'a;
    type GetRes<'a>
        = &'a Self::E
    where
        Self: 'a;
    type P = P;

    fn new() -> Self {
        Self::new()
    }

    fn capacity(&self) -> usize {
        self.capacity()
    }

    fn generation(&self) -> P::Gen {
        self.generation()
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

    fn get_mut(&mut self, p: Self::P) -> Option<Link<P, &mut T>> {
        self.get_link_mut(p)
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

impl<P: Ptr, T> ArenaTrait for ChainNoGenArena<P, T> {
    type Adv = chain_no_gen_iterators::PtrAdvancer<P, T>;
    type E = LinkNoGen<P, T>;
    type GetMutRes<'a>
        = LinkNoGen<P, &'a mut T>
    where
        Self: 'a;
    type GetRes<'a>
        = &'a Self::E
    where
        Self: 'a;
    type P = P;

    fn new() -> Self {
        Self::new()
    }

    fn capacity(&self) -> usize {
        self.capacity()
    }

    fn generation(&self) -> P::Gen {
        self.generation()
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

    fn get_mut(&mut self, p: Self::P) -> Option<LinkNoGen<P, &mut T>> {
        self.get_link_mut(p)
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
    type GetMutRes<'a>
        = &'a mut Self::E
    where
        Self: 'a;
    type GetRes<'a>
        = &'a Self::E
    where
        Self: 'a;
    type P = P;

    fn new() -> Self {
        Self::new()
    }

    fn capacity(&self) -> usize {
        self.capacity_keys()
    }

    fn generation(&self) -> P::Gen {
        self.generation()
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

    fn get_mut(&mut self, p: Self::P) -> Option<&mut Self::E> {
        self.get_key_mut(p)
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
    type GetMutRes<'a>
        = (&'a K, &'a mut V)
    where
        Self: 'a;
    type GetRes<'a>
        = (&'a K, &'a V)
    where
        Self: 'a;
    type P = P;

    fn new() -> Self {
        Self::new()
    }

    fn capacity(&self) -> usize {
        self.capacity()
    }

    fn generation(&self) -> P::Gen {
        self.generation()
    }

    fn len(&self) -> usize {
        self.len()
    }

    fn is_empty(&self) -> bool {
        self.is_empty()
    }

    /// Uses the hereditary insert
    fn insert(&mut self, e: Self::E) -> P {
        self.insert(e.0, e.1).0
    }

    fn remove(&mut self, p: Self::P) -> Option<Self::E> {
        self.remove(p)
    }

    fn get(&self, p: Self::P) -> Option<(&K, &V)> {
        self.get(p)
    }

    fn get_mut(&mut self, p: Self::P) -> Option<(&K, &mut V)> {
        self.get_mut(p)
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
