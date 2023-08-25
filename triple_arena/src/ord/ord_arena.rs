#![allow(clippy::type_complexity)]

use core::{
    borrow::Borrow,
    fmt,
    fmt::Debug,
    mem,
    num::NonZeroUsize,
    ops::{Index, IndexMut},
};

use crate::{
    chain::LinkNoGen,
    utils::{ChainNoGenArena, PtrInx},
    Advancer, Arena, ChainArena, Link, Ptr,
};

// This is based on the "Rank-balanced trees" paper by Haeupler, Bernhard;
// Sen, Siddhartha; Tarjan, Robert E. (2015).
//
// Each key-value pair is one-to-one with a tree node pointer and rank group (in
// contrast to some balanced trees which only store keys in the leaves or
// effectively need extra indirection like B-Trees do), which means they can be
// stored as one unit in an entry of an arena (we will call this unit just the
// "node" from now on). We use a ChainArena with all the nodes ordered on a
// single chain, which allows simple pointer following for fast iteration or for
// skipping traversal when finding a neighbor for the displacement step in
// removal. We keep the balancing property by keeping the invariants:
//
// 0. Rank difference calculations count the rank of a `None` child as 0.
// 1. If a node's children are both `None`, its rank can only be 1.
// 2. Rank differences can only be 1 or 2.
//
// We can almost omit rule 1 (and the tree would still be balanced because nodes
// with any `None` child could not have a rank higher than 2), but it leads to
// really bad worst case removal scenarios.

// TODO to fix cache locality, I'm thinking we stay with WAVL because of the
// extra search depth induced by anything B-Tree like. It involves storing the
// values on their own arena that preserves stable `Ptr`s. They have
// backreferences to the keys. We group the keys together in memory, and rewrite
// groups based on different factors. We may need tricks like the bitfields of
// https://github.com/sebastiencs/shared-arena for a different freelist approach

/// Internal node for an `OrdArena`
#[derive(Clone)]
pub struct Node<P: Ptr, K, V> {
    pub k: K,
    pub v: V,
    // Pointer back to parent
    pub p_back: Option<P::Inx>,
    // Pointer to left subtree
    pub p_tree0: Option<P::Inx>,
    // Pointer to right subtree
    pub p_tree1: Option<P::Inx>,
    // we do not have to worry about overflow because the worst case is that the root rank is
    // 2*lb(len), meaning that even i128::MAX could not overflow this.
    pub rank: u8,
}

/// An Ordered Arena with three parameters: a `P: Ptr` type that gives single
/// indirection access to elements, a `K: Ord` key type that is used to define
/// an ordering among elements, and a `V` value type that is not ordered over
/// but is associated with each `K`. `O(log n)` insertions, finds, and deletions
/// are guaranteed.
///
/// This is similar to the standard `BTreeMap`, but is more powerful and
/// performant because of the arena strategy. It internally uses a specialized
/// WAVL tree on a `ChainArena` with one-to-one tree node and key-value pair
/// storage, which enables all the properties of arenas including stable `Ptr`
/// references (meaning that accesses are `O(1)` instead of `O(log n)` as long
/// as the `Ptr` is kept, and no cumbersome `Entry` handling is needed like for
/// `BTreeMap` or for hashmaps). The tree is balanced such that the number of
/// internal lookups needed to find a key is at most about `1.44 *
/// log_2(arena.len())` if only insertions and no removals are used, otherwise
/// the worst case is `2 * log_2(arena.len())`.
///
/// Note that multiple equal keys are allowed through the `insert_nonhereditary`
/// function, and this violates the hereditary property and `find_*` uniqueness
/// only for those keys.
///
/// Note: it is a logic error for a key's ordering to change relative to other
/// keys. The functions are constructed such that _no_ panics, aborts, memory
/// leaks, or non-termination occurs. However, the well ordered property,
/// `find_key`, and hereditary properties may be broken for any entry in the
/// arena.
///
/// Note: the serialization impls from `serde_support` requires that `OrdArena`s
/// are compressed with one of the `compress_and_shrink_*` functions such as
/// [OrdArena::compress_and_shrink_recaster] before use.
///
/// ```
/// use core::cmp::Ordering;
///
/// use triple_arena::{ptr_struct, OrdArena};
///
/// ptr_struct!(P0);
/// let mut a: OrdArena<P0, u64, ()> = OrdArena::new();
///
/// let p50 = a.insert(50, ()).0;
/// let p30 = a.insert(30, ()).0;
/// let p70 = a.insert(70, ()).0;
/// let p60 = a.insert(60, ()).0;
/// let p10 = a.insert(10, ()).0;
///
/// assert_eq!(a.min().unwrap(), p10);
/// assert_eq!(a.max().unwrap(), p70);
///
/// // note that this is `O(1)` because we are using a `Ptr` to directly
/// // index
/// assert_eq!(*a.get_key(p50).unwrap(), 50);
///
/// // the `insert_*`, `find_*`, and `remove` operations are the only
/// // `O(log n)` per-element operations
/// assert_eq!(a.find_key(&50).unwrap(), p50);
///
/// // this could find either `(p50, Ordering::Greater)` or
/// // `(p60, Ordering::Less)`
/// assert_eq!(a.find_similar_key(&53).unwrap(), (p60, Ordering::Less));
///
/// // in `O(1)` time get the previous and next pairs
/// assert_eq!(a.get_link(p60).unwrap().prev_next(), (Some(p50), Some(p70)));
///
/// // `remove` does have to do `O(log n)` tree rebalancing, but it avoids
/// // needing to redo the lookup if the `Ptr` is kept around
/// let link = a.remove(p50).unwrap();
/// assert_eq!(link, (50, ()));
///
/// // The iterators are fully deterministic and iterate from the
/// // least element to the greatest
/// let expected = [(p10, 10), (p30, 30), (p60, 60), (p70, 70)];
/// for (i, (p, key, _)) in a.iter().enumerate() {
///     assert_eq!(expected[i], (p, *key));
/// }
/// ```
///
/// Note: due to a known problem with cache locality, insert and find operations
/// can take twice the time they would on a `BTreeMap`. A future `triple_arena`
/// version will find a way to fix this, however it should still be faster in
/// many cases if `Ptr`s can be reused multiple times. Try to minimize
/// the points where `find_key` is required.
pub struct OrdArena<P: Ptr, K, V> {
    pub(crate) root: P::Inx,
    pub(crate) first: P::Inx,
    pub(crate) last: P::Inx,
    pub(crate) a: ChainNoGenArena<P, Node<P, K, V>>,
}

impl<P: Ptr, K, V> OrdArena<P, K, V> {
    pub fn new() -> Self {
        Self {
            root: P::Inx::new(NonZeroUsize::new(1).unwrap()),
            first: P::Inx::new(NonZeroUsize::new(1).unwrap()),
            last: P::Inx::new(NonZeroUsize::new(1).unwrap()),
            a: ChainNoGenArena::new(),
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        let mut res = Self::new();
        res.reserve(capacity);
        res
    }

    /// Returns the total number of valid `Ptr`s, or equivalently the number of
    /// key-value entries in the arena.
    pub fn len(&self) -> usize {
        self.a.len()
    }

    /// Returns if the arena is empty
    pub fn is_empty(&self) -> bool {
        self.a.is_empty()
    }

    /// Returns the key-value capacity of the arena
    pub fn capacity(&self) -> usize {
        self.a.capacity()
    }

    /// Follows [Arena::gen]
    pub fn gen(&self) -> P::Gen {
        self.a.gen()
    }

    /// Follows [Arena::reserve]
    pub fn reserve(&mut self, additional: usize) {
        self.a.reserve(additional);
    }

    /// Returns the `Ptr` to the minimum key. Runs in `O(1)` time. Returns
    /// `None` if `self.is_empty()`.
    #[must_use]
    pub fn min(&self) -> Option<P> {
        if self.is_empty() {
            None
        } else {
            let gen = self.a.get_no_gen(self.first).unwrap().0;
            Some(Ptr::_from_raw(self.first, gen))
        }
    }

    /// Returns the `Ptr` to the maximum key. Runs in `O(1)` time. Returns
    /// `None` if `self.is_empty()`.
    #[must_use]
    pub fn max(&self) -> Option<P> {
        if self.is_empty() {
            None
        } else {
            let gen = self.a.get_no_gen(self.last).unwrap().0;
            Some(Ptr::_from_raw(self.last, gen))
        }
    }

    /// Returns if `p` is a valid `Ptr`
    pub fn contains(&self, p: P) -> bool {
        self.a.contains(p)
    }

    /// Returns a reference to the key-value pair pointed to by `p`
    #[must_use]
    pub fn get(&self, p: P) -> Option<(&K, &V)> {
        self.a.get(p).map(|node| (&node.k, &node.v))
    }

    /// Returns a reference to the key pointed to by `p`
    #[must_use]
    pub fn get_key(&self, p: P) -> Option<&K> {
        self.a.get(p).map(|node: &Node<P, K, V>| &node.k)
    }

    /// Returns a reference to the value pointed to by `p`
    #[must_use]
    pub fn get_val(&self, p: P) -> Option<&V> {
        self.a.get(p).map(|node| &node.v)
    }

    /// Returns a mutable reference to the value pointed to by `p`
    #[must_use]
    pub fn get_val_mut(&mut self, p: P) -> Option<&mut V> {
        self.a.get_mut(p).map(|t| &mut t.v)
    }

    /// Returns a mutable reference to the key-value pair pointed to by `p`
    #[must_use]
    pub fn get_mut(&mut self, p: P) -> Option<(&K, &mut V)> {
        self.a.get_mut(p).map(|t| (&t.k, &mut t.v))
    }

    /// Returns the full `Link<P, (&K, &V)>`. Using [prev](crate::Link::prev) on
    /// the result gives the `Ptr` to the next lesser key, and using
    /// [next](crate::Link::next) gives the `Ptr` to the next greater key.
    #[must_use]
    pub fn get_link(&self, p: P) -> Option<Link<P, (&K, &V)>> {
        self.a.get_link(p).map(|link| {
            let prev = if let Some(prev) = link.prev() {
                let (gen, _) = self.a.get_no_gen(prev).unwrap();
                Some(Ptr::_from_raw(prev, gen))
            } else {
                None
            };
            let next = if let Some(next) = link.next() {
                let (gen, _) = self.a.get_no_gen(next).unwrap();
                Some(Ptr::_from_raw(next, gen))
            } else {
                None
            };
            Link::new((prev, next), (&link.t.k, &link.t.v))
        })
    }

    /// Returns the generation associated with `p` and a `LinkNoGen<P, &K>`, the
    /// interlinks of which point to neighboring pairs.
    pub fn get_link_no_gen(&self, p: P::Inx) -> Option<(P::Gen, LinkNoGen<P, (&K, &V)>)> {
        self.a.get_no_gen(p).map(|(gen, link)| {
            (
                gen,
                LinkNoGen::new(link.prev_next(), (&link.t.k, &link.t.v)),
            )
        })
    }

    /// Gets two references pointed to by `p0` and `p1`.
    /// If `p0 == p1` or a pointer is invalid, `None` is returned.
    #[allow(clippy::type_complexity)]
    #[must_use]
    pub fn get2_val_mut(&mut self, p0: P, p1: P) -> Option<(&mut V, &mut V)> {
        self.a
            .get2_mut(p0, p1)
            .map(|(t0, t1)| (&mut t0.v, &mut t1.v))
    }

    /// Invalidates all references to the entry pointed to by `p`, and returns a
    /// new valid reference. Does no invalidation and returns `None` if `p` is
    /// invalid.
    #[must_use]
    pub fn invalidate(&mut self, p: P) -> Option<P> {
        // the tree pointers do not have generation counters
        self.a.invalidate(p)
    }

    /// Replaces the `V` pointed to by `p` with `new`, returns the
    /// old `V`, and keeps the internal generation counter as-is so that
    /// previously constructed `Ptr`s are still valid.
    ///
    /// # Errors
    ///
    /// Returns ownership of `new` instead if `p` is invalid
    pub fn replace_val_and_keep_gen(&mut self, p: P, new: V) -> Result<V, V> {
        if let Some(t) = self.a.get_mut(p) {
            let old = mem::replace(&mut t.v, new);
            Ok(old)
        } else {
            Err(new)
        }
    }

    /// Replaces the `V` pointed to by `p` with `new`, returns a tuple of the
    /// old `V` and new `Ptr`, and updates the internal generation counter so
    /// that previous `Ptr`s to this are invalidated.
    ///
    /// # Errors
    ///
    /// Does no invalidation and returns ownership of `new` if `p` is invalid
    pub fn replace_val_and_update_gen(&mut self, p: P, new: V) -> Result<(V, P), V> {
        // the tree pointers do not have generation counters
        if let Some(p_new) = self.a.invalidate(p) {
            let old = mem::replace(&mut self.a.get_inx_mut_unwrap_t(p_new.inx()).v, new);
            Ok((old, p_new))
        } else {
            Err(new)
        }
    }

    /// Swaps the `V` values pointed to by `Ptr`s `p0` and `p1` and keeps the
    /// generation counters as-is. If `p0 == p1`, then nothing occurs. Returns
    /// `None` if `p0` or `p1` are invalid.
    #[must_use]
    pub fn swap_vals(&mut self, p0: P, p1: P) -> Option<()> {
        if p0 == p1 {
            // still need to check for containment
            if self.contains(p0) {
                Some(())
            } else {
                None
            }
        } else {
            let (lhs, rhs) = self.a.get2_mut(p0, p1)?;
            // be careful to swap only the inner `V` values
            mem::swap(&mut lhs.v, &mut rhs.v);
            Some(())
        }
    }

    /// Drops all keys and values from the arena and invalidates all pointers
    /// previously created from it. This has no effect on the allocated
    /// capacity.
    pub fn clear(&mut self) {
        self.a.clear();
    }

    /// Performs an [OrdArena::clear] and resets capacity to 0
    pub fn clear_and_shrink(&mut self) {
        self.a.clear_and_shrink();
    }

    /// Compresses the arena by moving around entries to be able to shrink the
    /// capacity down to the length. All key-value relations remain, but all
    /// `Ptr`s are invalidated. New `Ptr`s to the entries can be found again
    /// by iterators and advancers. Additionally, cache locality is improved
    /// by neighboring keys being moved close together in memory, and search
    /// speed is improved by the tree being balanced close to the ideal
    /// balancing.
    pub fn compress_and_shrink(&mut self) {
        self.compress_and_shrink_with(|_, _, _, _| ())
    }

    /// The same as [OrdArena::compress_and_shrink] except that `map` is run
    /// on every `(P, &K, &mut V, P)` with the first `P` being the old `Ptr` and
    /// the last `P` being the new `Ptr`.
    pub fn compress_and_shrink_with<F: FnMut(P, &K, &mut V, P)>(&mut self, mut map: F) {
        if let Some(min) = self.min() {
            self.a
                .compress_and_shrink_acyclic_chain_with(min, |p, node, q| {
                    // handles partially exterior nodes for later
                    node.p_tree0 = None;
                    node.p_tree1 = None;
                    map(p, &node.k, &mut node.v, q)
                });
            self.raw_rebalance_assuming_compressed();
        } else {
            self.a.clear_and_shrink();
        }
    }

    // TODO probably have some from_ordered function

    /// Assumes `!self.is_empty()`, and the keys are in order, raw entries are
    /// compressed, and all `p_tree0`s and `p_tree1`s are preset to `None`.
    pub(crate) fn raw_rebalance_assuming_compressed(&mut self) {
        // redo the tree structure for better balance
        let p_first = P::Inx::new(NonZeroUsize::new(1).unwrap());
        self.first = p_first;
        self.last = P::Inx::new(NonZeroUsize::new(self.a.len()).unwrap());
        let root_rank = (self
            .a
            .len()
            .wrapping_sub(1)
            .next_power_of_two()
            .trailing_zeros() as u8)
            .wrapping_add(1);
        let mut i = NonZeroUsize::new(self.a.len()).unwrap();
        loop {
            let mut lvl = root_rank;
            let p = P::Inx::new(i);
            let mut subtree_first = 1;
            let mut subtree_last = self.a.len();
            let mut last_subtree_mid = None;
            // TODO use a stack of 12
            loop {
                let subtree_len = subtree_last.wrapping_sub(subtree_first).wrapping_add(1);
                let subtree_mid = subtree_first.wrapping_add(subtree_len.wrapping_shr(1));
                if i.get() == subtree_mid {
                    // important: actual accesses are only done at this time
                    let node = self.a.get_inx_mut_unwrap_t(p);
                    if subtree_len == 1 {
                        node.rank = 1;
                    } else if subtree_len == 2 {
                        node.rank = 2;
                    } else if subtree_len == 3 || subtree_len == 4 {
                        node.rank = 3;
                    } else {
                        node.rank = lvl;
                    }
                    if let Some(last_subtree_mid) = last_subtree_mid {
                        let p_back = P::Inx::new(NonZeroUsize::new(last_subtree_mid).unwrap());
                        node.p_back = Some(p_back);
                        let node = self.a.get_inx_mut_unwrap_t(p_back);
                        if i < P::Inx::get(p_back) {
                            node.p_tree0 = Some(p);
                        } else {
                            node.p_tree1 = Some(p);
                        }
                    } else {
                        node.p_back = None;
                        self.root = p;
                    }
                    break
                } else if i.get() < subtree_mid {
                    subtree_last = subtree_mid.wrapping_sub(1);
                } else {
                    subtree_first = subtree_mid.wrapping_add(1);
                }
                lvl = lvl.wrapping_sub(1);
                last_subtree_mid = Some(subtree_mid);
            }
            i = if let Some(prev) = NonZeroUsize::new(i.get().wrapping_sub(1)) {
                prev
            } else {
                break
            }
        }
    }

    /// Overwrites `chain_arena` (dropping all preexisting `T`, overwriting the
    /// generation counter, and reusing capacity) with the `Ptr` mapping of
    /// `self`, with the ordering preserved in a single chain
    /// ([next](crate::Link::next) points to the next greater entry)
    pub fn clone_to_chain_arena<U, F: FnMut(P, &K, &V) -> U>(
        &self,
        chain_arena: &mut ChainArena<P, U>,
        mut map: F,
    ) {
        self.a
            .clone_to_chain_arena(chain_arena, |p, node| map(p, &node.k, &node.v))
    }

    /// Overwrites `arena` (dropping all preexisting `T`, overwriting the
    /// generation counter, and reusing capacity) with the `Ptr` mapping of
    /// `self`
    pub fn clone_to_arena<U, F: FnMut(P, &K, &V) -> U>(&self, arena: &mut Arena<P, U>, mut map: F) {
        arena.clone_from_with(&self.a.a, |p, link| map(p, &link.t.k, &link.t.v));
    }
}

impl<P: Ptr, K: Clone, V0> OrdArena<P, K, V0> {
    /// Has the same properties of [Arena::clone_from_with]. Clones the keys.
    pub fn clone_from_with<V1, F: FnMut(P, &V1) -> V0>(
        &mut self,
        source: &OrdArena<P, K, V1>,
        mut map: F,
    ) {
        self.a.clone_from_with(&source.a, |p, link| Node {
            k: link.t.k.clone(),
            v: map(p, &link.t.v),
            p_back: link.t.p_back,
            p_tree0: link.t.p_tree0,
            p_tree1: link.t.p_tree1,
            rank: link.t.rank,
        })
    }
}

/// Implemented if `K: Clone` and `V: Clone`.
impl<P: Ptr, K: Clone, V: Clone> Clone for OrdArena<P, K, V> {
    /// Has the `Ptr` preserving properties of [Arena::clone]
    fn clone(&self) -> Self {
        Self {
            root: self.root,
            first: self.first,
            last: self.last,
            a: self.a.clone(),
        }
    }

    /// Has the `Ptr` and capacity preserving properties of [Arena::clone_from]
    fn clone_from(&mut self, source: &Self) {
        self.root = source.root;
        self.first = source.first;
        self.last = source.last;
        self.a.clone_from(&source.a)
    }
}

impl<P: Ptr, K, V> Default for OrdArena<P, K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P: Ptr, K, V, B: Borrow<P>> Index<B> for OrdArena<P, K, V> {
    type Output = V;

    fn index(&self, inx: B) -> &V {
        let p: P = *inx.borrow();
        self.get_val(p)
            .expect("indexed `OrdArena` with invalidated `Ptr`")
    }
}

impl<P: Ptr, K, V, B: Borrow<P>> IndexMut<B> for OrdArena<P, K, V> {
    fn index_mut(&mut self, inx: B) -> &mut V {
        let p: P = *inx.borrow();
        self.get_val_mut(p)
            .expect("indexed `OrdArena` with invalidated `Ptr`")
    }
}

impl<P: Ptr, K: Debug, V: Debug> Debug for OrdArena<P, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO here and in other triple `Debug`s we need a flat triple
        f.debug_map()
            .entries(self.iter().map(|triple| (triple.0, (triple.1, triple.2))))
            .finish()
    }
}

impl<P: Ptr, K: PartialEq, V: PartialEq> PartialEq<OrdArena<P, K, V>> for OrdArena<P, K, V> {
    /// Checks if all `(K, V)` pairs are equal. This is sensitive to
    /// nonhereditary ordering, but does not compare pointers, generations,
    /// arena capacities, internal tree configuration, or `self.gen()`.
    fn eq(&self, other: &OrdArena<P, K, V>) -> bool {
        // first the keys
        let mut adv0 = self.advancer();
        let mut adv1 = other.advancer();
        while let Some(p0) = adv0.advance(self) {
            if let Some(p1) = adv1.advance(other) {
                let node0 = self.a.get_inx_unwrap(p0.inx());
                let node1 = self.a.get_inx_unwrap(p1.inx());
                if node0.t.k != node1.t.k {
                    return false
                }
                if node0.t.v != node1.t.v {
                    return false
                }
            } else {
                return false
            }
        }
        adv1.advance(other).is_none()
    }
}

impl<P: Ptr, K: Eq, V: Eq> Eq for OrdArena<P, K, V> {}

// TODO PartialOrd
