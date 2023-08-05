#![allow(clippy::type_complexity)]

use core::{
    borrow::Borrow,
    fmt,
    fmt::Debug,
    mem,
    num::NonZeroUsize,
    ops::{Index, IndexMut},
};

use crate::{utils::PtrInx, Arena, ChainArena, Link, Ptr};

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

/// Internal node for an `OrdArena`
#[derive(Clone)]
pub struct Node<P: Ptr, K, V> {
    pub k_v: (K, V),
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
/// ```
/// use core::cmp::Ordering;
///
/// use triple_arena::{ptr_struct, OrdArena};
///
/// ptr_struct!(P0);
/// let mut a: OrdArena<P0, u64, ()> = OrdArena::new();
///
/// // we purposely group the key-value pairs in tuples for technical
/// // performance reasons, and often they are returned as tuples
/// let p50 = a.insert((50, ())).0;
/// let p30 = a.insert((30, ())).0;
/// let p70 = a.insert((70, ())).0;
/// let p60 = a.insert((60, ())).0;
/// let p10 = a.insert((10, ())).0;
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
/// // `remove` does have to do `O(log n)` tree rebalancing, but it avoids
/// // needing to redo the lookup if the `Ptr` is kept around
/// let link = a.remove(p50).unwrap();
/// assert_eq!(link.t, (50, ()));
/// assert_eq!(link.prev_next(), (Some(p30), Some(p60)));
///
/// // The iterators are fully deterministic and iterate from the
/// // least element to the greatest
/// let expected = [(p10, 10), (p30, 30), (p60, 60), (p70, 70)];
/// for (i, (p, (key, _))) in a.iter().enumerate() {
///     assert_eq!(expected[i], (p, *key));
/// }
/// ```
pub struct OrdArena<P: Ptr, K, V> {
    pub(in crate::ord_arena) root: P::Inx,
    pub(in crate::ord_arena) first: P::Inx,
    pub(in crate::ord_arena) last: P::Inx,
    pub(in crate::ord_arena) a: ChainArena<P, Node<P, K, V>>,
}

impl<P: Ptr, K, V> OrdArena<P, K, V> {
    pub fn new() -> Self {
        Self {
            root: P::Inx::new(NonZeroUsize::new(1).unwrap()),
            first: P::Inx::new(NonZeroUsize::new(1).unwrap()),
            last: P::Inx::new(NonZeroUsize::new(1).unwrap()),
            a: ChainArena::new(),
        }
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
            let gen = self.a.get_ignore_gen(self.first).unwrap().0;
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
            let gen = self.a.get_ignore_gen(self.last).unwrap().0;
            Some(Ptr::_from_raw(self.last, gen))
        }
    }

    /// Returns if `p` is a valid `Ptr`
    pub fn contains(&self, p: P) -> bool {
        self.a.contains(p)
    }

    /// Returns the full `Link<P, (&K, &V)>`. Using [prev](crate::Link::prev) on
    /// the result gives the `Ptr` to the next lesser key, and using
    /// [next](crate::Link::next) gives the `Ptr` to the next greater key.
    #[must_use]
    pub fn get_link(&self, p: P) -> Option<Link<P, &(K, V)>> {
        self.a
            .get_link(p)
            .map(|link| Link::new(link.prev_next(), &link.t.k_v))
    }

    /// Returns a reference to the key-value pair pointed to by `p`
    #[must_use]
    pub fn get(&self, p: P) -> Option<&(K, V)> {
        self.a.get(p).map(|node| &node.k_v)
    }

    /// Returns a reference to the key pointed to by `p`
    #[must_use]
    pub fn get_key(&self, p: P) -> Option<&K> {
        self.a.get(p).map(|node: &Node<P, K, V>| &node.k_v.0)
    }

    /// Returns a reference to the value pointed to by `p`
    #[must_use]
    pub fn get_val(&self, p: P) -> Option<&V> {
        self.a.get(p).map(|node| &node.k_v.1)
    }

    /// Returns the full `Link<P, (&K, &mut V)>`. Using
    /// [prev](crate::Link::prev) on the result gives the `Ptr` to the next
    /// lesser key, and using [next](crate::Link::next) gives the `Ptr` to
    /// the next greater key.
    #[must_use]
    pub fn get_link_mut(&mut self, p: P) -> Option<Link<P, (&K, &mut V)>> {
        self.a
            .get_link_mut(p)
            .map(|link| Link::new(link.prev_next(), (&link.t.k_v.0, &mut link.t.k_v.1)))
    }

    /// Returns a mutable reference to the key-value pair pointed to by `p`
    #[must_use]
    pub fn get_mut(&mut self, p: P) -> Option<(&K, &mut V)> {
        self.a.get_mut(p).map(|t| (&t.k_v.0, &mut t.k_v.1))
    }

    /// Returns a mutable reference to the value pointed to by `p`
    #[must_use]
    pub fn get_val_mut(&mut self, p: P) -> Option<&mut V> {
        self.a.get_mut(p).map(|t| &mut t.k_v.1)
    }

    /// Gets two references pointed to by `p0` and `p1`.
    /// If `p0 == p1` or a pointer is invalid, `None` is returned.
    #[allow(clippy::type_complexity)]
    #[must_use]
    pub fn get2_link_mut(
        &mut self,
        p0: P,
        p1: P,
    ) -> Option<(Link<P, (&K, &mut V)>, Link<P, (&K, &mut V)>)> {
        self.a.get2_link_mut(p0, p1).map(|(link0, link1)| {
            (
                Link::new(link0.prev_next(), (&link0.t.k_v.0, &mut link0.t.k_v.1)),
                Link::new(link1.prev_next(), (&link1.t.k_v.0, &mut link1.t.k_v.1)),
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
            .map(|(t0, t1)| (&mut t0.k_v.1, &mut t1.k_v.1))
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
            let old = mem::replace(&mut t.k_v.1, new);
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
            let old = mem::replace(&mut self.a.get_mut(p_new).unwrap().k_v.1, new);
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
            mem::swap(&mut lhs.k_v.1, &mut rhs.k_v.1);
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

    /// Overwrites `chain_arena` (dropping all preexisting `T`, overwriting the
    /// generation counter, and reusing capacity) with the `Ptr` mapping of
    /// `self`, with the ordering preserved in a single chain
    /// ([next](crate::Link::next) points to the next greater entry)
    pub fn clone_to_chain_arena<U, F: FnMut(P, Link<P, &(K, V)>) -> U>(
        &self,
        chain_arena: &mut ChainArena<P, U>,
        mut map: F,
    ) {
        chain_arena.clone_from_with(&self.a, |p, link| {
            map(p, Link::new(link.prev_next(), &link.t.k_v))
        })
    }

    /// Overwrites `arena` (dropping all preexisting `T`, overwriting the
    /// generation counter, and reusing capacity) with the `Ptr` mapping of
    /// `self`
    pub fn clone_to_arena<U, F: FnMut(P, Link<P, &(K, V)>) -> U>(
        &self,
        arena: &mut Arena<P, U>,
        mut map: F,
    ) {
        arena.clone_from_with(&self.a.a, |p, link| {
            map(p, Link::new(link.prev_next(), &link.t.k_v))
        });
    }
}

impl<P: Ptr, K: Clone, V0> OrdArena<P, K, V0> {
    /// Has the same properties of [Arena::clone_from_with]. Clones the keys.
    pub fn clone_from_with<V1, F: FnMut(P, Link<P, &V1>) -> V0>(
        &mut self,
        source: &OrdArena<P, K, V1>,
        mut map: F,
    ) {
        self.a.clone_from_with(&source.a, |p, link| Node {
            k_v: (
                link.t.k_v.0.clone(),
                map(p, Link::new(link.prev_next(), &link.t.k_v.1)),
            ),
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
        f.debug_map().entries(self.iter()).finish()
    }
}
