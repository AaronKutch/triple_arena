#![allow(clippy::type_complexity)]

use core::{
    borrow::Borrow,
    fmt::{self, Debug},
    num::NonZeroUsize,
    ops::{Index, IndexMut},
};

use crate::{
    Arena, ChainArena, InvalidationOption, LinkNoGen,
    arena::{from_checked_ptr, from_checked_raw},
    ord_iterators::{self, OrderedPtrAdvancer},
    stack::{NonZeroInxArray, NonZeroInxGenericStack},
    traits::{ArenaCloneFromWith, ArenaTrait, ChainArenaTrait, Ptr},
    utils::traits::ArenaBacking,
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
// https://github.com/sebastiencs/shared-arena for a different freelist approach.
// The counterpoint however, is that pure WAVL with chain arena traversal incurs
// 5 whole `P::Inx`s competing for cache line space. We probably want a special
// key arena design that tries to cram as many keys as possible into the same
// 128 byte cache line space, and as may `P::Inx`s as possible are on the value
// arena side. May have some thing configured on the key size to have a
// `NonZeroInxArray<P>` that compresses a variable number of keys together. We
// are keeping the `SimpleOrdArena` however as-is because the key can't be
// separated anyway (at least unless there is an `upcast_key` equivalent like
// what `iddqd` has, I have named `SimpleOrdItem` in case I want an associated
// value which would require a new trait `OrdItem`)
/*
// this couldn't implement `ArenaTrait` (or maybe it could on values?)
pub struct OrdArena<
    P: Ptr,
    K,
    V,
    #[cfg(feature = "alloc")] B: ArenaBacking = crate::HeapBacking,
    #[cfg(not(feature = "alloc"))] B: ArenaBacking,
> {
    pub(crate) a: SimpleOrdArena<P, OrdPair<K, V>, B>,
}
*/

// FIXME have a test that makes sure only bounds that are absolutely required
// are used

/// Internal node for a [SimpleOrdArena]
#[derive(Clone)]
pub struct Node<P: Ptr, T> {
    pub t: T,
    /// Pointer back to parent
    pub p_back: Option<P::Inx>,
    /// Pointer to left subtree
    pub p_tree0: Option<P::Inx>,
    /// Pointer to right subtree
    pub p_tree1: Option<P::Inx>,
    /// The rank of the node. We do not have to worry about overflow because the
    /// worst case is that the root rank is `2*lb(len)`, meaning that even
    /// `i128::MAX` could not overflow this.
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
/// keys, or for a special function like `insert_inx_manual_unwrap` to be used
/// incorrectly. The functions are constructed such that _no_ panics, aborts,
/// memory leaks, or non-termination occurs. However, the well ordered property,
/// `find_key`, and hereditary properties may be broken for any entry in the
/// arena.
///
/// ```
/// use core::cmp::Ordering;
///
/// use triple_arena::{OrdArena, ptr_struct};
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
/// assert_eq!(a.first().unwrap(), p10);
/// assert_eq!(a.last().unwrap(), p70);
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
/// version will introduce an advanced `OrdArena<P, K, V, B>` (since its keys
/// and values can be separated internally, the tradeoff being that its version
/// of `SimpleOrdItem` will not have the same generality), however it should
/// still be faster in many cases if `Ptr`s can be reused multiple times. Try to
/// minimize the points where `find_key` is required.
pub struct SimpleOrdArena<
    P: Ptr,
    T,
    #[cfg(feature = "alloc")] B: ArenaBacking = crate::HeapBacking,
    #[cfg(not(feature = "alloc"))] B: ArenaBacking,
> {
    // these are invalid if `a.is_empty()`
    pub(crate) root: P::Inx,
    pub(crate) first: P::Inx,
    pub(crate) last: P::Inx,
    pub(crate) a: ChainArena<P, Node<P, T>, B>,
}

impl<P: Ptr, T, B: ArenaBacking> SimpleOrdArena<P, T, B> {
    /// Follows [Arena::generation]
    pub fn generation(&self) -> P::Gen {
        self.a.generation()
    }

    /// Follows [Arena::set_generation]
    pub fn set_generation(&mut self, new_gen: P::Gen) {
        self.a.set_generation(new_gen)
    }

    /// Follows [Arena::inc_generation]
    pub fn inc_generation(&mut self) -> InvalidationOption<()> {
        self.a.inc_generation()
    }

    /// Returns the `Ptr` to the minimum key. Runs in `O(1)` time. Returns
    /// `None` if `self.is_empty()`.
    #[must_use]
    pub fn first(&self) -> Option<P> {
        if self.is_empty() {
            None
        } else {
            let generation = self.a.get_inx(self.first).unwrap().0;
            Some(Ptr::_from_raw(self.first, generation))
        }
    }

    /// Returns the `Ptr` to the maximum key. Runs in `O(1)` time. Returns
    /// `None` if `self.is_empty()`.
    #[must_use]
    pub fn last(&self) -> Option<P> {
        if self.is_empty() {
            None
        } else {
            let generation = self.a.get_inx(self.last).unwrap().0;
            Some(Ptr::_from_raw(self.last, generation))
        }
    }

    /// Returns the generation associated with `p` and a `LinkNoGen<P, &T>`.
    /// Using [prev](crate::Link::prev) on the result gives the `Ptr` to the
    /// next lesser key, and using [next](crate::Link::next) gives the `Ptr`
    /// to the next greater key.
    pub fn get_inx_link_no_gen(&self, p: P::Inx) -> Option<(P::Gen, LinkNoGen<P, &T>)> {
        self.a
            .get_inx_link_no_gen(p)
            .map(|(generation, link)| (generation, LinkNoGen::new(link.prev_next(), &link.t.t)))
    }

    // this is safe for the `SimpleOrdArena`

    /// Returns a whole internal node
    pub fn get_inx_node(&self, p: P::Inx) -> Option<(P::Gen, &LinkNoGen<P, Node<P, T>>)> {
        self.a.get_inx_link_no_gen(p)
    }

    /// This advances over all the entries in order with respect to their keys.
    /// Starts from `p` and moves in reverse order if `rev` is set. Returns
    /// `None` if `p` is invalid
    pub fn advancer_ordered(&self, p: P, rev: bool) -> Option<OrderedPtrAdvancer<P>> {
        if !self.contains(p) {
            return None;
        }
        Some(ord_iterators::OrderedPtrAdvancer {
            inx: Some(p.inx()),
            rev,
        })
    }

    /*
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
        if let Some(min) = self.first() {
            self.a
                .compress_and_shrink_acyclic_chain_with(min, |p, node, q| {
                    // handles partially exterior nodes for later
                    node.p_tree0 = None;
                    node.p_tree1 = None;
                    map(p, &node.k, &mut node.v, q)
                });
            self.raw_rebalance_assuming_compressed();
        } else {
            //self.a.clear_and_shrink();
        }
    }
    */

    /// Assumes all `p_back`s, `p_tree0`s, and `p_tree1`s are preset to `None`,
    /// and all `rank`s are set to 0. `root` can be invalid. However, all
    /// other invariants must be kept such as the keys being in order in a
    /// single acyclic chain, and the `first` and `last` `Ptr`s being set if
    /// nonempty.
    pub(crate) fn raw_rebalance_assuming_prepared(&mut self) {
        /*
        If trying to make an `O(n)` pass to rebalance the tree, it seems that it is only possible to do so by starting, at least virtually, from the top down. Every set of entries has to be recursively cut about in half (there is some more extensive bound but if we are doing this, we may as well make it as balanced as possible). If not done so, it is inevitable with enough entries that a subtree is not only unbalanced but cannot even form a valid subtree because the ranks cannot be bridged.

        What we want to do is have an algorithm that can deterministically compute a node's placement in a tree only as a function of index (and we do it by requiring that all the tree `Ptr`s are `None` and then go through in one or two passes to idempotently set the `Ptr`s that require it.). Recalculating the recursive part would lead to `O(n log n)` complexity. However, we can have a stack to record intermediate parts. Even better, knowing what nodes to link to each other naturally falls out of this.
        */

        if self.is_empty() {
            return;
        }
        let root_rank = (self
            .a
            .len()
            .wrapping_sub(1)
            .next_power_of_two()
            .trailing_zeros() as u8)
            .wrapping_add(1);

        // A set of elements, the midpoint of which is the root of the subtree.
        // For finding the midpoint, we choose the formulation of `start + (len / 2)`
        // and make the element at the midpoint belong to subtree 1 (so
        // `i_start..i_midpoint` is one subtree and `i_midpoint..i_end` (`i_end` being
        // exclusive) is the other)
        #[derive(Debug, Clone, Copy)]
        struct Tracker<P: Ptr> {
            // to conserve size on small index cases, we use `P::Inx` and can safely cast if
            // inserts up to the current largest index slot were successful anyways
            i_start: P::Inx,
            subtree_len: P::Inx,
            // Stays `None` until finding that the midpoint is `p_target`
            p_midpoint: Option<P::Inx>,
        }

        impl<P: Ptr> Tracker<P> {
            fn i_start(self) -> NonZeroUsize {
                from_checked_ptr::<P>(self.i_start)
            }

            fn subtree_len(self) -> NonZeroUsize {
                from_checked_ptr::<P>(self.subtree_len)
            }
        }

        // use the nonzero stack to minimize dependencies

        // We can't use consts from generics here, but it only shaves off a few anyways.
        // We use `usize::BITS` and not `usize::BITS - 1` because we need the extra
        // superroot, and we would just use the power of two array size anyways.

        // ~2048 bytes on typical 64 bit platforms and indexes, 128 bytes on very
        // restricted 16 bit platforms, acceptable as long as this is a leaf function
        const MAX_DEPTH: usize = usize::BITS as usize;
        let mut stack = NonZeroInxArray::<Tracker<P>, MAX_DEPTH>::new();
        // Setup the stack virtually. When jumping power of two domains, single depth
        // backtracking has to be done but otherwise one pass is made.

        // the root
        stack.push(Tracker {
            i_start: from_checked_raw::<P>(NonZeroUsize::new(1).unwrap()),
            subtree_len: from_checked_raw::<P>(NonZeroUsize::new(self.a.len()).unwrap()),
            p_midpoint: None,
        });
        // descend to the first element, always ends up as a single element subtree, so
        // we can proceed by induction
        loop {
            let last = stack
                .get_mut(NonZeroUsize::new(stack.len()).unwrap())
                .unwrap();

            let i_midpoint =
                NonZeroUsize::new(1usize.wrapping_add(last.subtree_len().get() / 2)).unwrap();
                // FIXME should be removable
            if i_midpoint == NonZeroUsize::new(1).unwrap() {
                last.p_midpoint = Some(self.first);
            }
            let Some(subtree_len) = NonZeroUsize::new(i_midpoint.get().wrapping_sub(1)) else {
                break;
            };
            stack.push(Tracker {
                i_start: from_checked_raw::<P>(NonZeroUsize::new(1).unwrap()),
                subtree_len: from_checked_raw::<P>(subtree_len),
                p_midpoint: None,
            });
        }

        // maintain that every loop starts at `i_target` being the midpoint of the last
        // tracker on the stack, and that this is the largest set that has `i_target` as
        // the midpoint (if descending wrongly, we can have a repeat of the midpoint
        // which will lead to ranks being assigned wrong)
        let mut p_target = self.first;
        let mut i_target = NonZeroUsize::new(1).unwrap();
        let mut p_next = self.a.get_inx_link_no_gen(p_target).unwrap().1.next();
        loop {
            let i_next = i_target.checked_add(1).unwrap();
            let ascend = {
                let stack_len = stack.len();
                let last = stack
                    .get_mut(NonZeroUsize::new(stack.len()).unwrap())
                    .unwrap();
                last.p_midpoint = Some(p_target);
                let subtree_len = last.subtree_len();
                let i_end = last
                    .i_start()
                    .checked_add(last.subtree_len().get())
                    .unwrap();
                let node = self.a.get_inx_mut_unwrap(p_target);
                match subtree_len.get() {
                    // special base cases
                    1 => {
                        // a leaf node, forced to have this rank
                        node.rank = 1;
                    }
                    2 => {
                        // a node with one child being `None`, forced to have this
                        // rank
                        node.rank = 2;
                    }
                    3 => {
                        // a node with both children having rank 1, we have the
                        // option
                        // of rank 2 or 3, but it
                        // turns out that we need to choose the maximum rank in
                        // general, there is an 18 node minimal case
                        // where an impossibility shows up
                        node.rank = 3;
                    }
                    4 => {
                        // must have a rank 2 and rank 1 child, forced to have this
                        // rank
                        node.rank = 3;
                    }
                    // possible in all other cases if we always chose best midpoint
                    _ => {
                        node.rank = root_rank.wrapping_sub(stack_len as u8).wrapping_add(1);
                    }
                }

                // happens to always be if this
                if subtree_len.get() <= 2 {
                    Some(i_end)
                } else {
                    None
                }
            };

            // to find the correct stack state with the midpoint for `p_next`, if `i_next`
            // is not in our set we ascend until we get it, else we descend until we see it
            // for the first time.

            /*{
                dbg!("before", p_target, ascend);
                for i in 1..=stack.len() {
                    dbg!(stack.get(NonZeroUsize::new(i).unwrap()).unwrap());
                }
            }*/

            if let Some(i_end) = ascend {
                loop {
                    let removed = stack.pop().unwrap();
                    let p_removed = removed.p_midpoint.unwrap();
                    let Some(len) = NonZeroUsize::new(stack.len()) else {
                        self.root = p_removed;
                        return;
                    };
                    let last = stack.get_mut(len).unwrap();
                    // if the endpoint changes them we know we have reached the frame with the
                    // midpoint being the next element, also this coincides with the first time ascending from `p_tree0` after ascending from `p_tree1` zero or more times
                    let ascended1 = last
                        .i_start()
                        .checked_add(last.subtree_len().get())
                        .unwrap()
                        != i_end;
                    if ascended1
                    {
                        if let Some(p_next) = self.a.get_inx_link_no_gen(p_target).unwrap().1.next() {
                            // all `p_tree0`s set here
                            self.a.get_inx_mut_unwrap(p_next).p_tree0 = Some(p_removed);
                            self.a.get_inx_mut_unwrap(p_removed).p_back = Some(p_next);
                        }
                        break;
                    } else {
                        // this must have been set by the time we ascend from the right subtree
                        let p_last = last.p_midpoint.unwrap();
                        // all `p_tree1`s set here
                        self.a.get_inx_mut_unwrap(p_last).p_tree1 = Some(p_removed);
                        self.a.get_inx_mut_unwrap(p_removed).p_back = Some(p_last);
                    }
                }
            } else {
                // descend subtree 1, exclude the midpoint
                {
                    let last = stack
                        .get_mut(NonZeroUsize::new(stack.len()).unwrap())
                        .unwrap();
                    let subtree_len = last.subtree_len();
                    let i_start = last.i_start();
                    let i_midpoint = i_target;
                    let i_end = i_start.checked_add(subtree_len.get()).unwrap();
                    let i_start1 = i_midpoint.checked_add(1).unwrap();
                    if let Some(subtree1_len) =
                        NonZeroUsize::new(i_end.get().wrapping_sub(i_start1.get())) {
                            stack.push(Tracker {
                                i_start: from_checked_raw::<P>(i_start1),
                                subtree_len: from_checked_raw::<P>(subtree1_len),
                                p_midpoint: None,
                            });
                        } else {
                            panic!()
                        }
                }

                // find the midpoint or keep descending subtree 0
                loop {
                    let last = stack
                        .get_mut(NonZeroUsize::new(stack.len()).unwrap())
                        .unwrap();
                    let i_start = last.i_start();
                    let i_midpoint =
                        NonZeroUsize::new(i_start.get().wrapping_add(last.subtree_len().get() / 2))
                            .unwrap();

                    if i_midpoint == i_next {
                        break;
                    }

                    let Some(subtree0_len) =
                        NonZeroUsize::new(i_midpoint.get().wrapping_sub(i_start.get()))
                    else {
                        break;
                    };
                    stack.push(Tracker {
                        i_start: from_checked_raw::<P>(i_start),
                        subtree_len: from_checked_raw::<P>(subtree0_len),
                        p_midpoint: None,
                    });
                }
            }

            p_next = self.a.get_inx_link_no_gen(p_target).unwrap().1.next();
            p_target = p_next.unwrap();
            i_target = i_next;
        }
    }

    // TODO probably have some from_ordered_chain function

    /// Overwrites `chain_arena` (dropping all preexisting `T`, overwriting the
    /// generation counter, and reusing capacity) with the `Ptr` mapping of
    /// `self`, with the ordering preserved in a single chain
    /// ([next](crate::Link::next) points to the next greater entry)
    pub fn clone_to_chain_arena<U, F: FnMut(P, &T) -> U>(
        &self,
        chain_arena: &mut ChainArena<P, U, B>,
        mut map: F,
    ) {
        chain_arena.clone_from_with(&self.a, |p, link| map(p, &link.t.t));
    }

    /// Overwrites `arena` (dropping all preexisting `T`, overwriting the
    /// generation counter, and reusing capacity) with the `Ptr` mapping of
    /// `self`
    pub fn clone_to_arena<U, F: FnMut(P, &T) -> U>(&self, arena: &mut Arena<P, U, B>, mut map: F) {
        arena
            .clone_from_with(&self.a.a, |p, link| map(p, &link.t.t))
            .unwrap();
    }
}

/// Implemented if `T: Clone`.
impl<P: Ptr, T: Clone, B: ArenaBacking> Clone for SimpleOrdArena<P, T, B> {
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

impl<P: Ptr, T, B: ArenaBacking> Default for SimpleOrdArena<P, T, B> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P: Ptr, T, B: ArenaBacking, Q: Borrow<P>> Index<Q> for SimpleOrdArena<P, T, B> {
    type Output = T;

    fn index(&self, inx: Q) -> &T {
        let p: P = *inx.borrow();
        self.get(p)
            .expect("indexed `SimpleOrdArena` with invalidated `Ptr`")
    }
}

impl<P: Ptr, T, B: ArenaBacking, Q: Borrow<P>> IndexMut<Q> for SimpleOrdArena<P, T, B> {
    fn index_mut(&mut self, inx: Q) -> &mut T {
        let p: P = *inx.borrow();
        self.get_mut(p)
            .expect("indexed `SimpleOrdArena` with invalidated `Ptr`")
    }
}

impl<P: Ptr, T: Debug, B: ArenaBacking> Debug for SimpleOrdArena<P, T, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO here and in other triple `Debug`s we need a flat triple
        f.debug_map().entries(self.iter()).finish()
    }
}

// FIXME
/*
impl<P: Ptr, T: PartialEq, B0: ArenaBacking> SimpleOrdArena<P, T, B0> {
    /// Checks if there is the same number of `T` and if all `T` are equal. This is sensitive to
    /// nonhereditary ordering, but does not compare pointers, generations,
    /// arena capacities, internal tree configuration, or `self.generation()`.
    pub fn canonical_eq<Q: Ptr, B1>(&self, other: &SimpleOrdArena<Q, T, B1>) -> bool {
        let mut adv0 = self.advancer();
        let mut adv1 = other.advancer();
        while let Some(p0) = adv0.advance(self) {
            if let Some(p1) = adv1.advance(other) {
                let node0 = self.a.get_inx_unwrap(p0.inx());
                let node1 = other.a.get_inx_unwrap(p1.inx());
                if node0.t != node1.t {
                    return false;
                }
            } else {
                return false;
            }
        }
        adv1.advance(other).is_none()
    }
}

impl<P: Ptr, T: PartialOrd, B: ArenaBacking> SimpleOrdArena<P, T, B> {
    /// Orders as if the arena were a `Vec<T>` in order (note this is ordering over the order of the `T` itself and not the substructure through [SimpleOrdItem::key]), returning early if
    /// the prefix had a difference, checking the key before the value in the
    /// pair, and returning based on which is longer. This is sensitive to
    /// nonhereditary ordering, but does not compare pointers, generations,
    /// arena capacities, internal tree configuration, or `self.generation()`.
    pub fn canonical_partial_cmp(&self, other: &SimpleOrdArena<P, T, B>) -> Option<Ordering> {
        let mut adv0 = self.advancer();
        let mut adv1 = other.advancer();
        while let Some(p0) = adv0.advance(self) {
            if let Some(p1) = adv1.advance(other) {
                let node0 = self.a.get_inx_unwrap(p0.inx());
                let node1 = other.a.get_inx_unwrap(p1.inx());
                match node0.k.partial_cmp(&node1.k) {
                    Some(Ordering::Equal) => (),
                    ord => return ord,
                }
                match node0.v.partial_cmp(&node1.v) {
                    Some(Ordering::Equal) => (),
                    ord => return ord,
                }
            } else {
                return Some(Ordering::Greater);
            }
        }
        if adv1.advance(other).is_none() {
            Some(Ordering::Equal)
        } else {
            Some(Ordering::Less)
        }
    }
}

impl<P: Ptr, K: Ord, V: Ord, B: ArenaBacking> OrdArena<P, K, V, B> {
    /// Orders as if the arena were a `Vec<(K, V)>` in order, returning early if
    /// the prefix had a difference, checking the key before the value in the
    /// pair, and returning based on which is longer. This is sensitive to
    /// nonhereditary ordering, but does not compare pointers, generations,
    /// arena capacities, internal tree configuration, or `self.generation()`.
    pub fn canonical_cmp(&self, other: &OrdArena<P, K, V, B>) -> Ordering {
        let mut adv0 = self.advancer();
        let mut adv1 = other.advancer();
        while let Some(p0) = adv0.advance(self) {
            if let Some(p1) = adv1.advance(other) {
                let node0 = self.a.get_inx_unwrap(p0.inx());
                let node1 = other.a.get_inx_unwrap(p1.inx());
                match node0.k.cmp(&node1.k) {
                    Ordering::Equal => (),
                    ord => return ord,
                }
                match node0.v.cmp(&node1.v) {
                    Ordering::Equal => (),
                    ord => return ord,
                }
            } else {
                return Ordering::Greater;
            }
        }
        if adv1.advance(other).is_none() {
            Ordering::Equal
        } else {
            Ordering::Less
        }
    }
}
*/
