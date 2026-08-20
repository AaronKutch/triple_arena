use core::{
    borrow::Borrow,
    cmp::Ordering,
    fmt::{self, Debug},
    mem::ManuallyDrop,
    num::NonZeroUsize,
    ops::{Index, IndexMut},
};

use crate::{
    ChainArena, InvalidationOption, LinkNoGen,
    arena::{ArenaSlot, from_checked_ptr, from_checked_raw},
    errors::{MaxCapacityReductionError, ReallocationError},
    stack::{NonZeroInxArray, NonZeroInxGenericStack},
    traits::{ArenaCloneFromWith, ArenaDirectInsertTrait, ArenaTrait, ChainArenaTrait, Ptr},
    utils::traits::{ArenaBacking, SetMaxCapacity},
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

/// Internal node for a [SimpleOrdArena]
#[derive(Clone)]
pub struct SimpleOrdArenaNode<P: Ptr, T> {
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

/// An Ordered Arena with two main parameters: a `P: Ptr` type that gives single
/// indirection access to elements, and a `T: SimpleOrdItem` type that functions
/// as a unified key and value type, with
/// [crate::utils::traits::SimpleOrdItem::key] used to define an ordering among
/// elements. `O(log n)` insertions, finds, and deletions are guaranteed.
///
/// In common use, you should use `SimpleOrdArena<P, OrdPair<K, V>, B>`, where
/// `K: Ord` is the key used to define the ordering, and `V` is a value type
/// that is not ordered over but is associated with each `K`. `OrdPair` makes it
/// more difficult in practice to accidentally change a key in an arena, and in
/// the future if Rust adds an `Overwrite` trait we will make it `!Overwrite`.
/// `OrdPair<K, ()>` should be used in common cases where there is just a key.
/// In other cases, you should implement `SimpleOrdItem` yourself for a type.
///
/// This is similar to the standard `BTreeMap`, but is more powerful and
/// performant because of the arena strategy. It internally uses a specialized
/// WAVL tree on a `ChainArena` with one-to-one tree node and key-value pair
/// storage, which enables all the properties of arenas including stable `Ptr`
/// references (meaning that accesses are `O(1)` instead of `O(log n)` as long
/// as the `Ptr` is kept, with much more general `Ptr` advancing and entry
/// insertion possibilities). The tree is balanced such that the number of
/// internal lookups needed to find a key is at most about `1.44 *
/// log_2(arena.len())` if only insertions and no removals are used, otherwise
/// the worst case is `2 * log_2(arena.len())`.
///
/// Note that multiple equal keys are allowed through the
/// [Nonhereditary](crate::OrdInsertKind::Nonhereditary) insertion kinds, and
/// this violates the hereditary property and `find_*` uniqueness only for those
/// keys.
///
/// Note: it is a logic error for a key's ordering to change relative to other
/// keys (by using internal mutability or directly modifying the relevant part
/// of the `T: SimpleOrdItem` while it is still in the arena), or for a special
/// function like `insert_inx_manual_unwrap` or [crate::OrdInsertKind::Manual]
/// to be used incorrectly. Unlike some other implementations, the functions on
/// `SimpleOrdArena`s are constructed such that _no_ panics (unless explicitly
/// documented), aborts, memory leaks, or non-termination occurs, regardless of
/// how inconsistent key orderings are. However, the well ordered property,
/// `find_key` functions, and hereditary properties may be broken for any entry
/// in the arena.
///
/// ```
/// use core::cmp::Ordering;
///
/// use triple_arena::{HeapBacking, OrdPair, SimpleOrdArena, ptr_struct, traits::*};
///
/// ptr_struct!(P0);
/// let mut a = SimpleOrdArena::<P0, OrdPair<u64, ()>, HeapBacking>::new();
///
/// let p50 = a.insert(OrdPair::new(50, ())).0;
/// let p30 = a.insert(OrdPair::new(30, ())).0;
/// let p70 = a.insert(OrdPair::new(70, ())).0;
/// let p60 = a.insert(OrdPair::new(60, ())).0;
/// let p10 = a.insert(OrdPair::new(10, ())).0;
///
/// assert_eq!(a.first().unwrap(), p10);
/// assert_eq!(a.last().unwrap(), p70);
///
/// // note that this is `O(1)` because we are using a `Ptr` to directly
/// // index
/// assert_eq!(*a.get(p50).unwrap().k(), 50);
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
/// assert_eq!(
///     a.get_inx_link_no_gen(p60.inx()).unwrap().1.prev_next(),
///     (Some(p50.inx()), Some(p70.inx()))
/// );
///
/// // `remove` does have to do `O(log n)` tree rebalancing, but it avoids
/// // needing to redo the lookup if the `Ptr` is kept around
/// let pair = a.remove(p50).allow().unwrap();
/// assert_eq!(pair.into_k_v(), (50, ()));
///
/// // The `*_ordered` iterators are fully deterministic and iterate from the
/// // least element to the greatest
/// let expected = [(p10, 10), (p30, 30), (p60, 60), (p70, 70)];
/// for (i, (p, pair)) in a.iter_ordered().enumerate() {
///     assert_eq!(expected[i], (p, *pair.k()));
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
    pub(crate) a: ChainArena<P, SimpleOrdArenaNode<P, T>, B>,
}

// Note that we are careful to only require `T: SimpleOrdItem` when necessary

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
    /// Using [LinkNoGen::prev](crate::LinkNoGen::prev) on the result gives the
    /// `Ptr` to the next lesser key, and using
    /// [LinkNoGen::next](crate::LinkNoGen::next) gives the `Ptr`
    /// to the next greater key.
    pub fn get_inx_link_no_gen(&self, p: P::Inx) -> Option<(P::Gen, LinkNoGen<P, &T>)> {
        self.a
            .get_inx_link_no_gen(p)
            .map(|(generation, link)| (generation, LinkNoGen::new(link.prev_next(), &link.t.t)))
    }

    // this is safe for the `SimpleOrdArena`

    /// Returns a whole internal node, for advanced use only
    pub fn get_inx_node(
        &self,
        p: P::Inx,
    ) -> Option<(P::Gen, &LinkNoGen<P, SimpleOrdArenaNode<P, T>>)> {
        self.a.get_inx_link_no_gen(p)
    }

    /// Assumes all `p_back`s, `p_tree0`s, and `p_tree1`s are preset to `None`.
    /// `root`, `first`, `last`, and the `rank`s can be anything and are all
    /// set by this. The chain-level entries must be in a single acyclic chain
    /// of the intended order, but the base arena-level entries can be in any
    /// order in the backing.
    ///
    /// REF(ord_rebalance_guard) As long as the preconditions on this function
    /// holds, this cannot panic
    pub(crate) fn raw_rebalance_assuming_prepared(&mut self) {
        /*
        If trying to make an `O(n)` pass to rebalance the tree, it seems that it is only possible to do so by starting, at least virtually, from the top down. Every set of entries has to be recursively cut about in half (there is some more extensive bound but if we are doing this, we may as well make it as even as possible). If not done so, it is inevitable with enough entries that a subtree is not only unbalanced but cannot even form a valid subtree because the ranks cannot be bridged.

        What we want to do is have an algorithm that can deterministically compute a node's placement in a tree only as a function of index (and we do it by requiring that all the tree `Ptr`s are `None` and then go through in one or two passes to idempotently set the `Ptr`s that require it.). Recalculating the recursive part would lead to `O(n log n)` complexity. However, we can have a stack to record intermediate parts. Even better, knowing what nodes to link to each other naturally falls out of this.
        */

        if self.is_empty() {
            return;
        }
        // find `first`
        let mut first = self.a.find_first_inx_ptr().unwrap().inx();
        while let Some(prev) = self.a.get_inx_link_no_gen(first).unwrap().1.prev() {
            first = prev;
        }
        self.first = first;
        #[allow(clippy::cast_possible_truncation)]
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
        // `i_start..i_midpoint` is one subtree and `(i_midpoint + 1)..i_end` (`i_end`
        // being exclusive), if it exists, is the other). Also note that an element will
        // only appear as a midpoint once due to this construction.
        #[derive(Debug, Clone, Copy)]
        struct Tracker<P: Ptr> {
            // to conserve size on small index cases, we use `P::Inx` and can safely cast if
            // inserts up to the current largest index slot were successful anyways
            i_start: P::Inx,
            subtree_len: P::Inx,
            // This is needed to avoid a second pass when setting the `p_tree1` side
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
        // Setup the stack virtually. When jumping power of two domains, virtual
        // backtracking has to be done but it is `O(2*n)` virtually, and only one pass
        // is made on the real nodes and cache line accesses.

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
        // the midpoint
        let mut p_target = self.first;
        let mut i_target = NonZeroUsize::new(1).unwrap();
        loop {
            let p_next = self.a.get_inx_link_no_gen(p_target).unwrap().1.next();
            if p_next.is_none() {
                // the end of the chain, note that the `return` below has to happen on
                // this same iteration or else `p_next` will be unwrapped
                self.last = p_target;
            }
            let i_next = i_target.checked_add(1).unwrap();

            let stack_len = stack.len();
            let last = stack
                .get_mut(NonZeroUsize::new(stack.len()).unwrap())
                .unwrap();
            last.p_midpoint = Some(p_target);
            let subtree_len = last.subtree_len();
            let i_midpoint = i_target;
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
                #[allow(clippy::cast_possible_truncation)]
                _ => {
                    node.rank = root_rank.wrapping_sub(stack_len as u8).wrapping_add(1);
                }
            }

            // to find the correct stack state with the midpoint for `p_next`, if `i_next`
            // is not in our set we ascend until we get it, else we descend until we see it
            // for the first time.

            // happens to always be if this
            if subtree_len.get() <= 2 {
                loop {
                    let removed = stack.pop().unwrap();
                    let p_removed = removed.p_midpoint.unwrap();
                    let Some(len) = NonZeroUsize::new(stack.len()) else {
                        self.root = p_removed;
                        return;
                    };
                    let last = stack.get_mut(len).unwrap();
                    // if the endpoint changes them we know we have reached the frame with the
                    // midpoint being the next element, also this coincides with the first time
                    // ascending from `p_tree0` after ascending from `p_tree1` zero or more times
                    let ascended1 = last
                        .i_start()
                        .checked_add(last.subtree_len().get())
                        .unwrap()
                        != i_end;
                    if ascended1 {
                        if let Some(p_next) = p_next {
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
                    let i_start1 = i_midpoint.checked_add(1).unwrap();
                    if let Some(subtree1_len) =
                        NonZeroUsize::new(i_end.get().wrapping_sub(i_start1.get()))
                    {
                        stack.push(Tracker {
                            i_start: from_checked_raw::<P>(i_start1),
                            subtree_len: from_checked_raw::<P>(subtree1_len),
                            p_midpoint: None,
                        });
                    } else {
                        // `subtree_len >= 3` here, so this is
                        // `ceil(subtree_len / 2) - 1 >= 1`
                        unreachable!()
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

            p_target = p_next.unwrap();
            i_target = i_next;
        }
    }

    /// This is a more advanced version of [ArenaTrait::compress] that reorders
    /// the entries to be one after another internally and rebalances the tree
    /// deterministically, completely canonicalizing at every level (at least
    /// with respect to the prexisting ordering, this preserves the
    /// [LinkNoGen::prev_next] relations as they existed before this function
    /// was called). Improves cache locality, at least with respect to
    /// advancing over the entries in order.
    ///
    /// Because an element can be internally swapped multiple times to achieve
    /// this in-place in the allocation, this cannot have a map. Use
    /// [transfer_canonical_reallocating](
    /// SimpleOrdArena::transfer_canonical_reallocating) if a recaster is
    /// needed.
    pub fn compress_canonical(&mut self, reset_generation: bool) -> InvalidationOption<()> {
        // TODO single chain optimized internal version of this
        let res = self.a.compress_canonical(reset_generation);
        // chain arena canonicalization puts the arena and chain arena level entries
        // exactly where we want them, now we just need to rebuild the ord arena level.
        for node in self.a.vals_mut() {
            node.p_back = None;
            node.p_tree0 = None;
            node.p_tree1 = None;
        }
        self.raw_rebalance_assuming_prepared();
        res
    }

    // TODO use a `OrdArenaTrait` for `source`

    /// The ordered arena counterpart of
    /// [ChainArena::transfer_canonical_reallocating], transferring every entry
    /// out of `source` and into `self`. Follows all of the same properties,
    /// with the additional guarantee that the resulting `P::Inx`s are
    /// `1..=source.len()` in key order, and that the tree is deterministically
    /// rebalanced to be perfectly canonical as in
    /// [compress_canonical](SimpleOrdArena::compress_canonical).
    ///
    /// Corresponding recaster example:
    /// ```
    /// use triple_arena::{
    ///     DirectArena, HeapBacking, OrdPair, SimpleOrdArena, ptr_struct,
    ///     traits::*,
    ///     utils::traits::{PtrGen, PtrInx},
    /// };
    ///
    /// // (This would be a standard function, except there are far too many choices to
    /// // make on the backing of the recaster arena and how fallibility should be
    /// // handled)
    /// fn compress_canonical_recaster<P: Ptr, T>(
    ///     a: &mut SimpleOrdArena<P, T, HeapBacking>,
    ///     reset_generation: bool,
    /// ) -> DirectArena<P, P, HeapBacking> {
    ///     // This arena will be a recaster in which we create a mapping from the old
    ///     // `Ptr` domain to the new one. We use a `DirectArena` for this since it will
    ///     // only be used for this purpose and then discarded.
    ///     let mut recaster = DirectArena::<P, P, HeapBacking>::new();
    ///     let mut res = SimpleOrdArena::<P, T, HeapBacking>::new();
    ///     let new_generation = if reset_generation {
    ///         // reset for compactness, only safe if logically old domain `Ptr`s can be
    ///         // eliminated
    ///         P::Gen::two()
    ///     } else {
    ///         // use incremented generation so that all `Ptr`s of the old domain are
    ///         // invalidated
    ///         P::Gen::generational_inc(a.generation()).0
    ///     };
    ///     res.transfer_canonical_reallocating(new_generation, a, |_, o, _| o.allow(), &mut recaster)
    ///         .unwrap();
    ///     *a = res;
    ///     recaster
    /// }
    ///
    /// ptr_struct!(P0);
    ///
    /// type A = SimpleOrdArena<P0, OrdPair<&'static str, ()>, HeapBacking>;
    /// fn layout(a: &A) -> Vec<(usize, &'static str)> {
    ///     a.iter_ordered()
    ///         .map(|(p, pair)| (PtrInx::try_into_usize(p.inx()).unwrap().get(), *pair.k()))
    ///         .collect()
    /// }
    ///
    /// let mut a = A::new();
    /// let _ = a.insert(OrdPair::new("C", ()));
    /// let p_a = a.insert(OrdPair::new("A", ())).0;
    /// let p_d = a.insert(OrdPair::new("D", ())).0;
    /// let _ = a.insert(OrdPair::new("B", ()));
    /// // make an internal slot unallocated, and scatter the keys further
    /// a.remove(p_d).allow().unwrap();
    /// let _ = a.insert(OrdPair::new("E", ()));
    ///
    /// // the keys are in order as would be seen by the `*_ordered` iterators, but at the index level they are scattered
    /// assert_eq!(layout(&a), vec![(2, "A"), (4, "B"), (1, "C"), (3, "E")]);
    ///
    /// let recaster = compress_canonical_recaster(&mut a, false);
    ///
    /// // now the keys are in index order as well, and the internal tree is
    /// // deterministically rebalanced to be perfectly canonical
    /// assert_eq!(layout(&a), vec![(1, "A"), (2, "B"), (3, "C"), (4, "E")]);
    /// // and the recaster is a complete description of where the entries went
    /// assert_eq!(
    ///     &format!("{recaster:#?}"),
    ///     r#"{
    ///     P0[1](2): P0[3](4),
    ///     P0[2](2): P0[1](4),
    ///     P0[3](3): P0[4](4),
    ///     P0[4](2): P0[2](4),
    /// }"#
    /// );
    ///
    /// // external `Ptr`s are fixed up with it
    /// let mut external = p_a;
    /// external.recast(&recaster).unwrap();
    /// assert_eq!(*a[external].k(), "A");
    /// ```
    ///
    /// # Unwind Safety
    ///
    /// If `map` panics, this follows
    /// [ChainArena::transfer_canonical_reallocating], and additionally the tree
    /// of `self` is rebalanced over the entries that did arrive so that `self`
    /// is left in a valid state, and `source` is left as a valid ordered
    /// arena of the entries that were not transferred.
    pub fn transfer_canonical_reallocating<
        Q: Ptr,
        U,
        B1: ArenaBacking,
        F: FnMut(Q, InvalidationOption<U>, P) -> T,
        D: ArenaDirectInsertTrait<Q, P>,
    >(
        &mut self,
        new_generation: P::Gen,
        source: &mut SimpleOrdArena<Q, U, B1>,
        mut map: F,
        recaster: &mut D,
    ) -> Result<(), ReallocationError> {
        // REF(ord_rebalance_guard)
        struct Rebalance<'a, P: Ptr, T, B: ArenaBacking>(&'a mut SimpleOrdArena<P, T, B>);
        impl<P: Ptr, T, B: ArenaBacking> Drop for Rebalance<'_, P, T, B> {
            fn drop(&mut self) {
                self.0.raw_rebalance_assuming_prepared();
            }
        }
        impl<P: Ptr, T, B: ArenaBacking> Rebalance<'_, P, T, B> {
            /// Cancels running `raw_rebalance_assuming_prepared`
            fn cancel(self) {
                let _ = ManuallyDrop::new(self);
            }
        }

        let this = Rebalance(self);
        // by chain arena canonicalization this also sets it up how we want it
        let res = this.0.a.transfer_canonical_reallocating(
            new_generation,
            &mut source.a,
            |q, o, p| SimpleOrdArenaNode {
                t: map(q, o.map(|node| node.t), p),
                p_back: None,
                p_tree0: None,
                p_tree1: None,
                rank: 0,
            },
            recaster,
        );
        if res.is_err() {
            // all of the fallible points happen before anything is modified, so the
            // preexisting tree is still intact and must not be rebalanced over
            this.cancel();
        }
        res
    }

    // TODO probably have some from_ordered_chain function

    /// Calls [clone_from_with](ChainArena::clone_from_with) on `chain_arena`.
    /// The ordering is preserved in a single acyclic chain
    /// ([Link::next](crate::Link::next) points to the next greater entry)
    pub fn clone_to_chain_arena<U, B1: ArenaBacking, F: FnMut(P, &T) -> U>(
        &self,
        chain_arena: &mut ChainArena<P, U, B1>,
        mut map: F,
    ) -> Result<(), ReallocationError> {
        chain_arena.clone_from_with(&self.a, |p, link| map(p, &link.t.t))
    }

    /// Calls [clone_from_with](ArenaCloneFromWith::clone_from_with) on `arena`,
    /// giving all the combined chain arena and ord arena nodes of `self` to the
    /// `Ptr` preserving mapping.
    pub fn clone_to_arena<
        U,
        A: ArenaCloneFromWith<P, U>,
        F: FnMut(P, &LinkNoGen<P, SimpleOrdArenaNode<P, T>>) -> U,
    >(
        &self,
        arena: &mut A,
        map: F,
    ) -> Result<(), ReallocationError> {
        arena.clone_from_with(&self.a.a, map)
    }

    /// Directly returns a reference to the internal backing, for the purposes
    /// of accessing `ArenaBacking`-specific functions
    pub fn backing(&self) -> &B::Stack<ArenaSlot<P, LinkNoGen<P, SimpleOrdArenaNode<P, T>>>> {
        self.a.backing()
    }

    /// Directly returns a mutable reference to the internal backing, for the
    /// purposes of accessing `ArenaBacking`-specific functions
    ///
    /// # Safety
    ///
    /// The `ArenaSlot` allocation state must not be modified, or else the
    /// freelist or entry length could be broken. The `LinkNoGen` interlinks
    /// must also not be modified, or else chain invariants could be broken, and
    /// the `SimpleOrdArenaNode` tree pointers and ranks must not be modified or
    /// else the tree invariants could be broken.
    pub unsafe fn backing_mut(
        &mut self,
    ) -> &mut B::Stack<ArenaSlot<P, LinkNoGen<P, SimpleOrdArenaNode<P, T>>>> {
        // Safety: called in `unsafe` function with same invariants and added invariants
        unsafe { self.a.backing_mut() }
    }
}

/// Implemented if `T: Clone`.
impl<P: Ptr, T: Clone, B: ArenaBacking> Clone for SimpleOrdArena<P, T, B> {
    /// Has the `Ptr` preserving properties of [Arena::clone], and the ordering
    /// and internal tree are preserved as well.
    ///
    /// # Panics
    ///
    /// This function can panic on allocation failure, or if a
    /// [max_capacity](ArenaTrait::max_capacity) limit of the fresh `Self::new`
    /// arena prevents reaching the needed capacity.
    ///
    /// # Unwind Safety
    ///
    /// If a `T::clone` panics, the partially cloned arena is dropped.
    #[track_caller]
    fn clone(&self) -> Self {
        Self {
            root: self.root,
            first: self.first,
            last: self.last,
            a: self.a.clone(),
        }
    }

    /// Has the `Ptr` and capacity preserving properties of
    /// [Arena::clone_from], and the ordering and internal tree are preserved as
    /// well.
    ///
    /// # Panics
    ///
    /// This function can panic on allocation failure, or if a
    /// [max_capacity](ArenaTrait::max_capacity) limit of `self` prevents
    /// reaching the needed capacity.
    ///
    /// # Unwind Safety
    ///
    /// If a `T::clone` or `T::clone_from` panics, `self` is left with a mix of
    /// its old entries and the newly cloned ones, and the ordering and internal
    /// tree can be broken. See
    /// [ChainArena::clone_from](ChainArena::clone_from).
    #[track_caller]
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

    /// Returns a reference to the `T` pointed to by `inx`. Use
    /// [get](ArenaTrait::get) if invalid `Ptr`s need to be handled, or
    /// [get_inx_link_no_gen](SimpleOrdArena::get_inx_link_no_gen) if the
    /// neighboring keys are also needed.
    ///
    /// # Panics
    ///
    /// If `inx` is invalid
    #[track_caller]
    fn index(&self, inx: Q) -> &T {
        let p: P = *inx.borrow();
        self.get(p)
            .expect("indexed `SimpleOrdArena` with invalidated `Ptr`")
    }
}

impl<P: Ptr, T, B: ArenaBacking, Q: Borrow<P>> IndexMut<Q> for SimpleOrdArena<P, T, B> {
    /// Returns a mutable reference to the `T` pointed to by `inx`. Use
    /// [get_mut](ArenaTrait::get_mut) if invalid `Ptr`s need to be handled.
    /// Note that it is a logic error to change the key ordering of the `T`.
    ///
    /// # Panics
    ///
    /// If `inx` is invalid
    #[track_caller]
    fn index_mut(&mut self, inx: Q) -> &mut T {
        let p: P = *inx.borrow();
        self.get_mut(p)
            .expect("indexed `SimpleOrdArena` with invalidated `Ptr`")
    }
}

impl<P: Ptr, T: Debug, B: ArenaBacking> Debug for SimpleOrdArena<P, T, B> {
    /// Unlike the unordered arenas, this is in key order and not in internal
    /// slot order
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO here and in other triple `Debug`s we need a flat triple
        f.debug_map().entries(self.iter_ordered()).finish()
    }
}

impl<P: Ptr, T: PartialEq, B0: ArenaBacking> SimpleOrdArena<P, T, B0> {
    /// Checks if there is the same number of `T` and if all `T` in order are
    /// equal. This is sensitive to nonhereditary ordering, but does not
    /// compare pointers, generations, arena capacities, or internal tree
    /// configuration, or `self.generation()`.
    pub fn canonical_eq<Q: Ptr, B1: ArenaBacking>(&self, other: &SimpleOrdArena<Q, T, B1>) -> bool {
        let mut iter1 = other.iter_ordered();
        for (_, t0) in self.iter_ordered() {
            if let Some((_, t1)) = iter1.next() {
                if t0 != t1 {
                    return false;
                }
            } else {
                return false;
            }
        }
        iter1.next().is_none()
    }
}

impl<P: Ptr, T: PartialOrd, B0: ArenaBacking> SimpleOrdArena<P, T, B0> {
    /// Orders as if the arena were a `Vec<T>` in order, returning early if
    /// the prefix had a difference, and returning based on which is longer.
    /// This is sensitive to nonhereditary ordering, but does not compare
    /// pointers, generations, arena capacities, internal tree
    /// configuration, or `self.generation()`.
    pub fn canonical_partial_cmp<Q: Ptr, B1: ArenaBacking>(
        &self,
        other: &SimpleOrdArena<Q, T, B1>,
    ) -> Option<Ordering> {
        let mut iter1 = other.iter_ordered();
        for (_, t0) in self.iter_ordered() {
            if let Some((_, t1)) = iter1.next() {
                match t0.partial_cmp(t1) {
                    Some(Ordering::Equal) => (),
                    ord => return ord,
                }
            } else {
                return Some(Ordering::Greater);
            }
        }
        if iter1.next().is_none() {
            Some(Ordering::Equal)
        } else {
            Some(Ordering::Less)
        }
    }
}

impl<P: Ptr, T: Ord, B0: ArenaBacking> SimpleOrdArena<P, T, B0> {
    /// Orders as if the arena were a `Vec<T>` in order, returning early if
    /// the prefix had a difference, and returning based on which is longer.
    /// This is sensitive to nonhereditary ordering, but does not compare
    /// pointers, generations, arena capacities, internal tree
    /// configuration, or `self.generation()`.
    pub fn canonical_cmp<Q: Ptr, B1: ArenaBacking>(
        &self,
        other: &SimpleOrdArena<Q, T, B1>,
    ) -> Ordering {
        let mut iter1 = other.iter_ordered();
        for (_, t0) in self.iter_ordered() {
            if let Some((_, t1)) = iter1.next() {
                match t0.cmp(t1) {
                    Ordering::Equal => (),
                    ord => return ord,
                }
            } else {
                return Ordering::Greater;
            }
        }
        if iter1.next().is_none() {
            Ordering::Equal
        } else {
            Ordering::Less
        }
    }
}

impl<P: Ptr, T, B: ArenaBacking> SetMaxCapacity for SimpleOrdArena<P, T, B>
where
    <B as ArenaBacking>::Stack<ArenaSlot<P, LinkNoGen<P, SimpleOrdArenaNode<P, T>>>>:
        SetMaxCapacity,
{
    fn set_max_capacity(&mut self, max_capacity: usize) -> Result<(), MaxCapacityReductionError> {
        self.a.set_max_capacity(max_capacity)
    }
}
