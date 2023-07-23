#![allow(clippy::type_complexity)]

use core::{
    cmp::{min, Ordering},
    mem,
};

use crate::{Arena, ChainArena, Link, Ptr, PtrInx};

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

#[derive(Clone)]
pub(crate) struct Node<P: Ptr, K: Ord, V> {
    k: K,
    v: V,
    // Pointer back to parent
    p_back: Option<P::Inx>,
    // Pointer to left subtree
    p_tree0: Option<P::Inx>,
    // Pointer to right subtree
    p_tree1: Option<P::Inx>,
    // we do not have to worry about overflow because the worst case is that the root rank is
    // 2*lb(len), meaning that even i128::MAX could not overflow this.
    rank: u8,
}

/// An Ordered Arena with three parameters: a `P: Ptr` type that gives single
/// indirection access to elements, a `K: Ord` key type that is used to define
/// an ordering among elements, and a `V` value type that is not ordered over
/// but is associated with each `K`. `O(log n)` insertions and deletions are
/// guaranteed.
///
/// This is similar to the standard `BTreeMap`, but is more powerful and
/// performant because of the arena strategy. It internally uses a specialized
/// WAVL tree on a `ChainArena` with one-to-one tree node and key-value pair
/// storage, which enables all the properties of arenas including stable `Ptr`
/// references (as long as the `Ptr` returned from initial insertion is kept
/// around, `O(1)` single indirection lookups and no more `O(log n)` key finds
/// are needed to access the key-value pair afterwards). The tree is balanced
/// such that the number of internal lookups needed to find a key is at most
/// about `1.44 * log_2(arena.len())` if only insertions are used, otherwise the
/// worst case is `2 * log_2(arena.len())`.
///
/// Note that multiple equal keys are allowed through the `insert_nonhereditary`
/// function.
///
/// Note: it is a logic error for a key's ordering to change relative to other
/// keys. The functions are constructed such that _no_ panics, aborts, memory
/// leaks, or non-termination occurs. However, the well ordered property,
/// `find_key`, and hereditary properties may be broken for any entry in the
/// arena.
///
/// ```
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
/// ```
pub struct OrdArena<P: Ptr, K: Ord, V> {
    pub(crate) root: P::Inx,
    pub(crate) first: P::Inx,
    pub(crate) last: P::Inx,
    pub(crate) a: ChainArena<P, Node<P, K, V>>,
}

impl<P: Ptr, K: Ord, V> OrdArena<P, K, V> {
    /// Used by tests
    #[doc(hidden)]
    pub fn _check_invariants(this: &Self) -> Result<(), &'static str> {
        if this.a.is_empty() {
            return Ok(())
        }
        // check the root
        if let Some((_, root)) = this.a.get_ignore_gen(this.root) {
            if root.p_back.is_some() {
                return Err("root node has a back pointer")
            }
        } else {
            return Err("this.root is broken")
        };
        // first check the chain and ordering
        let mut count = 0;
        let mut prev: Option<P> = None;
        let first_gen = if let Some((first_gen, link)) = this.a.get_ignore_gen(this.first) {
            if Link::prev(link).is_some() {
                return Err("this.first is broken")
            }
            first_gen
        } else {
            return Err("this.first is broken")
        };
        let init: P = Ptr::_from_raw(this.first, first_gen);
        let mut p = init;
        let mut switch = false;
        let mut stop = this.a.is_empty();
        loop {
            if stop {
                break
            }

            count += 1;
            if !this.a.contains(p) {
                return Err("invalid Ptr")
            }
            if let Some(prev) = prev {
                if Ord::cmp(
                    &this.a.get_ignore_gen(prev.inx()).unwrap().1.t.k,
                    &this.a.get_ignore_gen(p.inx()).unwrap().1.t.k,
                ) == Ordering::Greater
                {
                    return Err("incorrect ordering")
                }
            }

            prev = Some(p);
            this.a.next_chain_ptr(init, &mut p, &mut switch, &mut stop);
        }
        if let Some(prev) = prev {
            if prev.inx() != this.last {
                return Err("this.last is not correct")
            }
        }
        if count != this.a.len() {
            return Err("multiple chains")
        }
        // after the linear checks, check the tree
        let (mut p, mut b) = this.a.first_ptr();
        loop {
            if b {
                break
            }

            let node = &this.a.get(p).unwrap().t;
            if let Some(p_back) = node.p_back {
                if let Some((_, parent)) = this.a.get_ignore_gen(p_back) {
                    if (parent.p_tree0 != Some(p.inx())) && (parent.p_tree1 != Some(p.inx())) {
                        return Err("broken tree")
                    }
                } else {
                    return Err("broken tree")
                }
            } else {
                // should be root, if this passes it implies there is only one common root
                if p.inx() != this.root {
                    return Err("more than one root node")
                }
            }
            if let Some(p_tree0) = node.p_tree0 {
                // prevent some unbalanced cases that the rank checks would not catch
                if Some(p_tree0) == node.p_tree1 {
                    return Err("`p_tree0` and `p_tree1` are the same")
                }
                if let Some((_, child0)) = this.a.get_ignore_gen(p_tree0) {
                    if child0.p_back != Some(p.inx()) {
                        return Err("broken tree")
                    }
                    if child0.p_back == Some(p_tree0) {
                        return Err("cycle")
                    }
                } else {
                    return Err("broken tree")
                }
            }
            if let Some(p_tree1) = node.p_tree1 {
                if let Some((_, child1)) = this.a.get_ignore_gen(p_tree1) {
                    if child1.p_back != Some(p.inx()) {
                        return Err("broken tree")
                    }
                    if child1.p_back == Some(p_tree1) {
                        return Err("cycle")
                    }
                } else {
                    return Err("broken tree")
                }
            }

            this.a.next_ptr(&mut p, &mut b);
        }
        // check the ranks
        let (mut p, mut b) = this.a.first_ptr();
        loop {
            if b {
                break
            }

            let node = &this.a.get(p).unwrap().t;

            let rank0 = if let Some(p_tree0) = node.p_tree0 {
                this.a.get_inx_unwrap(p_tree0).rank
            } else {
                0
            };
            if node.rank <= rank0 {
                return Err("rank difference is zero or negative")
            }
            let rank1 = if let Some(p_tree1) = node.p_tree1 {
                this.a.get_inx_unwrap(p_tree1).rank
            } else {
                0
            };
            if node.rank <= rank1 {
                return Err("rank difference is zero or negative")
            }
            if node.rank > min(rank0, rank1).wrapping_add(2) {
                return Err("rank difference is greater than 2")
            }
            if node.p_tree0.is_none() && node.p_tree1.is_none() && (node.rank != 1) {
                return Err("leaf node is not rank 1")
            }

            this.a.next_ptr(&mut p, &mut b);
        }
        Ok(())
    }

    pub fn new() -> Self {
        Self {
            root: PtrInx::new(0),
            first: PtrInx::new(0),
            last: PtrInx::new(0),
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

    /// Inserts at a leaf and manages ordering and replacement. Returns `Ok` if
    /// there is a new insertion, which will need to be rebalanced. Returns
    /// `Err` if there was a replacement (which does not happen with the
    /// nonhereditary case).
    fn raw_insert(&mut self, k: K, v: V, nonhereditary: bool) -> (P, Option<(K, V)>) {
        if self.a.is_empty() {
            let p_new = self.a.insert_new(Node {
                k,
                v,
                p_back: None,
                p_tree0: None,
                p_tree1: None,
                rank: 1,
            });
            self.first = p_new.inx();
            self.last = p_new.inx();
            self.root = p_new.inx();
            return (p_new, None)
        }
        let mut p = self.root;
        loop {
            let (gen, link) = self.a.get_ignore_gen(p).unwrap();
            let node = &link.t;
            let p_with_gen = Ptr::_from_raw(p, gen);
            match Ord::cmp(&k, &node.k) {
                Ordering::Less => {
                    if let Some(p_tree0) = node.p_tree0 {
                        p = p_tree0
                    } else {
                        // insert new leaf
                        let new_node = Node {
                            k,
                            v,
                            p_back: Some(p),
                            p_tree0: None,
                            p_tree1: None,
                            rank: 1,
                        };
                        if let Ok(p_new) = self.a.insert((None, Some(p_with_gen)), new_node) {
                            // fix tree pointer in leaf direction
                            self.a.get_ignore_gen_mut(p).unwrap().1.p_tree0 = Some(p_new.inx());
                            if self.first == p {
                                self.first = p_new.inx()
                            }
                            break (p_new, None)
                        } else {
                            unreachable!()
                        }
                    }
                }
                Ordering::Equal => {
                    if nonhereditary {
                        // supporting multiple equal keys
                        // need to get to leaves, use `p_tree0` bias to get to first spot
                        if let Some(p_tree0) = node.p_tree0 {
                            p = p_tree0
                        } else if let Some(p_tree1) = node.p_tree1 {
                            p = p_tree1
                        } else {
                            // go the Ordering::Less route
                            let new_node = Node {
                                k,
                                v,
                                p_back: Some(p),
                                p_tree0: None,
                                p_tree1: None,
                                rank: 1,
                            };
                            if let Ok(p_new) = self.a.insert((None, Some(p_with_gen)), new_node) {
                                self.a.get_ignore_gen_mut(p).unwrap().1.p_tree0 = Some(p_new.inx());
                                if self.first == p {
                                    self.first = p_new.inx()
                                }
                                break (p_new, None)
                            } else {
                                unreachable!()
                            }
                        }
                    } else {
                        let old_v = mem::replace(&mut self.a.get_mut(p_with_gen).unwrap().v, v);
                        return (p_with_gen, Some((k, old_v)))
                    }
                }
                Ordering::Greater => {
                    if let Some(p_tree1) = node.p_tree1 {
                        p = p_tree1
                    } else {
                        let new_node = Node {
                            k,
                            v,
                            p_back: Some(p),
                            p_tree0: None,
                            p_tree1: None,
                            rank: 1,
                        };
                        if let Ok(p_new) = self.a.insert((Some(p_with_gen), None), new_node) {
                            self.a.get_ignore_gen_mut(p).unwrap().1.p_tree1 = Some(p_new.inx());
                            if self.last == p {
                                self.last = p_new.inx()
                            }
                            break (p_new, None)
                        } else {
                            unreachable!()
                        }
                    }
                }
            }
        }
    }

    /// Same as [OrdArena::raw_insert] except that it uses linear probing
    /// starting from `p`. If `p_init` is `None`, this will return an error
    /// unless `self.is_empty()`.
    fn raw_insert_linear(
        &mut self,
        p_init: Option<P>,
        k: K,
        v: V,
        nonhereditary: bool,
    ) -> Result<(P, Option<(K, V)>), (K, V)> {
        if let Some(p_init) = p_init {
            if !self.a.contains(p_init) {
                return Err((k, v))
            }
            let mut p = p_init.inx();
            // detects if we would switch probing directions, note that even if `Ord` is
            // rigged to do nontransitive things it will still not result in an infinite
            // loop
            let mut direction = None;
            let direction = loop {
                let link = self.a.get_inx_unwrap(p);
                match Ord::cmp(&k, &link.t.k) {
                    Ordering::Less => {
                        if direction == Some(true) {
                            break Ordering::Less
                        }
                        direction = Some(false);
                        if let Some(prev) = Link::prev(link) {
                            p = prev.inx();
                        } else {
                            break Ordering::Less
                        }
                    }
                    Ordering::Equal => break Ordering::Equal,
                    Ordering::Greater => {
                        if direction == Some(false) {
                            break Ordering::Greater
                        }
                        direction = Some(true);
                        if let Some(next) = Link::next(link) {
                            p = next.inx();
                        } else {
                            break Ordering::Greater
                        }
                    }
                }
            };
            let link = self.a.get_inx_unwrap(p);
            // first, step to node with `None` subtree if we need to
            let direction = match direction {
                Ordering::Less => {
                    if link.p_tree0.is_some() {
                        p = Link::prev(link).unwrap().inx();
                        Ordering::Greater
                    } else {
                        Ordering::Less
                    }
                }
                Ordering::Equal => {
                    if nonhereditary {
                        if link.p_tree0.is_some() {
                            p = Link::prev(link).unwrap().inx();
                            // special case to account for rank 2 elbos
                            Ordering::Greater
                        } else {
                            Ordering::Less
                        }
                    } else {
                        direction
                    }
                }
                Ordering::Greater => {
                    if link.p_tree1.is_some() {
                        p = Link::next(link).unwrap().inx();
                        Ordering::Less
                    } else {
                        Ordering::Greater
                    }
                }
            };
            let (gen, _) = self.a.get_ignore_gen(p).unwrap();
            let p_with_gen = Ptr::_from_raw(p, gen);
            match direction {
                Ordering::Less => {
                    // insert new leaf
                    let new_node = Node {
                        k,
                        v,
                        p_back: Some(p),
                        p_tree0: None,
                        p_tree1: None,
                        rank: 1,
                    };
                    if let Ok(p_new) = self.a.insert((None, Some(p_with_gen)), new_node) {
                        // fix tree pointer in leaf direction
                        self.a.get_ignore_gen_mut(p).unwrap().1.p_tree0 = Some(p_new.inx());
                        if self.first == p {
                            self.first = p_new.inx()
                        }
                        Ok((p_new, None))
                    } else {
                        unreachable!()
                    }
                }
                Ordering::Equal => {
                    if nonhereditary {
                        unreachable!()
                    } else {
                        let old_v = mem::replace(&mut self.a.get_mut(p_with_gen).unwrap().v, v);
                        Ok((p_with_gen, Some((k, old_v))))
                    }
                }
                Ordering::Greater => {
                    let new_node = Node {
                        k,
                        v,
                        p_back: Some(p),
                        p_tree0: None,
                        p_tree1: None,
                        rank: 1,
                    };
                    if let Ok(p_new) = self.a.insert((Some(p_with_gen), None), new_node) {
                        self.a.get_ignore_gen_mut(p).unwrap().1.p_tree1 = Some(p_new.inx());
                        if self.last == p {
                            self.last = p_new.inx()
                        }
                        Ok((p_new, None))
                    } else {
                        unreachable!()
                    }
                }
            }
        } else if self.a.is_empty() {
            let p_new = self.a.insert_new(Node {
                k,
                v,
                p_back: None,
                p_tree0: None,
                p_tree1: None,
                rank: 1,
            });
            self.first = p_new.inx();
            self.last = p_new.inx();
            self.root = p_new.inx();
            return Ok((p_new, None))
        } else {
            return Err((k, v))
        }
    }

    /// Rebalances starting from newly inserted node `p`
    fn rebalance_inserted(&mut self, p: P::Inx) {
        // We keep record of the last three nodes for trinode restructuring.
        // We also keep the direction of the two edges between the nodes in
        // order to know exactly what trinode restructuring to choose
        let mut p0 = p;
        let n0 = self.a.get_inx_unwrap(p0);

        //  ? (1,2)
        //    /
        //   /
        // n0 (1)   (node `n0` has rank 1 and may have a parent of rank 1 or 2)
        //
        // `n1` cannot have rank 3 because the previous place that `n0` was inserted to
        // would be a rank 0 `None` child, and the rank difference between it and `n1`
        // would be 3, which would contradict invariants

        let (n1, mut p1) = if let Some(p1) = n0.p_back {
            // in case `n1` was rank 1 we must promote it, the loop expects no rank
            // violations at p1 and below (also, if it is rank 2 then it is within rank
            // difference 2 of the `None` sibling to `n0`)

            //  ? (2,3) or (3,4)
            //        /
            //       /
            //  n1 (1) or (2)
            //     /   \
            //    /     \
            // n0 (1)  s0 (0,1)

            let n1 = self.a.get_inx_mut_unwrap_t(p1);
            if n1.rank == 2 {
                //       ? (3,4)
                //         /
                //        /
                //     n1 (2)
                //     /   \
                //    /     \
                // n0 (1)  s0 (0,1)

                // this isn't just an optimization, later branches need to make sure that the
                // rank of `s0` has a rank difference of 2 below `n1`
                return
            } else {
                //      ? (2,3)
                //        /
                //       /
                //     n1 (1)
                //     /   \
                //    /     \
                // n0 (1)  s0 (0)
                n1.rank = 2;
                //      ? (2,3)
                //        /
                //       /
                //     n1 (2)
                //     /   \
                //    /     \
                // n0 (1)  s0 (0)
            }
            (self.a.get_inx_unwrap(p1), p1)
        } else {
            // single node tree, inserted node was inserted as rank 1 which is immediately
            // correct

            // n0 (1)
            return
        };
        let mut d01 = n1.p_tree1 == Some(p0);
        let (n2, mut p2) = if let Some(p2) = n1.p_back {
            //      n2 (2,3)
            //        /
            //       /
            //     n1 (2)
            //    /    \
            //   /      \
            // n0 (1)  s0 (0)
            (self.a.get_inx_unwrap(p2), p2)
        } else {
            // height 2 tree, ranks are guaranteed correct because the root is at rank 2

            //     n1 (2)
            //    /    \
            //   /      \
            // n0 (1)  s0 (0)
            return
        };
        let mut d12 = n2.p_tree1 == Some(p1);
        loop {
            // the prelude and any previous iterations of this loop must lead the state to
            // match with

            //    n2 (r+1,r+2)
            //        /
            //       /
            //    n1 (r+1)
            //    /     \
            //   /       \
            // n0 (r)   s0 (r-1)
            //
            // (also `d01` and `d12` can alternate, but that only becomes
            // important during restructuring)
            let n0 = self.a.get_inx_unwrap(p0);
            let n1 = self.a.get_inx_unwrap(p1);
            let n2 = self.a.get_inx_unwrap(p2);
            let p3 = n2.p_back;

            let rank0 = n0.rank;
            let rank1 = n1.rank;
            let rank2 = n2.rank;
            if rank1 < rank2 {
                //      n2 (r+2)
                //        /
                //       /
                //    n1 (r+1)
                //    /     \
                //   /       \
                // n0 (r)   s0 (r-1)
                break
            }
            //           ? (r+2,r+3)
            //             /
            //            /
            //         n2 (r+1)
            //        /       \
            //       /         \
            //    n1 (r+1)   s1 (r-1,r)
            //    /     \
            //   /       \
            // n0 (r)   s0 (r-1)

            // Check the sibling of n1 to see if we can promote n2 and avoid a restructure.
            // This isn't just an optimization, a general case restructure requires the
            // sibling of n1 to be 2 ranks below n2 or else the restructure may introduce
            // lower height violations.
            let p_s1 = if d12 { n2.p_tree0 } else { n2.p_tree1 };
            let rank_s1 = if let Some(p_s1) = p_s1 {
                self.a.get_inx_unwrap(p_s1).rank
            } else {
                0
            };
            if rank_s1.wrapping_add(1) == rank2 {
                // if there is a rank difference of 1, we can promote the shared `n2` and avoid
                // a violation with the sibling

                //           ? (r+2,r+3)
                //             /
                //            /
                //         n2 (r+1)
                //        /       \
                //       /         \
                //    n1 (r+1)   s1 (r)
                //    /     \
                //   /       \
                // n0 (r)   s0 (r-1)
                //
                self.a.get_inx_mut_unwrap_t(p2).rank = rank1.wrapping_add(1);
                //
                //           ? (r+2,r+3)
                //             /
                //            /
                //         n2 (r+2)
                //        /       \
                //       /         \
                //    n1 (r+1)   s1 (r)
                //    /     \
                //   /       \
                // n0 (r)   s0 (r-1)
                if let Some(p3) = p3 {
                    // convey up the tree

                    //           n3 (r+2,r+3)
                    //             /
                    //            /
                    //         n2 (r+2)
                    //        /       \
                    //       /         \
                    //    n1 (r+1)   s1 (r)
                    //    /     \
                    //   /       \
                    // n0 (r)   s0 (r-1)
                    //
                    //   ==> (recode for next iteration)
                    //
                    //           n2 (r+1,r+2)
                    //             /
                    //            /
                    //         n1 (r+1)
                    //        /       \
                    //       /         \
                    //    n0 (r)     s0 (r-1)
                    //    /     \
                    //   /       \
                    //  * *
                    //
                    // which matches with loop entry assumption

                    p0 = p1;
                    p1 = p2;
                    p2 = p3;
                    d01 = d12;
                    d12 = self.a.get_inx_unwrap(p2).p_tree1 == Some(p1);
                    continue
                } else {
                    // n2 was the root, the rest of the tree is ok

                    //         n2 (r+2)
                    //        /       \
                    //       /         \
                    //    n1 (r+1)   s1 (r)
                    //    /     \
                    //   /       \
                    // n0 (r)   s0 (r-1)
                    break
                }
            }

            //           ? (r+2,r+3)
            //             /
            //            /
            //         n2 (r+1)
            //        /       \
            //       /         \
            //    n1 (r+1)   s1 (r-1)
            //    /     \
            //   /       \
            // n0 (r)   s0 (r-1)

            // now the directions `d10` and `d12` and the order of subtrees will matter for
            // restructuring

            if d01 == d12 {
                // nonalternating case
                //
                //         ----n2 (r+1)
                //        /           \
                //       /             \
                //     n1 (r+1)      s1 (r-1)
                //     /     \
                //    /       \
                // n0 (r)   s0 (r-1)
                //
                // n0  n1   s0 n2    s1
                //
                //     n1 (r+1)
                //     /     \
                //    /       \
                // n0 (r)      n2 (r)
                //             /    \
                //            /      \
                //          s0 (r-1) s1 (r-1)

                let p_s0 = if d01 { n1.p_tree0 } else { n1.p_tree1 };
                if let Some(p_s0) = p_s0 {
                    let s0 = self.a.get_inx_mut_unwrap_t(p_s0);
                    s0.p_back = Some(p2);
                }
                if d01 {
                    // reversed version
                    let n1 = self.a.get_inx_mut_unwrap_t(p1);
                    n1.p_tree0 = Some(p2);
                    n1.p_back = p3;
                    let n2 = self.a.get_inx_mut_unwrap_t(p2);
                    n2.p_tree0 = p_s1;
                    n2.p_back = Some(p1);
                    n2.p_tree1 = p_s0;
                    n2.rank = rank0;
                } else {
                    let n1 = self.a.get_inx_mut_unwrap_t(p1);
                    n1.p_back = p3;
                    n1.p_tree1 = Some(p2);
                    let n2 = self.a.get_inx_mut_unwrap_t(p2);
                    n2.p_tree0 = p_s0;
                    n2.p_back = Some(p1);
                    n2.p_tree1 = p_s1;
                    n2.rank = rank0;
                }
                if let Some(p3) = p3 {
                    let n3 = self.a.get_inx_mut_unwrap_t(p3);
                    if n3.p_tree1 == Some(p2) {
                        n3.p_tree1 = Some(p1);
                    } else {
                        n3.p_tree0 = Some(p1);
                    }
                } else {
                    // we have reached the root
                    self.root = p1;
                }
            } else {
                // alternating case
                //
                //         -------n2 (r+1)
                //        /         \
                //       /           \
                //    n1 (r+1)       s1 (r-1)
                //    /     \
                //   /       \
                // s0 (r-1)  n0 (r)
                //          / \
                //         /   \
                //        a     b
                //
                // s0 n1  a  n0 b n2 s1
                //
                //       ----n0 (r+1)
                //      /         \
                //     /           \
                //    n1 (r)      n2 (r)
                //   /  \         / \
                //  /    \       /   \
                // s0     a     b    s1 (r-1)

                let (p_a, p_b) = if d01 {
                    (n0.p_tree1, n0.p_tree0)
                } else {
                    (n0.p_tree0, n0.p_tree1)
                };
                if let Some(p_a) = p_a {
                    self.a.get_inx_mut_unwrap_t(p_a).p_back = Some(p2);
                }
                if let Some(p_b) = p_b {
                    self.a.get_inx_mut_unwrap_t(p_b).p_back = Some(p1);
                }
                if d01 {
                    let n1 = self.a.get_inx_mut_unwrap_t(p1);
                    n1.p_back = Some(p0);
                    n1.p_tree1 = p_b;
                    n1.rank = rank0;
                    let n0 = self.a.get_inx_mut_unwrap_t(p0);
                    n0.p_tree0 = Some(p1);
                    n0.p_back = p3;
                    n0.p_tree1 = Some(p2);
                    n0.rank = rank1;
                    let n2 = self.a.get_inx_mut_unwrap_t(p2);
                    n2.p_tree0 = p_a;
                    n2.p_back = Some(p0);
                    n2.rank = rank0;
                } else {
                    // reverse version
                    let n1 = self.a.get_inx_mut_unwrap_t(p1);
                    n1.p_tree0 = p_b;
                    n1.p_back = Some(p0);
                    n1.rank = rank0;
                    let n0 = self.a.get_inx_mut_unwrap_t(p0);
                    n0.p_tree0 = Some(p2);
                    n0.p_back = p3;
                    n0.p_tree1 = Some(p1);
                    n0.rank = rank1;
                    let n2 = self.a.get_inx_mut_unwrap_t(p2);
                    n2.p_back = Some(p0);
                    n2.p_tree1 = p_a;
                    n2.rank = rank0;
                }
                if let Some(p3) = p3 {
                    let n3 = self.a.get_inx_mut_unwrap_t(p3);
                    if n3.p_tree1 == Some(p2) {
                        n3.p_tree1 = Some(p0);
                    } else {
                        n3.p_tree0 = Some(p0);
                    }
                } else {
                    // we have reached the root
                    self.root = p0;
                }
            }
            // The previous branches all result in the next higher rank difference not being
            // violated, so we can just return. This also implies that we only need at most
            // one restructure.
            break
        }
    }

    /// Inserts key `k` and an associated value `v` into `self` and returns a
    /// `Ptr` to it. If the inserted key is equal to a key already contained in
    /// `self`, the new value replaces the old value, and `k` and the old value
    /// are returned. The existing key is not replaced, which should not make a
    /// difference unless special `Ord` definitions are being used.
    #[must_use]
    pub fn insert(&mut self, k: K, v: V) -> (P, Option<(K, V)>) {
        let (p, k_v) = self.raw_insert(k, v, false);
        if k_v.is_none() {
            self.rebalance_inserted(p.inx());
        }
        (p, k_v)
    }

    /// Inserts key `k` and an associated value `v` into `self` and returns a
    /// `Ptr` to it. If the inserted key is equal to a key already contained in
    /// `self`, the inserted key is inserted in a `Link::prev` position to
    /// all the equal keys. Future calls to `self.find_key` with an
    /// equal `k` could find any of the equal keys.
    pub fn insert_nonhereditary(&mut self, k: K, v: V) -> P {
        let (p, _) = self.raw_insert(k, v, true);
        self.rebalance_inserted(p.inx());
        p
    }

    /// Uses linear comparisons starting at `p_init` in order to insert `k` and
    /// `v`. If `p_init` is not within a small constant number of elements
    /// away from where `k` should be ordered, this function may operate in
    /// `O(n)` time instead of the `O(1)` this is intended for. If the
    /// inserted key is equal to a key already contained in `self`, the new
    /// value replaces the old value, and `k` and the old value are
    /// returned. If `self.is_empty()`, `p_init` should be `None`, otherwise
    /// there will be an error. Returns an `Err` if `p_init` is invalid or
    /// if it is `None` and `!self.is_empty()`.
    pub fn insert_linear(
        &mut self,
        p_init: Option<P>,
        k: K,
        v: V,
    ) -> Result<(P, Option<(K, V)>), (K, V)> {
        match self.raw_insert_linear(p_init, k, v, false) {
            Ok((p, k_v)) => {
                if k_v.is_none() {
                    self.rebalance_inserted(p.inx());
                }
                Ok((p, k_v))
            }
            Err(k_v) => Err(k_v),
        }
    }

    /// Combines the behaviors of [OrdArena::insert_nonhereditary] and
    /// [OrdArena::insert_linear]
    pub fn insert_nonhereditary_linear(
        &mut self,
        p_init: Option<P>,
        k: K,
        v: V,
    ) -> Result<P, (K, V)> {
        match self.raw_insert_linear(p_init, k, v, true) {
            Ok((p, _)) => {
                self.rebalance_inserted(p.inx());
                Ok(p)
            }
            Err(k_v) => Err(k_v),
        }
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

    /// Finds a `Ptr` with an associated key that is equal to `k`. Returns
    /// `None` if such a key is not in the arena.
    #[must_use]
    pub fn find_key(&self, k: &K) -> Option<P> {
        if self.a.is_empty() {
            return None
        }
        let mut p = self.root;
        loop {
            let (gen, link) = self.a.get_ignore_gen(p).unwrap();
            let node = &link.t;
            match Ord::cmp(k, &node.k) {
                Ordering::Less => p = node.p_tree0?,
                Ordering::Equal => break Some(Ptr::_from_raw(p, gen)),
                Ordering::Greater => p = node.p_tree1?,
            }
        }
    }

    /// Finds a `Ptr` with an associated key that is equal key to `k`. If such a
    /// key is not in the arena, this will instead return a `Ptr` to a similar
    /// key, such that if `k` were to be inserted into the arena, it would be
    /// inserted immediately previous or next to the entry of the returned
    /// `Ptr`. An `Ordering` is returned, with `Ordering::Equal` indicating an
    /// exact match was found, `Ordering::Less` indicating that `k` is less than
    /// the similar entry, and `Ordering::Greater` indicating that `k` is
    /// greater than the similar entry. `None` is returned if `self.is_empty()`.
    pub fn find_similar_key(&self, k: &K) -> Option<(P, Ordering)> {
        if self.a.is_empty() {
            return None
        }
        let mut p = self.root;
        loop {
            let (gen, link) = self.a.get_ignore_gen(p).unwrap();
            let node = &link.t;
            match Ord::cmp(k, &node.k) {
                Ordering::Less => {
                    if let Some(p_tree0) = node.p_tree0 {
                        p = p_tree0;
                    } else {
                        break Some((Ptr::_from_raw(p, gen), Ordering::Less))
                    }
                }
                Ordering::Equal => break Some((Ptr::_from_raw(p, gen), Ordering::Equal)),
                Ordering::Greater => {
                    if let Some(p_tree1) = node.p_tree1 {
                        p = p_tree1;
                    } else {
                        break Some((Ptr::_from_raw(p, gen), Ordering::Greater))
                    }
                }
            }
        }
    }

    /// The same as [OrdArena::find_similar_key], except it uses linear
    /// comparisons starting at `p_init`. If `p` is not within a small constant
    /// number of elements away from where `k` should be ordered, this
    /// function may operate in `O(n)` time instead of the `O(1)` this is
    /// intended for. Returns `None` if `p_init` is invalid.
    pub fn find_similar_key_linear(&self, p_init: P, k: &K) -> Option<(P, Ordering)> {
        if !self.a.contains(p_init) {
            return None
        }
        let mut p = p_init.inx();
        let mut direction = None;
        let ordering = loop {
            let link = self.a.get_inx_unwrap(p);
            let node = &link.t;
            match Ord::cmp(k, &node.k) {
                Ordering::Less => {
                    if direction == Some(true) {
                        break Ordering::Less
                    }
                    direction = Some(false);
                    if let Some(prev) = Link::prev(link) {
                        p = prev.inx();
                    } else {
                        break Ordering::Less
                    }
                }
                Ordering::Equal => break Ordering::Equal,
                Ordering::Greater => {
                    if direction == Some(false) {
                        break Ordering::Greater
                    }
                    direction = Some(true);
                    if let Some(next) = Link::next(link) {
                        p = next.inx();
                    } else {
                        break Ordering::Greater
                    }
                }
            }
        };
        let (gen, _) = self.a.get_ignore_gen(p).unwrap();
        Some((Ptr::_from_raw(p, gen), ordering))
    }

    /// Returns if `p` is a valid `Ptr`
    pub fn contains(&self, p: P) -> bool {
        self.a.contains(p)
    }

    /// Returns the full `Link<P, (&K, &V)>`. Using [Link::prev] on the result
    /// gives the `Ptr` to the next lesser key, and using [Link::next] gives the
    /// `Ptr` to the next greater key.
    #[must_use]
    pub fn get_link(&self, p: P) -> Option<Link<P, (&K, &V)>> {
        self.a
            .get(p)
            .map(|link| Link::new(Link::prev_next(link), (&link.k, &link.v)))
    }

    /// Returns a reference to the key-value pair pointed to by `p`
    #[must_use]
    pub fn get(&self, p: P) -> Option<(&K, &V)> {
        self.a.get(p).map(|link| (&link.k, &link.v))
    }

    /// Returns a reference to the key pointed to by `p`
    #[must_use]
    pub fn get_key(&self, p: P) -> Option<&K> {
        self.a.get(p).map(|link| &link.k)
    }

    /// Returns a reference to the value pointed to by `p`
    #[must_use]
    pub fn get_val(&self, p: P) -> Option<&V> {
        self.a.get(p).map(|link| &link.v)
    }

    /// Invalidates all references to the entry pointed to by `p`, and returns a
    /// new valid reference. Does no invalidation and returns `None` if `p` is
    /// invalid.
    #[must_use]
    pub fn invalidate(&mut self, p: P) -> Option<P> {
        let p_new = self.a.invalidate(p)?;
        if let Some(p_tree0) = self.a.get(p).unwrap().p_tree0 {
            self.a.get_ignore_gen_mut(p_tree0).unwrap().1.p_back = Some(p_new.inx());
        }
        if let Some(p_tree1) = self.a.get(p).unwrap().p_tree1 {
            self.a.get_ignore_gen_mut(p_tree1).unwrap().1.p_back = Some(p_new.inx());
        }
        if let Some(p_back) = self.a.get(p).unwrap().p_back {
            let parent = self.a.get_ignore_gen_mut(p_back).unwrap().1.t;
            if parent.p_tree0 == Some(p.inx()) {
                parent.p_tree0 = Some(p_new.inx());
            } else {
                parent.p_tree1 = Some(p_new.inx());
            }
        }
        Some(p_new)
    }

    /// Removes the key-value entry at `p`. Returns `None` if `p` is invalid.
    #[must_use]
    pub fn remove(&mut self, p: P) -> Option<(K, V)> {
        let link = self.a.remove(p)?;
        if self.a.is_empty() {
            // last node to be removed, our invariants require that `self.a.is_empty` be
            // checked to determine whether or not `self.first`, etc are valid.
            return Some((link.t.k, link.t.v))
        }

        // when removing a nonleaf node of the tree, its place in the tree is
        // replaced by a similar node, and if that node is nonleaf then it is
        // replaced again. We reach a leaf node in 2 replacements in the worst case:
        //
        //                      -----...
        //                     /
        //                    /
        //                   d
        //                  / \
        //       -----------   \
        //      /               \
        //     x                ...
        //    / \
        //   /   \
        // ...   ...
        //        \
        //         \
        //          y (4)
        //         / \
        //        /   \
        //      ...    --r (2)
        //              /
        //             /
        //            z (1)
        //
        // `d` is replaced by `r`, then `r` is replaced by `z`, and we are left with the
        // much simpler task of rebalancing from the exterior of the tree.

        // previous configuration of displaced node
        let (mut p_d, mut d_tree0, mut d_tree1, mut d_back, mut d_rank, mut d_prev, mut d_next) = (
            p.inx(),
            link.p_tree0,
            link.p_tree1,
            link.p_back,
            link.rank,
            Link::prev(&link),
            Link::next(&link),
        );
        let mut use_next = false;
        let mut p1 = d_back;
        loop {
            if d_tree0.is_some() || d_tree1.is_some() {
                // pointer to replacement node
                let p_r = if use_next {
                    d_next.unwrap()
                } else if let Some(p_r) = d_prev {
                    if (d_rank == 2) && (d_tree0.is_none()) {
                        // if we are on a displaced rank 2 node that has a `None` `p_tree0`,
                        // look at `p_tree1` to avoid going up the tree
                        use_next = true;
                        d_next.unwrap()
                    } else {
                        p_r
                    }
                } else {
                    // if on the first `Link::prev` acquire we get a `None` (because we are on
                    // the start), go only `Link::next`
                    use_next = true;
                    d_next.unwrap()
                }
                .inx();
                let r = self.a.get_inx_mut_unwrap(p_r);
                // keep the old configuration of the replacement node
                let buf = (
                    r.p_tree0,
                    r.p_tree1,
                    r.p_back,
                    r.rank,
                    Link::prev(&r),
                    Link::next(&r),
                );
                r.t.rank = d_rank;
                if let Some(d_back) = d_back {
                    if d_back != p.inx() {
                        r.t.p_back = Some(d_back);
                        let n = self.a.get_inx_mut_unwrap_t(d_back);
                        if n.p_tree1 == Some(p_d) {
                            n.p_tree1 = Some(p_r);
                        } else {
                            n.p_tree0 = Some(p_r);
                        }
                    }
                } else {
                    r.t.p_back = None;
                    self.root = p_r;
                }
                let mut use_p_d = false;
                let r = self.a.get_inx_mut_unwrap_t(p_r);
                if let Some(d_tree0) = d_tree0 {
                    if d_tree0 != p_r {
                        r.p_tree0 = Some(d_tree0);
                        self.a.get_inx_mut_unwrap_t(d_tree0).p_back = Some(p_r);
                    } else {
                        // in the case where the replacement node is a child of the displaced node,
                        // we need to leave `p_tree0` as-is
                        use_p_d = true;
                    }
                } else {
                    r.p_tree0 = None;
                }
                let r = self.a.get_inx_mut_unwrap_t(p_r);
                if let Some(d_tree1) = d_tree1 {
                    if d_tree1 != p_r {
                        r.p_tree1 = Some(d_tree1);
                        self.a.get_inx_mut_unwrap_t(d_tree1).p_back = Some(p_r);
                    } else {
                        use_p_d = true;
                    }
                } else {
                    r.p_tree1 = None;
                }
                // the replacement node becomes the displacement node for the next round
                p_d = p_r;
                d_tree0 = buf.0;
                d_tree1 = buf.1;
                d_back = buf.2;
                d_rank = buf.3;
                d_prev = buf.4;
                d_next = buf.5;
                if use_p_d {
                    p1 = Some(p_d);
                } else {
                    p1 = d_back;
                }
            } else {
                break
            }
        }
        let mut p0 = None;
        let mut p1 = p1.unwrap();
        let n1 = self.a.get_inx_mut_unwrap(p1);
        if n1.p_tree1 == Some(p_d) {
            n1.t.p_tree1 = None;
        } else {
            n1.t.p_tree0 = None;
        }
        // check if we are on the end of the chain to fix the first and last pointers
        if Link::prev(&n1).is_none() {
            self.first = p1;
        }
        if Link::next(&n1).is_none() {
            self.last = p1;
        }

        // all pointers should be fixed, now to fix rank violations

        if n1.t.p_tree0.is_none() && n1.t.p_tree1.is_none() {
            // special casing for invariant 1
            n1.t.rank = 1;
        }

        loop {
            let n1 = self.a.get_inx_unwrap(p1);
            let rank1 = n1.rank;
            let d01 = n1.p_tree1 == p0;
            let p2 = n1.p_back;

            let rank0 = if let Some(p0) = p0 {
                self.a.get_inx_unwrap(p0).rank
            } else {
                0
            };

            let p_s0 = if d01 { n1.p_tree0 } else { n1.p_tree1 };
            if let Some(p_s0) = p_s0 {
                if rank0.wrapping_add(2) >= rank1 {
                    // no violation
                    break
                }
                let s0 = self.a.get_inx_unwrap(p_s0);
                let rank_s0 = s0.rank;

                if rank_s0.wrapping_add(2) == rank1 {
                    // this is not just an optimization, the other branch would require `s0` to have
                    // a rank difference of 1 with `n1`

                    //    n1 (r+3)
                    //    /     \
                    //   /       \
                    // n0 (r)   s0 (r+1)
                    self.a.get_inx_mut_unwrap_t(p1).rank = rank_s0.wrapping_add(1);
                    //    n1 (r+2)
                    //    /     \
                    //   /       \
                    // n0 (r)   s0 (r+1)
                    //

                    if let Some(p2) = p2 {
                        // convey
                        p0 = Some(p1);
                        p1 = p2;
                        continue
                    } else {
                        break
                    }
                }

                //     n1 (r+3)
                //    /       \
                //   /         \
                // n0 (r)     s0 (r+2)

                let (p_a, p_b) = if d01 {
                    (s0.p_tree1, s0.p_tree0)
                } else {
                    (s0.p_tree0, s0.p_tree1)
                };

                let rank_a = if let Some(p_a) = p_a {
                    self.a.get_inx_unwrap(p_a).rank
                } else {
                    0
                };
                let rank_b = if let Some(p_b) = p_b {
                    self.a.get_inx_unwrap(p_b).rank
                } else {
                    0
                };

                if rank_b.wrapping_add(1) == rank_s0 {
                    //     n1 (r+3)
                    //    /      \
                    //   /        \
                    // n0 (r)     s0 (r+2)
                    //           /     \
                    //          /       \
                    //         a (r,r+1) b (r+1)
                    //
                    // n0  n1  a  s0     b
                    //
                    //            s0 (r+3)
                    //           /      \
                    //          /        \
                    //     n1 (r(a)+1)    b (r+1)
                    //    /      \
                    //   /        \
                    // n0 (r)  a (r,r+1)

                    // note that this handles the special case where rank invariant 1 comes into
                    // play

                    //     n1 (3)
                    //    /      \
                    //   /        \
                    // n0 (0)     s0 (2)
                    //           /     \
                    //          /       \
                    //         a (0)     b (1)
                    //
                    // n0  n1  a  s0     b
                    //
                    //            s0 (3)
                    //           /     \
                    //          /       \
                    //     n1 (1)        b (1)

                    if let Some(p_a) = p_a {
                        let a = self.a.get_inx_mut_unwrap_t(p_a);
                        a.p_back = Some(p1);
                    }
                    if d01 {
                        // reverse version
                        let n1 = self.a.get_inx_mut_unwrap_t(p1);
                        n1.p_tree0 = p_a;
                        n1.p_back = Some(p_s0);
                        n1.rank = rank_a.wrapping_add(1);
                        let s0 = self.a.get_inx_mut_unwrap_t(p_s0);
                        s0.p_back = p2;
                        s0.p_tree1 = Some(p1);
                        s0.rank = rank1;
                    } else {
                        let n1 = self.a.get_inx_mut_unwrap_t(p1);
                        n1.p_back = Some(p_s0);
                        n1.p_tree1 = p_a;
                        n1.rank = rank_a.wrapping_add(1);
                        let s0 = self.a.get_inx_mut_unwrap_t(p_s0);
                        s0.p_tree0 = Some(p1);
                        s0.p_back = p2;
                        s0.rank = rank1;
                    }
                    if let Some(p2) = p2 {
                        let n2 = self.a.get_inx_mut_unwrap_t(p2);
                        if n2.p_tree1 == Some(p1) {
                            n2.p_tree1 = Some(p_s0);
                        } else {
                            n2.p_tree0 = Some(p_s0);
                        }
                    } else {
                        self.root = p_s0;
                    }
                    // all invariants resolved
                    break
                }

                //     n1 (r+3)
                //    /      \
                //   /        \
                // n0 (r)     s0 (r+2)
                //           /     \
                //          /       \
                //         a (r,r+1) b (r)

                if rank_a.wrapping_add(2) == rank_s0 {
                    // double demotion

                    //     n1 (r+3)
                    //    /      \
                    //   /        \
                    // n0 (r)     s0 (r+2)
                    //           /     \
                    //          /       \
                    //         a (r)   b (r)
                    self.a.get_inx_mut_unwrap_t(p_s0).rank = rank0.wrapping_add(1);
                    self.a.get_inx_mut_unwrap_t(p1).rank = rank0.wrapping_add(2);
                    //     n1 (r+2)
                    //    /      \
                    //   /        \
                    // n0 (r)     s0 (r+1)
                    //           /     \
                    //          /       \
                    //         a (r)   b (r)

                    // also handles invariant 1

                    if let Some(p2) = p2 {
                        // convey
                        p0 = Some(p1);
                        p1 = p2;
                        continue
                    } else {
                        break
                    }
                }

                //    n1 (r+3)
                //    /      \
                //   /        \
                // n0 (r)      -------s0 (r+2)
                //                   /   \
                //                  /     \
                //            a (r+1)     b (r)
                //           /    \
                //          /      \
                //        c (r-1,r) d(r-1,r)
                //
                // n0 n1  c   a     d s0  b
                //
                //            a (r+3)
                //           /      \
                //          /        \
                //    n1 (r+1)       s0 (r+1)
                //     /    \         /   \
                //    /      \       /     \
                // n0 (r) c (r-1,r) d     b (r-1,r)

                // also handles invariant 1

                let p_a = p_a.unwrap();
                let a = self.a.get_inx_unwrap(p_a);
                let (p_c, p_d) = if d01 {
                    (a.p_tree1, a.p_tree0)
                } else {
                    (a.p_tree0, a.p_tree1)
                };
                if let Some(p_c) = p_c {
                    let c = self.a.get_inx_mut_unwrap_t(p_c);
                    c.p_back = Some(p1);
                }
                if let Some(p_d) = p_d {
                    let d = self.a.get_inx_mut_unwrap_t(p_d);
                    d.p_back = Some(p_s0);
                }
                if d01 {
                    // reverse version
                    let n1 = self.a.get_inx_mut_unwrap_t(p1);
                    n1.p_tree0 = p_c;
                    n1.p_back = Some(p_a);
                    n1.rank = rank_a;
                    let a = self.a.get_inx_mut_unwrap_t(p_a);
                    a.p_tree0 = Some(p_s0);
                    a.p_back = p2;
                    a.p_tree1 = Some(p1);
                    a.rank = rank1;
                    let s0 = self.a.get_inx_mut_unwrap_t(p_s0);
                    s0.p_back = Some(p_a);
                    s0.p_tree1 = p_d;
                    s0.rank = rank_a;
                } else {
                    let n1 = self.a.get_inx_mut_unwrap_t(p1);
                    n1.p_back = Some(p_a);
                    n1.p_tree1 = p_c;
                    n1.rank = rank_a;
                    let a = self.a.get_inx_mut_unwrap_t(p_a);
                    a.p_tree0 = Some(p1);
                    a.p_back = p2;
                    a.p_tree1 = Some(p_s0);
                    a.rank = rank1;
                    let s0 = self.a.get_inx_mut_unwrap_t(p_s0);
                    s0.p_tree0 = p_d;
                    s0.p_back = Some(p_a);
                    s0.rank = rank_a;
                }
                if let Some(p2) = p2 {
                    let n2 = self.a.get_inx_mut_unwrap_t(p2);
                    if n2.p_tree1 == Some(p1) {
                        n2.p_tree1 = Some(p_a);
                    } else {
                        n2.p_tree0 = Some(p_a);
                    }
                } else {
                    self.root = p_a;
                }
                break
            } else {
                // only possible at exterior of the tree with this case

                //    n1 (2)
                //    /
                //   /
                // d (0)
                self.a.get_inx_mut_unwrap_t(p1).rank = 1;
                //    n1 (1)

                if let Some(p2) = p2 {
                    // convey
                    p0 = Some(p1);
                    p1 = p2;
                    continue
                } else {
                    break
                }
            }
        }
        Some((link.t.k, link.t.v))
    }

    /// Replaces the `V` pointed to by `p` with `new`, returns the
    /// old `V`, and keeps the internal generation counter as-is so that
    /// previously constructed `Ptr`s are still valid.
    ///
    /// # Errors
    ///
    /// Returns ownership of `new` instead if `p` is invalid
    pub fn replace_val_and_keep_gen(&mut self, p: P, new: V) -> Result<V, V> {
        if let Some(link) = self.a.get_mut(p) {
            let old = mem::replace(&mut link.t.v, new);
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
        if let Some(p_new) = self.invalidate(p) {
            let old = mem::replace(&mut self.a.get_mut(p_new).unwrap().t.v, new);
            Ok((old, p_new))
        } else {
            Err(new)
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

    /// Has the same properties of [Arena::clone_from_with]
    pub fn clone_from_with<K1: Ord, V1, F: FnMut(P, Link<P, (&K1, &V1)>) -> (K, V)>(
        &mut self,
        source: &OrdArena<P, K1, V1>,
        mut map: F,
    ) {
        self.a.clone_from_with(&source.a, |p, link| {
            let (k, v) = map(p, Link::new(Link::prev_next(link), (&link.k, &link.v)));
            Node {
                k,
                v,
                p_back: link.p_back,
                p_tree0: link.p_tree0,
                p_tree1: link.p_tree1,
                rank: link.rank,
            }
        })
    }

    /// Overwrites `chain_arena` (dropping all preexisting `T`, overwriting the
    /// generation counter, and reusing capacity) with the `Ptr` mapping of
    /// `self`, with the ordering preserved in a single chain (`Link::next`
    /// points to the next greater entry)
    pub fn clone_to_chain_arena<U, F: FnMut(P, Link<P, (&K, &V)>) -> U>(
        &self,
        chain_arena: &mut ChainArena<P, U>,
        mut map: F,
    ) {
        chain_arena.clone_from_with(&self.a, |p, link| {
            map(p, Link::new(Link::prev_next(link), (&link.k, &link.v)))
        })
    }

    /// Overwrites `arena` (dropping all preexisting `T`, overwriting the
    /// generation counter, and reusing capacity) with the `Ptr` mapping of
    /// `self`
    pub fn clone_to_arena<U, F: FnMut(P, Link<P, (&K, &V)>) -> U>(
        &self,
        arena: &mut Arena<P, U>,
        mut map: F,
    ) {
        arena.clone_from_with(&self.a.a, |p, link| {
            map(p, Link::new(Link::prev_next(link), (&link.k, &link.v)))
        });
    }
}

/// Implemented if `K: Clone` and `V: Clone`.
impl<P: Ptr, K: Ord + Clone, V: Clone> Clone for OrdArena<P, K, V> {
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

impl<P: Ptr, K: Ord + Clone, V: Clone> Default for OrdArena<P, K, V> {
    fn default() -> Self {
        Self::new()
    }
}

// TODO
/*impl<P: Ptr, K: Ord + Debug, V: Debug> Debug for OrdArena<P, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}*/

/*
impl<P: Ptr, K: Ord + Clone + alloc::fmt::Debug, V: Clone + alloc::fmt::Debug> OrdArena<P, K, V> {
    pub fn debug_arena(&self) -> Arena<P, (u8, K, V, Option<P>, Option<P>, Option<P>)> {
        let mut res: Arena<P, (u8, K, V, Option<P>, Option<P>, Option<P>)> = Arena::new();
        self.a.clone_to_arena(&mut res, |_, link| {
            (
                link.rank,
                link.k.clone(),
                link.v.clone(),
                link.p_tree0
                    .map(|inx| Ptr::_from_raw(inx, crate::PtrGen::one())),
                link.p_back
                    .map(|inx| Ptr::_from_raw(inx, crate::PtrGen::one())),
                link.p_tree1
                    .map(|inx| Ptr::_from_raw(inx, crate::PtrGen::one())),
            )
        });
        // fix the generations
        let (mut p, mut b) = res.first_ptr();
        loop {
            if b {
                break
            }

            if let Some(ref mut tmp) = res.get_mut(p).unwrap().3 {
                let gen = self
                    .a
                    .get_ignore_gen(tmp.inx())
                    .map(|x| x.0)
                    .unwrap_or(<P::Gen as crate::PtrGen>::one());
                *tmp = Ptr::_from_raw(tmp.inx(), gen);
            }
            if let Some(ref mut tmp) = res.get_mut(p).unwrap().4 {
                let gen = self
                    .a
                    .get_ignore_gen(tmp.inx())
                    .map(|x| x.0)
                    .unwrap_or(<P::Gen as crate::PtrGen>::one());
                *tmp = Ptr::_from_raw(tmp.inx(), gen);
            }
            if let Some(ref mut tmp) = res.get_mut(p).unwrap().5 {
                let gen = self
                    .a
                    .get_ignore_gen(tmp.inx())
                    .map(|x| x.0)
                    .unwrap_or(<P::Gen as crate::PtrGen>::one());
                *tmp = Ptr::_from_raw(tmp.inx(), gen);
            }

            res.next_ptr(&mut p, &mut b);
        }
        res
    }

    pub fn debug(&self) -> alloc::string::String {
        use core::fmt::Write;
        let mut s = alloc::string::String::new();
        writeln!(s, "root: {:?}", self.root).unwrap();
        writeln!(s, "first: {:?}", self.first).unwrap();
        writeln!(s, "last: {:?}", self.last).unwrap();
        let init = Ptr::_from_raw(
            self.first,
            self.a
                .get_ignore_gen(self.first)
                .map(|x| x.0)
                .unwrap_or(<P::Gen as crate::PtrGen>::one()),
        );
        let mut p = init;
        let mut switch = false;
        let mut stop = !self.a.contains(init);
        loop {
            if stop {
                break
            }

            let n = self.a.get(p).unwrap();
            writeln!(
                s,
                "(inx: {:2?}, k: {:3?}, v: {:3?}, rank: {:2?}, p_back: {:2?}, p_tree0: {:2?}, \
                 p_tree1: {:2?})",
                p.inx(),
                n.k,
                n.v,
                n.rank,
                n.p_back,
                n.p_tree0,
                n.p_tree1,
            )
            .unwrap();

            self.a.next_chain_ptr(init, &mut p, &mut switch, &mut stop);
        }
        s
    }
}
*/
