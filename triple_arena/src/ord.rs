use core::{
    cmp::{max, min, Ordering},
    fmt, mem,
};

use crate::{Arena, ChainArena, Link, Ptr, PtrGen, PtrInx};

// The reason why the standard `BTreeMap` uses B-trees has to do with the
// decision of allocating individual nodes. If we have the nodes on a single
// arena, this problem goes away. I settled on implementing a WAVL tree on a
// ChainArena, based on the "Rank-balanced trees" paper by Haeupler, Bernhard;
// Sen, Siddhartha; Tarjan, Robert E. (2015).
// The main difference I have made is that keys and values are stored on all
// nodes of the tree. We keep the balancing property by keeping the invariants:
//
// 0. If a node has zero children, its rank is 0
// 1. If a node has one child, its rank is 1
// 2. If a node has two children, its rank difference from each child can only
//    be 1 or 2.

#[derive(Clone)]
pub(crate) struct Node<P: Ptr, K: Ord, V> {
    k: K,
    v: V,
    // Pointer back to parent. Is invalid if this is the root node as determined by the `root` of
    // the arena
    p_back: Option<P::Inx>,
    p_tree0: Option<P::Inx>,
    p_tree1: Option<P::Inx>,
    // Allows up to a depth of 256, we do not have to worry about overflow.
    // `rank == 0` is a leaf node.
    rank: u8,
}

impl<P: Ptr, K: Ord, V> Node<P, K, V> {
    fn new(k: K, v: V) -> Self {
        Self {
            k,
            v,
            p_back: None,
            p_tree0: None,
            p_tree1: None,
            rank: 0,
        }
    }
}

/// An Ordered Arena with three parameters: a `P: Ptr` type that gives single
/// indirection access to elements, a `K: Ord` key type that is used to define
/// an ordering among elements, and a `V` value type that is not ordered over
/// but is associated with each `K`. `O(log n)` insertions and deletions are
/// guaranteed.
///
/// This is similar to the standard `BTreeMap` but slightly more powerful and
/// more performant because of the arena strategy (the B-tree is stored on an
/// arena and not on individual allocated nodes, and the elements are stored in
/// a chain arena for quick redirections and iteration).
///
/// Note that multiple equal keys are allowed through the `insert_nonhereditary`
/// function.
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
            if node.p_tree0.is_none() && node.p_tree1.is_none() {
                if node.rank != 0 {
                    return Err("leaf is not rank 0")
                }
            } else if node.p_tree0.is_none() || node.p_tree1.is_none() {
                // this along with the rank difference limit enforces that the tree must be
                // balanced
                if node.rank != 1 {
                    return Err("node before external edge has rank not equal to 1")
                }
            }
            if let Some(p_back) = node.p_back {
                let rank0 = node.rank;
                let parent = this.a.get_ignore_gen(p_back).unwrap().1;
                let rank1 = parent.rank;
                if rank0 >= rank1 {
                    return Err("rank difference is zero or negative")
                }
                let rank_diff = rank1.wrapping_sub(rank0);
                if rank_diff > 2 {
                    return Err("rank difference is greater than 2")
                }
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
    /// key-value elements in the arena.
    pub fn len(&self) -> usize {
        self.a.len()
    }

    /// Returns if the arena is empty
    pub fn is_empty(&self) -> bool {
        self.a.is_empty()
    }

    /// Returns the element capacity of the arena
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

    pub fn clear(&mut self) {
        self.a.clear();
    }

    pub fn clear_and_shrink(&mut self) {
        self.a.clear_and_shrink();
    }

    /// Inserts at a leaf and manages ordering and replacement. Returns `Ok` if
    /// there is a new insertion, which may need to be rebalanced. Returns
    /// `Err` if there was a replacement (which does not happen with the
    /// nonhereditary case).
    pub fn raw_insert(&mut self, k: K, v: V, nonhereditary: bool) -> Result<P, (K, V)> {
        if self.a.is_empty() {
            let p_new = self.a.insert_new(Node::new(k, v));
            self.first = p_new.inx();
            self.last = p_new.inx();
            self.root = p_new.inx();
            return Ok(p_new)
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
                        let mut new_node = Node::new(k, v);
                        new_node.p_back = Some(p);
                        if let Ok(p_new) = self.a.insert((None, Some(p_with_gen)), new_node) {
                            // fix tree pointer in leaf direction
                            self.a.get_ignore_gen_mut(p).unwrap().1.p_tree0 = Some(p_new.inx());
                            if self.first == p {
                                self.first = p_new.inx()
                            }
                            break Ok(p_new)
                        } else {
                            unreachable!()
                        }
                    }
                }
                // supporting multiple equal keys
                // TODO conditional, we would want to keep old key but replace and return old value
                Ordering::Equal => {
                    if nonhereditary {
                        // need to get to leaves, use `p_tree0` bias
                        if let Some(p_tree0) = node.p_tree0 {
                            p = p_tree0
                        } else if let Some(p_tree1) = node.p_tree1 {
                            p = p_tree1
                        } else {
                            // go the Ordering::Less route
                            let mut new_node = Node::new(k, v);
                            new_node.p_back = Some(p);
                            if let Ok(p_new) = self.a.insert((None, Some(p_with_gen)), new_node) {
                                self.a.get_ignore_gen_mut(p).unwrap().1.p_tree0 = Some(p_new.inx());
                                if self.first == p {
                                    self.first = p_new.inx()
                                }
                                break Ok(p_new)
                            } else {
                                unreachable!()
                            }
                        }
                    } else {
                        let old_v = mem::replace(&mut self.a.get_mut(p_with_gen).unwrap().v, v);
                        return Err((k, old_v))
                    }
                }
                Ordering::Greater => {
                    if let Some(p_tree1) = node.p_tree1 {
                        p = p_tree1
                    } else {
                        let mut new_node = Node::new(k, v);
                        new_node.p_back = Some(p);
                        if let Ok(p_new) = self.a.insert((Some(p_with_gen), None), new_node) {
                            self.a.get_ignore_gen_mut(p).unwrap().1.p_tree1 = Some(p_new.inx());
                            if self.last == p {
                                self.last = p_new.inx()
                            }
                            break Ok(p_new)
                        } else {
                            unreachable!()
                        }
                    }
                }
            }
        }
    }

    // Rebalances starting from newly inserted node `p`
    fn rebalance_inserted(&mut self, p: P::Inx) {
        // We keep record of the last three nodes for trinode restructuring.
        // We also keep the direction of the two edges between the nodes in
        // order to know exactly what trinode restructuring to choose
        let mut p0 = p;
        let n0 = self.a.get_inx_unwrap(p0);
        let (n1, mut p1) = if let Some(p1) = n0.p_back {
            // Must promote so we maintain a loop invariant that n0 and n1 do not violate
            // rank invariants. If there is a sibling then it must have rank 0 and thus we
            // can unconditionally do this
            self.a.get_inx_mut_unwrap_t(p1).rank = 1;
            (self.a.get_inx_unwrap(p1), p1)
        } else {
            // single node tree, inserted node was inserted as rank 0 which is immediately
            // correct
            return
        };
        let mut d01 = n1.p_tree1 == Some(p0);
        let (n2, mut p2) = if let Some(p2) = n1.p_back {
            (self.a.get_inx_unwrap(p2), p2)
        } else {
            // height 2 tree, rank has already been set to 1
            return
        };
        let mut d12 = n2.p_tree1 == Some(p1);
        loop {
            let n0 = self.a.get_inx_unwrap(p0);
            let n1 = self.a.get_inx_unwrap(p1);
            let n2 = self.a.get_inx_unwrap(p2);
            let p3 = n2.p_back;

            let rank1 = n1.rank;
            let rank2 = n2.rank;
            if rank1 != rank2 {
                // n2 was previously two ranks over n1, so when n1 was promoted in the prelude
                // or a previous loop, it did not introduce another rank violation
                break
            } else {
                // Check the sibling of n1 to see if we can promote n2 and avoid a restructure.
                // This isn't just an optimization, a general case restructure requires the
                // sibling of n1 to be 2 ranks below n2 or else the restructure may introduce
                // lower height violations.
                let p_sibling1 = if d12 { n2.p_tree0 } else { n2.p_tree1 };
                if let Some(p_sibling1) = p_sibling1 {
                    if self.a.get_inx_unwrap(p_sibling1).rank.wrapping_add(1) == rank2 {
                        self.a.get_inx_mut_unwrap_t(p2).rank = rank1.wrapping_add(1);
                        if let Some(p3) = p3 {
                            // convey up the tree
                            p0 = p1;
                            p1 = p2;
                            p2 = p3;
                            d01 = d12;
                            d12 = self.a.get_inx_unwrap(p2).p_tree1 == Some(p1);
                            continue
                        } else {
                            // n2 was the root
                            break
                        }
                    }
                }

                // Need a trinode restructure, and the sibling of n1 is two ranks below n2 so
                // there is space. There are 4 combinations of `d01` and `d12` that
                // we need to handle, which deal with 7 nodes

                // some pointer resets could be avoided with higher level branching, but I think
                // that having a single code path with as few conditionals as possible is better
                let t: (
                    Option<P::Inx>,
                    P::Inx,
                    Option<P::Inx>,
                    P::Inx,
                    Option<P::Inx>,
                    P::Inx,
                    Option<P::Inx>,
                ) = match (d12, d01) {
                    (false, false) => (n0.p_tree0, p0, n0.p_tree1, p1, n1.p_tree1, p2, n2.p_tree1),
                    (false, true) => (n1.p_tree0, p1, n0.p_tree0, p0, n0.p_tree1, p2, n2.p_tree1),
                    (true, false) => (n2.p_tree0, p2, n0.p_tree0, p0, n0.p_tree1, p1, n1.p_tree1),
                    (true, true) => (n2.p_tree0, p2, n1.p_tree0, p1, n0.p_tree0, p0, n0.p_tree1),
                };
                // calculate ranks and fix external pointers
                if let Some(p) = p3 {
                    let ext = self.a.get_inx_mut_unwrap_t(p);
                    if ext.p_tree1 == Some(p2) {
                        ext.p_tree1 = Some(t.3);
                    } else {
                        ext.p_tree0 = Some(t.3);
                    }
                }
                let mut rank_x0 = 0;
                if let Some(p) = t.0 {
                    let ext = self.a.get_inx_mut_unwrap_t(p);
                    rank_x0 = ext.rank.wrapping_add(1);
                    ext.p_back = Some(t.1);
                }
                if let Some(p) = t.2 {
                    let ext = self.a.get_inx_mut_unwrap_t(p);
                    rank_x0 = max(rank_x0, ext.rank.wrapping_add(1));
                    ext.p_back = Some(t.1);
                }
                let mut rank_x1 = 0;
                if let Some(p) = t.4 {
                    let ext = self.a.get_inx_mut_unwrap_t(p);
                    rank_x1 = ext.rank.wrapping_add(1);
                    ext.p_back = Some(t.5);
                }
                if let Some(p) = t.6 {
                    let ext = self.a.get_inx_mut_unwrap_t(p);
                    rank_x1 = max(rank_x1, ext.rank.wrapping_add(1));
                    ext.p_back = Some(t.5);
                }
                // restructure
                let x0 = self.a.get_inx_mut_unwrap_t(t.1);
                x0.p_tree0 = t.0;
                x0.p_back = Some(t.3);
                x0.p_tree1 = t.2;
                x0.rank = rank_x0;
                let x1 = self.a.get_inx_mut_unwrap_t(t.3);
                x1.p_tree0 = Some(t.1);
                x1.p_back = p3;
                x1.p_tree1 = Some(t.5);
                x1.rank = max(rank_x0, rank_x1).wrapping_add(1);
                let x2 = self.a.get_inx_mut_unwrap_t(t.5);
                x2.p_tree0 = t.4;
                x2.p_back = Some(t.3);
                x2.p_tree1 = t.6;
                x2.rank = rank_x1;

                if let Some(p3) = p3 {
                    // orient around minimum rank side
                    if rank_x0 <= rank_x1 {
                        p0 = t.1;
                        p1 = t.3;
                        p2 = p3;
                        d01 = false;
                        d12 = self.a.get_inx_unwrap(p2).p_tree1 == Some(p1);
                    } else {
                        p0 = t.5;
                        p1 = t.3;
                        p2 = p3;
                        d01 = true;
                        d12 = self.a.get_inx_unwrap(p2).p_tree1 == Some(p1);
                    }
                } else {
                    // we have reached the root
                    self.root = t.3;
                    break
                }
            }
        }
    }

    /// Inserts key `k` and an associated value `v` into `self` and returns a
    /// `Ptr` to it. If the inserted key is equal to one or more keys already
    /// contained in `self`, the inserted key is inserted in a `Link::prev`
    /// position to all the equal keys. Future calls to `self.find_key` with an
    /// equal `k` could find any of the equal keys.
    pub fn insert_nonhereditary(&mut self, k: K, v: V) -> P {
        let p = match self.raw_insert(k, v, true) {
            Ok(p) => p,
            Err(_) => unreachable!(),
        };
        self.rebalance_inserted(p.inx());
        p
    }

    // Uses linear comparisons starting at `p` in order to insert `k` and `v`. If
    // `p` is not a small constant number of elements away from where `k` should be
    // ordered, this function may operate in `O(n)` time instead of the `O(1)` this
    // is intended for. pub fn insert_similar(&mut self, p: P, k: K, v: V) -> P
    // {} pub fn insert_similar_nonhereditary(&mut self, p: P, k: K, v: V) -> P
    // {}

    //pub fn replace_val(&mut self, p: P, v: V)

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

    /// Finds a `Ptr`
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

    // Finds an equal key to `k`, or if there is none then it attempts to find the
    // least key that is greater than `k`. Only one binary search is used internally
    // (but if you already have a `Ptr` to the key, use `get_link` to find it
    // instead). Returns `None` if there are no keys greater than `k`.
    // pub fn find_key_or_supremum(&self, k: &K) -> Option<P>
    // Finds an equal key to `k`, or if there is none then it attempts to find the
    // greatest key that is less than `k`. Only one binary search is used internally
    // (but if you already have a `Ptr` to the key, use `get_link` to find it
    // instead). Returns `None` if there are no keys lesser than `k`.
    // pub fn find_key_or_infinum(&self, k: &K) -> Option<P>
    // Attempts to find `k`, or if it cannot find `k` then it finds a "similar" key
    // which could be the supremum or infinum to `k`.  Only one binary search is
    // used internally. Only returns `None` if `self.is_empty()`.
    // pub fn find_key_or_similar(&self, k: &K) -> Option<P>

    /// Returns if `p` is a valid `Ptr`
    pub fn contains(&self, p: P) -> bool {
        self.a.contains(p)
    }

    /// Returns the full `Link<P, (&K, &V)>`. Using [Link::prev] on the result
    /// gives the `Ptr` to the next lesser key, and using [Link::next] gives the
    /// `Ptr` to the next greater element.
    #[must_use]
    pub fn get_link(&self, p: P) -> Option<Link<P, (&K, &V)>> {
        self.a
            .get(p)
            .map(|link| Link::new(Link::prev_next(link), (&link.k, &link.v)))
    }

    #[must_use]
    pub fn get(&self, p: P) -> Option<(&K, &V)> {
        self.a.get(p).map(|link| (&link.k, &link.v))
    }

    #[must_use]
    pub fn get_key(&self, p: P) -> Option<&K> {
        self.a.get(p).map(|link| &link.k)
    }

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

    #[must_use]
    pub fn remove(&mut self, p: P) -> Option<(K, V)> {
        let link = self.a.remove(p)?;
        let p = p.inx();
        if self.a.is_empty() {
            return Some((link.t.k, link.t.v))
        }
        if Link::prev(&link).is_none() {
            self.first = Link::next(&link).unwrap().inx();
        } else if Link::next(&link).is_none() {
            self.last = Link::prev(&link).unwrap().inx();
        }

        // handle interior nodes
        let (old_back, old_tree0, old_tree1, old_rank, p_replace) = if link.rank > 1 {
            // when removing an interior node of the tree, its place in the tree is
            // replaced by a similar node which must be either be a rank 1 or 0
            // node, we later have to handle the rebalancing from the shifted removal point
            // on the leaves
            let p_replace = if let Some(prev) = Link::prev(&link) {
                prev.inx()
            } else {
                Link::next(&link).unwrap().inx()
            };
            let x = self.a.get_inx_mut_unwrap_t(p_replace);
            let old = (x.p_back, x.p_tree0, x.p_tree1, x.rank, p_replace);
            let (p_back, p_tree0, p_tree1) = (link.p_back, link.p_tree0, link.p_tree1);
            x.p_back = p_back;
            x.p_tree0 = p_tree0;
            x.p_tree1 = p_tree1;
            x.rank = link.rank;
            if let Some(p_back) = p_back {
                let n = self.a.get_inx_mut_unwrap_t(p_back);
                if n.p_tree0 == Some(p) {
                    n.p_tree0 = Some(p_replace);
                } else {
                    n.p_tree1 = Some(p_replace);
                }
            } else {
                self.root = p_replace;
            }
            if let Some(p_tree0) = p_tree0 {
                self.a.get_inx_mut_unwrap_t(p_tree0).p_back = Some(p_replace);
            }
            if let Some(p_tree1) = p_tree1 {
                self.a.get_inx_mut_unwrap_t(p_tree1).p_back = Some(p_replace);
            }
            old
        } else {
            if link.p_back.is_none() {
                // must have been a two or three node tree, go ahead and special case
                // restructure
                if let Some(next) = Link::next(&link) {
                    let next = next.inx();
                    let x = self.a.get_inx_mut_unwrap_t(next);
                    x.p_tree1 = None;
                    x.p_back = None;
                    self.root = next;
                    self.last = next;
                    if let Some(prev) = Link::prev(&link) {
                        let prev = prev.inx();
                        x.p_tree0 = Some(prev);
                        x.rank = 1;
                        let y = self.a.get_inx_mut_unwrap_t(prev);
                        y.p_tree0 = None;
                        y.p_tree1 = None;
                        y.p_back = Some(next);
                        y.rank = 0;
                        self.first = prev;
                    } else {
                        x.p_tree0 = None;
                        x.rank = 0;
                        self.first = next;
                    }
                } else if let Some(prev) = Link::prev(&link) {
                    let prev = prev.inx();
                    let x = self.a.get_inx_mut_unwrap_t(prev);
                    x.p_tree0 = None;
                    x.p_tree1 = None;
                    x.p_back = None;
                    x.rank = 0;
                    self.root = prev;
                    self.first = prev;
                    self.last = prev;
                }
                return Some((link.t.k, link.t.v))
            }
            (link.p_back, link.p_tree0, link.p_tree1, link.rank, p)
        };

        // handle the links around the removed or displaced exterior node
        let (mut p0, mut p1) = if old_rank == 1 {
            // if the old removed tree position was rank 1, there is one rank 0 child that
            // needs to be reconnected
            let child = if let Some(p_tree0) = old_tree0 {
                self.a.get_inx_mut_unwrap_t(p_tree0).p_back = old_back;
                p_tree0
            } else {
                let p_tree1 = old_tree1.unwrap();
                self.a.get_inx_mut_unwrap_t(p_tree1).p_back = old_back;
                p_tree1
            };
            if let Some(p_back) = old_back {
                let x = self.a.get_inx_mut_unwrap_t(p_back);
                if x.p_tree0 == Some(p_replace) {
                    x.p_tree0 = Some(child);
                } else {
                    x.p_tree1 = Some(child);
                }
            }
            (child, old_back.unwrap())
        } else {
            // removed a rank 0, check if an interior node has been exposed
            let p1 = old_back.unwrap();
            let n1 = self.a.get_inx_mut_unwrap_t(p1);
            let p2 = n1.p_back;

            let d01 = n1.p_tree1 == Some(p_replace);
            if d01 {
                n1.p_tree1 = None;
            } else {
                n1.p_tree0 = None;
            }
            let p_s0 = if d01 { n1.p_tree0 } else { n1.p_tree1 };
            if n1.rank == 1 {
                if p_s0.is_none() {
                    // need to demote a rank 1 to rank 0
                    n1.rank = 0;
                }
                if let Some(p2) = p2 {
                    (p1, p2)
                } else {
                    return Some((link.t.k, link.t.v))
                }
            } else {
                // If a rank 2 node is exposed to the exterior then we must perform a special
                // case restructure since the loop is expecting rank differences of 3.

                // Because it is rank 2, there must be a sibling of rank 1.
                let p_s0 = p_s0.unwrap();
                let s0 = self.a.get_inx_unwrap(p_s0);
                let p_a = if d01 { s0.p_tree1 } else { s0.p_tree0 };
                if let Some(p_a) = p_a {
                    let n1 = self.a.get_inx_mut_unwrap_t(p1);
                    n1.rank = 0;
                    n1.p_back = Some(p_a);
                    if d01 {
                        n1.p_tree0 = None;
                    } else {
                        n1.p_tree1 = None;
                    }
                    let a = self.a.get_inx_mut_unwrap_t(p_a);
                    a.rank = 2;
                    a.p_back = p2;
                    if p2.is_none() {
                        self.root = p_a;
                    }
                    if d01 {
                        a.p_tree0 = Some(p_s0);
                        a.p_tree1 = Some(p1);
                    } else {
                        a.p_tree0 = Some(p1);
                        a.p_tree1 = Some(p_s0);
                    }
                    let s0 = self.a.get_inx_mut_unwrap_t(p_s0);
                    s0.p_back = Some(p_a);
                    if d01 {
                        s0.p_tree1 = None;
                    } else {
                        s0.p_tree0 = None;
                    }
                } else {
                    // must be at least one rank 0 node in the subtree
                    let p_b = s0.p_tree1.unwrap();
                    let n1 = self.a.get_inx_mut_unwrap_t(p1);
                    n1.rank = 0;
                    n1.p_back = Some(p_s0);
                    if d01 {
                        n1.p_tree0 = None;
                    } else {
                        n1.p_tree1 = None;
                    }
                    let s0 = self.a.get_inx_mut_unwrap_t(p_s0);
                    s0.p_back = p2;
                    if p2.is_none() {
                        self.root = p_s0;
                    }
                    if d01 {
                        s0.p_tree0 = Some(p1);
                    } else {
                        s0.p_tree1 = Some(p_b);
                    }
                    let b = self.a.get_inx_mut_unwrap_t(p_b);
                    b.p_back = Some(p_s0);
                }
                return Some((link.t.k, link.t.v))
            }
        };

        let mut d01 = self.a.get_inx_unwrap(p1).p_tree1 == Some(p0);
        loop {
            let n0 = self.a.get_inx_unwrap(p0);
            let n1 = self.a.get_inx_unwrap(p1);
            let p2 = n1.p_back;

            // For removal rebalancing, we want to either demote `n1` by a single rank (we
            // do not want to demote more than we have to, otherwise more than 2
            // restructures may be needed), or we do a restructure that can preserve the
            // rank of `n1`.

            // We may have to look at the sibling of `n0` which we will denote `s0`, the
            // children of `s0` which are `a` and `b` (of which `a` is in the middle), and
            // the children of `a` which are `c` and `d`
            let rank0 = n0.rank;
            let rank1 = n1.rank;
            if rank0.wrapping_add(2) < rank1 {
                // check sibling to see if we can demote n1
                let p_s0 = if d01 { n1.p_tree0 } else { n1.p_tree1 };
                let p_s0 = p_s0.unwrap();
                let s0 = self.a.get_inx_unwrap(p_s0);
                let rank_s0 = s0.rank;
                if rank_s0.wrapping_add(2) == rank1 {
                    // demote `n1`
                    self.a.get_inx_mut_unwrap_t(p1).rank = rank0.wrapping_add(2);
                    if let Some(p2) = p2 {
                        // convey up the tree
                        p0 = p1;
                        p1 = p2;
                        d01 = self.a.get_inx_unwrap(p1).p_tree1 == Some(p0);
                        continue
                    } else {
                        break
                    }
                }
                // Check children of `s0` to see if we can demote `n1` and `s0` at the same time
                // and prevent a rebalance.
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
                if max(rank_a, rank_b).wrapping_add(1) < rank_s0 {
                    // demote `n1` and `s0`
                    self.a.get_inx_mut_unwrap_t(p_s0).rank = rank0.wrapping_add(1);
                    self.a.get_inx_mut_unwrap_t(p1).rank = rank0.wrapping_add(2);
                    if let Some(p2) = p2 {
                        // convey up the tree
                        p0 = p1;
                        p1 = p2;
                        d01 = self.a.get_inx_unwrap(p1).p_tree1 == Some(p0);
                        continue
                    } else {
                        break
                    }
                }
                // If `b` has a high enough rank we can do a 6 edge restructure
                if rank_b.wrapping_add(1) == rank_s0 {
                    let n1 = self.a.get_inx_mut_unwrap_t(p1);
                    n1.rank = rank0.wrapping_add(2);
                    n1.p_back = Some(p_s0);
                    if d01 {
                        n1.p_tree0 = p_a;
                    } else {
                        n1.p_tree1 = p_a;
                    }
                    if let Some(p_a) = p_a {
                        let a = self.a.get_inx_mut_unwrap_t(p_a);
                        a.p_back = Some(p1);
                    }
                    let s0 = self.a.get_inx_mut_unwrap_t(p_s0);
                    s0.rank = rank0.wrapping_add(3);
                    s0.p_back = p2;
                    if d01 {
                        s0.p_tree0 = p_b;
                        s0.p_tree1 = Some(p1);
                    } else {
                        s0.p_tree0 = Some(p1);
                        s0.p_tree1 = p_b;
                    }
                    // we can break since the rank of `a` is equal to the replaced `n1`
                    break
                }
                // else we need a 8 edge restructure, using the children of a0 which we will
                // call `b0` and `b1`
                let p_a = p_a.unwrap();
                let a = self.a.get_inx_unwrap(p_a);
                let p_c = a.p_tree0;
                let p_d = a.p_tree1;
                let n1 = self.a.get_inx_mut_unwrap_t(p1);
                n1.rank = rank0.wrapping_add(1);
                n1.p_back = Some(p_s0);
                if d01 {
                    n1.p_tree0 = p_c;
                } else {
                    n1.p_tree1 = p_c;
                }
                if let Some(p_c) = p_c {
                    self.a.get_inx_mut_unwrap_t(p_c).p_back = Some(p1);
                }
                let a = self.a.get_inx_mut_unwrap_t(p_a);
                a.rank = rank0.wrapping_add(3);
                a.p_back = p2;
                if d01 {
                    a.p_tree0 = Some(p_s0);
                    a.p_tree1 = Some(p1);
                } else {
                    a.p_tree0 = Some(p1);
                    a.p_tree1 = Some(p_s0);
                }
                if let Some(p_d) = p_d {
                    self.a.get_inx_mut_unwrap_t(p_d).p_back = Some(p1);
                }
                let s0 = self.a.get_inx_mut_unwrap_t(p_s0);
                s0.rank = rank0.wrapping_add(1);
                s0.p_back = Some(p_a);
                if d01 {
                    s0.p_tree0 = p_b;
                    s0.p_tree1 = p_d;
                } else {
                    s0.p_tree0 = p_d;
                    s0.p_tree1 = p_b;
                }
                if let Some(p_b) = p_b {
                    self.a.get_inx_mut_unwrap_t(p_b).p_back = Some(p_s0);
                }
                break
            } else {
                break
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
    pub fn replace_and_keep_gen(&mut self, p: P, new: V) -> Result<V, V> {
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
    pub fn replace_and_update_gen(&mut self, p: P, new: V) -> Result<(V, P), V> {
        if let Some(p_new) = self.invalidate(p) {
            let old = mem::replace(&mut self.a.get_mut(p_new).unwrap().t.v, new);
            Ok((old, p_new))
        } else {
            Err(new)
        }
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
            map(p, Link::new(Link::prev_next(&link), (&link.k, &link.v)))
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

impl<P: Ptr, K: Ord + Clone + fmt::Debug, V: Clone + fmt::Debug> OrdArena<P, K, V> {
    pub fn debug_arena(&self) -> Arena<P, (u8, K, V, Option<P>, Option<P>, Option<P>)> {
        let mut res: Arena<P, (u8, K, V, Option<P>, Option<P>, Option<P>)> = Arena::new();
        self.a.clone_to_arena(&mut res, |p, link| {
            (
                link.rank,
                link.k.clone(),
                link.v.clone(),
                link.p_tree0.map(|inx| Ptr::_from_raw(inx, PtrGen::one())),
                link.p_back.map(|inx| Ptr::_from_raw(inx, PtrGen::one())),
                link.p_tree1.map(|inx| Ptr::_from_raw(inx, PtrGen::one())),
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
                    .unwrap_or(P::Gen::one());
                *tmp = Ptr::_from_raw(tmp.inx(), gen);
            }
            if let Some(ref mut tmp) = res.get_mut(p).unwrap().4 {
                let gen = self
                    .a
                    .get_ignore_gen(tmp.inx())
                    .map(|x| x.0)
                    .unwrap_or(P::Gen::one());
                *tmp = Ptr::_from_raw(tmp.inx(), gen);
            }
            if let Some(ref mut tmp) = res.get_mut(p).unwrap().5 {
                let gen = self
                    .a
                    .get_ignore_gen(tmp.inx())
                    .map(|x| x.0)
                    .unwrap_or(P::Gen::one());
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
                .unwrap_or(P::Gen::one()),
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
