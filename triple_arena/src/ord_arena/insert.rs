#![allow(clippy::type_complexity)]

use core::{cmp::Ordering, mem};

use super::ord::Node;
use crate::{OrdArena, Ptr};

impl<P: Ptr, K: Ord, V> OrdArena<P, K, V> {
    /// Inserts at a leaf and manages ordering and replacement. Returns `Ok` if
    /// there is a new insertion, which will need to be rebalanced. Returns
    /// `Err` if there was a replacement (which does not happen with the
    /// nonhereditary case).
    fn raw_insert(&mut self, k_v: (K, V), nonhereditary: bool) -> (P, Option<(K, V)>) {
        if self.a.is_empty() {
            let p_new = self.a.insert_new(Node {
                k_v,
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
            let p_with_gen = crate::Ptr::_from_raw(p, gen);
            match Ord::cmp(&k_v.0, &node.k_v.0) {
                Ordering::Less => {
                    if let Some(p_tree0) = node.p_tree0 {
                        p = p_tree0
                    } else {
                        // insert new leaf
                        let new_node = Node {
                            k_v,
                            p_back: Some(p),
                            p_tree0: None,
                            p_tree1: None,
                            rank: 1,
                        };
                        if let Ok(p_new) = self.a.insert((None, Some(p_with_gen)), new_node) {
                            // fix tree pointer in leaf direction
                            self.a.get_ignore_gen_mut(p).unwrap().1.t.p_tree0 = Some(p_new.inx());
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
                                k_v,
                                p_back: Some(p),
                                p_tree0: None,
                                p_tree1: None,
                                rank: 1,
                            };
                            if let Ok(p_new) = self.a.insert((None, Some(p_with_gen)), new_node) {
                                self.a.get_ignore_gen_mut(p).unwrap().1.t.p_tree0 =
                                    Some(p_new.inx());
                                if self.first == p {
                                    self.first = p_new.inx()
                                }
                                break (p_new, None)
                            } else {
                                unreachable!()
                            }
                        }
                    } else {
                        let old_v =
                            mem::replace(&mut self.a.get_mut(p_with_gen).unwrap().k_v.1, k_v.1);
                        return (p_with_gen, Some((k_v.0, old_v)))
                    }
                }
                Ordering::Greater => {
                    if let Some(p_tree1) = node.p_tree1 {
                        p = p_tree1
                    } else {
                        let new_node = Node {
                            k_v,
                            p_back: Some(p),
                            p_tree0: None,
                            p_tree1: None,
                            rank: 1,
                        };
                        if let Ok(p_new) = self.a.insert((Some(p_with_gen), None), new_node) {
                            self.a.get_ignore_gen_mut(p).unwrap().1.t.p_tree1 = Some(p_new.inx());
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
        k_v: (K, V),
        nonhereditary: bool,
    ) -> Result<(P, Option<(K, V)>), (K, V)> {
        if let Some(p_init) = p_init {
            if !self.a.contains(p_init) {
                return Err(k_v)
            }
            let mut p = p_init.inx();
            // detects if we would switch probing directions, note that even if `Ord` is
            // rigged to do nontransitive things it will still not result in an infinite
            // loop
            let mut direction = None;
            let direction = loop {
                let link = self.a.get_inx_unwrap(p);
                match Ord::cmp(&k_v.0, &link.t.k_v.0) {
                    Ordering::Less => {
                        if direction == Some(true) {
                            break Ordering::Less
                        }
                        direction = Some(false);
                        if let Some(prev) = link.prev() {
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
                        if let Some(next) = link.next() {
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
                    if link.t.p_tree0.is_some() {
                        p = link.prev().unwrap().inx();
                        Ordering::Greater
                    } else {
                        Ordering::Less
                    }
                }
                Ordering::Equal => {
                    if nonhereditary {
                        if link.t.p_tree0.is_some() {
                            p = link.prev().unwrap().inx();
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
                    if link.t.p_tree1.is_some() {
                        p = link.next().unwrap().inx();
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
                        k_v,
                        p_back: Some(p),
                        p_tree0: None,
                        p_tree1: None,
                        rank: 1,
                    };
                    if let Ok(p_new) = self.a.insert((None, Some(p_with_gen)), new_node) {
                        // fix tree pointer in leaf direction
                        self.a.get_ignore_gen_mut(p).unwrap().1.t.p_tree0 = Some(p_new.inx());
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
                        let old_v =
                            mem::replace(&mut self.a.get_mut(p_with_gen).unwrap().k_v.1, k_v.1);
                        Ok((p_with_gen, Some((k_v.0, old_v))))
                    }
                }
                Ordering::Greater => {
                    let new_node = Node {
                        k_v,
                        p_back: Some(p),
                        p_tree0: None,
                        p_tree1: None,
                        rank: 1,
                    };
                    if let Ok(p_new) = self.a.insert((Some(p_with_gen), None), new_node) {
                        self.a.get_ignore_gen_mut(p).unwrap().1.t.p_tree1 = Some(p_new.inx());
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
                k_v,
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
            return Err(k_v)
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

        let (n1, mut p1) = if let Some(p1) = n0.t.p_back {
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
        let mut d01 = n1.t.p_tree1 == Some(p0);
        let (n2, mut p2) = if let Some(p2) = n1.t.p_back {
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
        let mut d12 = n2.t.p_tree1 == Some(p1);
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
            let p3 = n2.t.p_back;

            let rank0 = n0.t.rank;
            let rank1 = n1.t.rank;
            let rank2 = n2.t.rank;
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
            let p_s1 = if d12 { n2.t.p_tree0 } else { n2.t.p_tree1 };
            let rank_s1 = if let Some(p_s1) = p_s1 {
                self.a.get_inx_unwrap(p_s1).t.rank
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
                    d12 = self.a.get_inx_unwrap(p2).t.p_tree1 == Some(p1);
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

                let p_s0 = if d01 { n1.t.p_tree0 } else { n1.t.p_tree1 };
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
                    (n0.t.p_tree1, n0.t.p_tree0)
                } else {
                    (n0.t.p_tree0, n0.t.p_tree1)
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

    /// Inserts key-value pair `k_v` into `self` and returns a `Ptr` to it. If
    /// the inserted key is equal to a key already contained in `self`, the
    /// new value replaces the old value, and `k_v.0` and the old value
    /// are returned. The existing key is not replaced, which should not make a
    /// difference unless special `Ord` definitions are being used.
    #[must_use]
    pub fn insert(&mut self, k_v: (K, V)) -> (P, Option<(K, V)>) {
        let (p, k_v) = self.raw_insert(k_v, false);
        if k_v.is_none() {
            self.rebalance_inserted(p.inx());
        }
        (p, k_v)
    }

    /// Inserts key-value pair `k_v` into `self` and returns a
    /// `Ptr` to it. If the inserted key is equal to a key already contained in
    /// `self`, the inserted key is inserted in a [prev](crate::Link::prev)
    /// position to all the equal keys. Future calls to `self.find_key` with
    /// an equal `k_v.0` could find any of the equal keys.
    pub fn insert_nonhereditary(&mut self, k_v: (K, V)) -> P {
        let (p, _) = self.raw_insert(k_v, true);
        self.rebalance_inserted(p.inx());
        p
    }

    /// Uses linear comparisons starting at `p_init` in order to insert
    /// key-value pair `k_v`. If `p_init` is not within a small constant number
    /// of elements away from where the key should be ordered, this function
    /// may operate in `O(n)` time instead of the `O(1)` this is intended
    /// for. If the inserted key is equal to a key already contained in
    /// `self`, the new value replaces the old value, and `k` and the old
    /// value are returned. If `self.is_empty()`, `p_init` should be `None`,
    /// otherwise there will be an error. Returns an `Err` if `p_init` is
    /// invalid or if it is `None` and `!self.is_empty()`.
    pub fn insert_linear(
        &mut self,
        p_init: Option<P>,
        k_v: (K, V),
    ) -> Result<(P, Option<(K, V)>), (K, V)> {
        match self.raw_insert_linear(p_init, k_v, false) {
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
        k_v: (K, V),
    ) -> Result<P, (K, V)> {
        match self.raw_insert_linear(p_init, k_v, true) {
            Ok((p, _)) => {
                self.rebalance_inserted(p.inx());
                Ok(p)
            }
            Err(k_v) => Err(k_v),
        }
    }
}
