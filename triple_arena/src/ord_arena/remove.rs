use crate::{Link, OrdArena, Ptr};

impl<P: Ptr, K, V> OrdArena<P, K, V> {
    /// Removes the key-value link at `p`. Returns `None` if `p` is invalid.
    #[must_use]
    pub fn remove(&mut self, p: P) -> Option<Link<P, (K, V)>> {
        let link = self.a.remove(p)?;
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
            link.t.p_tree0,
            link.t.p_tree1,
            link.t.p_back,
            link.t.rank,
            link.prev(),
            link.next(),
        );
        let res = Some(Link::new(link.prev_next(), link.t.k_v));
        if self.a.is_empty() {
            // last node to be removed, our invariants require that `self.a.is_empty` be
            // checked to determine whether or not `self.first`, etc are valid.
            return res
        }
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
                    r.t.p_tree0,
                    r.t.p_tree1,
                    r.t.p_back,
                    r.t.rank,
                    r.prev(),
                    r.next(),
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
        if n1.t.p_tree1 == Some(p_d) {
            n1.t.p_tree1 = None;
        } else {
            n1.t.p_tree0 = None;
        }
        // check if we are on the end of the chain to fix the first and last pointers
        if n1.prev().is_none() {
            self.first = p1;
        }
        if n1.next().is_none() {
            self.last = p1;
        }

        // all pointers should be fixed, now to fix rank violations

        if n1.t.p_tree0.is_none() && n1.t.p_tree1.is_none() {
            // special casing for invariant 1
            n1.t.rank = 1;
        }

        loop {
            let n1 = self.a.get_inx_unwrap(p1);
            let rank1 = n1.t.rank;
            let d01 = n1.t.p_tree1 == p0;
            let p2 = n1.t.p_back;

            let rank0 = if let Some(p0) = p0 {
                self.a.get_inx_unwrap(p0).t.rank
            } else {
                0
            };

            let p_s0 = if d01 { n1.t.p_tree0 } else { n1.t.p_tree1 };
            if let Some(p_s0) = p_s0 {
                if rank0.wrapping_add(2) >= rank1 {
                    // no violation
                    break
                }
                let s0 = self.a.get_inx_unwrap(p_s0);
                let rank_s0 = s0.t.rank;

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
                    (s0.t.p_tree1, s0.t.p_tree0)
                } else {
                    (s0.t.p_tree0, s0.t.p_tree1)
                };

                let rank_a = if let Some(p_a) = p_a {
                    self.a.get_inx_unwrap(p_a).t.rank
                } else {
                    0
                };
                let rank_b = if let Some(p_b) = p_b {
                    self.a.get_inx_unwrap(p_b).t.rank
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
                    (a.t.p_tree1, a.t.p_tree0)
                } else {
                    (a.t.p_tree0, a.t.p_tree1)
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
        res
    }
}
