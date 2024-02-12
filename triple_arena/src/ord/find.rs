use core::cmp::{min, Ordering};

use crate::{utils::ChainNoGenArena, Advancer, OrdArena, Ptr};

impl<P: Ptr, K: Ord, V> OrdArena<P, K, V> {
    /// Used by tests
    #[doc(hidden)]
    pub fn _check_invariants(this: &Self) -> Result<(), &'static str> {
        // needed because of special functions like `compress_and_shrink`
        ChainNoGenArena::_check_invariants(&this.a)?;
        if this.a.is_empty() {
            return Ok(())
        }
        // check the root
        if let Some((_, root)) = this.a.get_no_gen(this.root) {
            if root.t.p_back.is_some() {
                return Err("root node has a back pointer")
            }
        } else {
            return Err("this.root is broken")
        };
        // first check the chain and ordering
        let mut count = 0usize;
        let mut prev: Option<P> = None;
        if let Some((_, link)) = this.a.get_no_gen(this.first) {
            if link.prev().is_some() {
                return Err("this.first is broken")
            }
        } else {
            return Err("this.first is broken")
        }

        let mut adv = this.a.advancer_chain(this.first);
        while let Some(p) = adv.advance(&this.a) {
            count = count.checked_add(1).unwrap();
            if !this.a.contains(p) {
                return Err("invalid Ptr")
            }
            if let Some(prev) = prev {
                if Ord::cmp(
                    &this.a.get_no_gen(prev.inx()).unwrap().1.t.k,
                    &this.a.get_no_gen(p.inx()).unwrap().1.t.k,
                ) == Ordering::Greater
                {
                    return Err("incorrect ordering")
                }
            }
            prev = Some(p);
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
        let mut adv = this.a.advancer();
        while let Some(p) = adv.advance(&this.a) {
            let node = &this.a.get(p).unwrap();
            if let Some(p_back) = node.p_back {
                if let Some((_, parent)) = this.a.get_no_gen(p_back) {
                    if (parent.t.p_tree0 != Some(p.inx())) && (parent.t.p_tree1 != Some(p.inx())) {
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
                if let Some((_, child0)) = this.a.get_no_gen(p_tree0) {
                    if child0.t.p_back != Some(p.inx()) {
                        return Err("broken tree")
                    }
                    if child0.t.p_back == Some(p_tree0) {
                        return Err("cycle")
                    }
                } else {
                    return Err("broken tree")
                }
            }
            if let Some(p_tree1) = node.p_tree1 {
                if let Some((_, child1)) = this.a.get_no_gen(p_tree1) {
                    if child1.t.p_back != Some(p.inx()) {
                        return Err("broken tree")
                    }
                    if child1.t.p_back == Some(p_tree1) {
                        return Err("cycle")
                    }
                } else {
                    return Err("broken tree")
                }
            }
        }
        // check the ranks
        let mut adv = this.a.advancer();
        while let Some(p) = adv.advance(&this.a) {
            let node = &this.a.get(p).unwrap();

            let rank0 = if let Some(p_tree0) = node.p_tree0 {
                this.a.get_inx_unwrap(p_tree0).t.rank
            } else {
                0
            };
            if node.rank <= rank0 {
                return Err("rank difference is zero or negative")
            }
            let rank1 = if let Some(p_tree1) = node.p_tree1 {
                this.a.get_inx_unwrap(p_tree1).t.rank
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
        }
        Ok(())
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
            let (gen, link) = self.a.get_no_gen(p).unwrap();
            let node = &link.t;
            match Ord::cmp(k, &node.k) {
                Ordering::Less => p = node.p_tree0?,
                Ordering::Equal => break Some(Ptr::_from_raw(p, gen)),
                Ordering::Greater => p = node.p_tree1?,
            }
        }
    }

    /// The same as [OrdArena::find_key], except it uses linear
    /// comparisons starting at `p_init`. If the key is not found
    /// within `num` comparisons, or `p_init` is invalid, a normal search is
    /// used. Returns `None` if the key was not found.
    #[must_use]
    pub fn find_key_linear(&self, p_init: P, num: usize, k: &K) -> Option<P> {
        if !self.a.contains(p_init) {
            return self.find_key(k)
        }
        // we settled on the model of trying `num` linear comparisons, because any kind
        // of search starting from the leaves of the tree runs into the problem that
        // constant numbers of distance can leave the target on the other side of the
        // tree, and the search time becomes twice the normal search time in many cases.
        let mut p = p_init.inx();
        let mut direction = None;
        for _ in 0..num {
            let (gen, link) = self.a.get_no_gen(p).unwrap();
            let node = &link.t;
            match Ord::cmp(k, &node.k) {
                Ordering::Less => {
                    if direction == Some(true) {
                        break
                    }
                    direction = Some(false);
                    if let Some(prev) = link.prev() {
                        p = prev;
                    } else {
                        break
                    }
                }
                Ordering::Equal => return Some(Ptr::_from_raw(p, gen)),
                Ordering::Greater => {
                    if direction == Some(false) {
                        break
                    }
                    direction = Some(true);
                    if let Some(next) = link.next() {
                        p = next;
                    } else {
                        break
                    }
                }
            }
        }
        self.find_key(k)
    }

    /// Finds a `Ptr` with an associated key that is equal key to `k`. If such a
    /// key is not in the arena, this will instead return a `Ptr` to a similar
    /// key, such that if `k` were to be inserted into the arena, it would be
    /// inserted immediately previous or next to the entry of the returned
    /// `Ptr`. An `Ordering` is returned, with `Ordering::Equal` indicating an
    /// exact match was found, `Ordering::Less` indicating that `k` is less than
    /// the similar entry, and `Ordering::Greater` indicating that `k` is
    /// greater than the similar entry. `None` is returned if `self.is_empty()`.
    #[must_use]
    pub fn find_similar_key(&self, k: &K) -> Option<(P, Ordering)> {
        if self.a.is_empty() {
            return None
        }
        let mut p = self.root;
        loop {
            let (gen, link) = self.a.get_no_gen(p).unwrap();
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

    /// Combines the behaviors of [OrdArena::find_similar_key] and
    /// [OrdArena::find_key_linear]
    #[must_use]
    pub fn find_similar_key_linear(&self, p_init: P, num: usize, k: &K) -> Option<(P, Ordering)> {
        if !self.a.contains(p_init) {
            return self.find_similar_key(k)
        }
        let mut p = p_init.inx();
        let mut direction = None;
        for _ in 0..num {
            let (gen, link) = self.a.get_no_gen(p).unwrap();
            let node = &link.t;
            let p_with_gen = Ptr::_from_raw(p, gen);
            match Ord::cmp(k, &node.k) {
                Ordering::Less => {
                    if direction == Some(true) {
                        return Some((p_with_gen, Ordering::Less))
                    }
                    direction = Some(false);
                    if let Some(prev) = link.prev() {
                        p = prev;
                    } else {
                        return Some((p_with_gen, Ordering::Less))
                    }
                }
                Ordering::Equal => return Some((p_with_gen, Ordering::Equal)),
                Ordering::Greater => {
                    if direction == Some(false) {
                        return Some((p_with_gen, Ordering::Greater))
                    }
                    direction = Some(true);
                    if let Some(next) = link.next() {
                        p = next;
                    } else {
                        return Some((p_with_gen, Ordering::Greater))
                    }
                }
            }
        }
        self.find_similar_key(k)
    }
}

/// Does not require `K: Ord`
impl<P: Ptr, K, V> OrdArena<P, K, V> {
    /// Finds a `Ptr` through binary search with a user-provided function `f`.
    /// `f` is provided a `P, &K, &V` triple of the node the binary search is
    /// currently at. Will go in a `Ordering::Less` direction if `f` returns
    /// that, or an `Ordering::Greater` direction if `f` returns that. Stops and
    /// returns the `P` when `Ordering::Equal` is returned. Returns
    /// `None` if `self.is_empty` or an `Ordering::Equal` case is not
    /// encountered by the end of the binary search.
    pub fn find_with<F: FnMut(P, &K, &V) -> Ordering>(&self, mut f: F) -> Option<P> {
        if self.a.is_empty() {
            return None
        }
        let mut p = self.root;
        loop {
            let (gen, link) = self.a.get_no_gen(p).unwrap();
            let node = &link.t;
            let p_with_gen = Ptr::_from_raw(p, gen);
            match f(p_with_gen, &node.k, &node.v) {
                Ordering::Less => p = node.p_tree0?,
                Ordering::Equal => break Some(p_with_gen),
                Ordering::Greater => p = node.p_tree1?,
            }
        }
    }

    /// The same as [OrdArena::find_with], except that if `f` does not return
    /// `Ordering::Equal` by the end of the binary search (and in which case the
    /// returned ordering will be `Ordering::Equal`), it will instead return a
    /// similar `Ptr` with the last `Ordering` returned by `f`. `None` is only
    /// returned if `self.is_empty()`
    pub fn find_similar_with<F: FnMut(P, &K, &V) -> Ordering>(
        &self,
        mut f: F,
    ) -> Option<(P, Ordering)> {
        if self.a.is_empty() {
            return None
        }
        let mut p = self.root;
        loop {
            let (gen, link) = self.a.get_no_gen(p).unwrap();
            let node = &link.t;
            let p_with_gen = Ptr::_from_raw(p, gen);
            match f(p_with_gen, &node.k, &node.v) {
                Ordering::Less => {
                    if let Some(tmp) = node.p_tree0 {
                        p = tmp;
                    } else {
                        return Some((p_with_gen, Ordering::Less))
                    }
                }
                Ordering::Equal => break Some((p_with_gen, Ordering::Equal)),
                Ordering::Greater => {
                    if let Some(tmp) = node.p_tree1 {
                        p = tmp;
                    } else {
                        return Some((p_with_gen, Ordering::Greater))
                    }
                }
            }
        }
    }
}

// example use of the below in debugging
/*
use std::path::PathBuf;
use triple_arena::{ptr_struct, Arena, OrdArena};
use triple_arena_render::{render_to_svg_file, DebugNode};
// ...
let debug_arena = a.debug_arena();
let mut debug_arena2 = Arena::new();
let res = OrdArena::_check_invariants(&a);
if res.is_err() {
    debug_arena2.clone_from_with(
        &debug_arena,
        |_, (rank, k, _, p_tree0, p_back, p_tree1)| DebugNode {
            sources: if let Some(p_back) = p_back {
                vec![(*p_back, String::new())]
            } else {
                vec![]
            },
            center: vec![format!("r: {rank}, k: {k}")],
            sinks: {
                let mut v = vec![];
                if let Some(p_tree0) = p_tree0 {
                    v.push((*p_tree0, "0".to_owned()));
                }
                if let Some(p_tree1) = p_tree1 {
                    v.push((*p_tree1, "1".to_owned()));
                }
                v
            },
        },
    );
    render_to_svg_file(&debug_arena2, false, PathBuf::from("tmp.svg".to_owned()))
        .unwrap();
    println!("{}", a.debug());
    dbg!(len);
}
res.unwrap();
*/

/// Used for development debugging only, see find.rs for example
#[cfg(feature = "expose_internal_utils")]
#[allow(clippy::type_complexity)]
impl<P: Ptr, K: Ord + Clone + alloc::fmt::Debug, V: Clone + alloc::fmt::Debug> OrdArena<P, K, V> {
    pub fn debug_arena(&self) -> crate::Arena<P, (u8, K, V, Option<P>, Option<P>, Option<P>)> {
        let mut res: crate::Arena<P, (u8, K, V, Option<P>, Option<P>, Option<P>)> =
            crate::Arena::new();
        self.a.clone_to_arena(&mut res, |_, link| {
            (
                link.t.rank,
                link.t.k.clone(),
                link.t.v.clone(),
                link.t
                    .p_tree0
                    .map(|inx| Ptr::_from_raw(inx, crate::utils::PtrGen::one())),
                link.t
                    .p_back
                    .map(|inx| Ptr::_from_raw(inx, crate::utils::PtrGen::one())),
                link.t
                    .p_tree1
                    .map(|inx| Ptr::_from_raw(inx, crate::utils::PtrGen::one())),
            )
        });
        // fix the generations
        let mut adv = res.advancer();
        while let Some(p) = adv.advance(&res) {
            if let Some(ref mut tmp) = res.get_mut(p).unwrap().3 {
                let gen = self
                    .a
                    .get_no_gen(tmp.inx())
                    .map(|x| x.0)
                    .unwrap_or(<P::Gen as crate::utils::PtrGen>::one());
                *tmp = Ptr::_from_raw(tmp.inx(), gen);
            }
            if let Some(ref mut tmp) = res.get_mut(p).unwrap().4 {
                let gen = self
                    .a
                    .get_no_gen(tmp.inx())
                    .map(|x| x.0)
                    .unwrap_or(<P::Gen as crate::utils::PtrGen>::one());
                *tmp = Ptr::_from_raw(tmp.inx(), gen);
            }
            if let Some(ref mut tmp) = res.get_mut(p).unwrap().5 {
                let gen = self
                    .a
                    .get_no_gen(tmp.inx())
                    .map(|x| x.0)
                    .unwrap_or(<P::Gen as crate::utils::PtrGen>::one());
                *tmp = Ptr::_from_raw(tmp.inx(), gen);
            }
        }
        res
    }

    pub fn debug(&self) -> alloc::string::String {
        use core::fmt::Write;
        let mut s = alloc::string::String::new();
        writeln!(s, "root: {:?}", self.root).unwrap();
        writeln!(s, "first: {:?}", self.first).unwrap();
        writeln!(s, "last: {:?}", self.last).unwrap();
        let mut adv = self.a.advancer_chain(self.first);
        while let Some(p) = adv.advance(&self.a) {
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
        }
        s
    }
}
