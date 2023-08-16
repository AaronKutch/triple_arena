use core::cmp::{min, Ordering};

use crate::{Advancer, ChainArena, OrdArena, Ptr};

impl<P: Ptr, K: Ord, V> OrdArena<P, K, V> {
    /// Used by tests
    #[doc(hidden)]
    pub fn _check_invariants(this: &Self) -> Result<(), &'static str> {
        // needed because of special functions like `compress_and_shrink`
        ChainArena::_check_invariants(&this.a)?;
        if this.a.is_empty() {
            return Ok(())
        }
        // check the root
        if let Some((_, root)) = this.a.get_ignore_gen(this.root) {
            if root.t.p_back.is_some() {
                return Err("root node has a back pointer")
            }
        } else {
            return Err("this.root is broken")
        };
        // first check the chain and ordering
        let mut count = 0usize;
        let mut prev: Option<P> = None;
        let first_gen = if let Some((first_gen, link)) = this.a.get_ignore_gen(this.first) {
            if link.prev().is_some() {
                return Err("this.first is broken")
            }
            first_gen
        } else {
            return Err("this.first is broken")
        };

        let mut adv = this.a.advancer_chain(Ptr::_from_raw(this.first, first_gen));
        while let Some(p) = adv.advance(&this.a) {
            count = count.checked_add(1).unwrap();
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
                if let Some((_, parent)) = this.a.get_ignore_gen(p_back) {
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
                if let Some((_, child0)) = this.a.get_ignore_gen(p_tree0) {
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
                if let Some((_, child1)) = this.a.get_ignore_gen(p_tree1) {
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
            let (gen, link) = self.a.get_ignore_gen(p).unwrap();
            let node = &link.t;
            match Ord::cmp(k, &node.k) {
                Ordering::Less => p = node.p_tree0?,
                Ordering::Equal => break Some(Ptr::_from_raw(p, gen)),
                Ordering::Greater => p = node.p_tree1?,
            }
        }
    }

    /// The same as [OrdArena::find_key], except it uses linear
    /// comparisons starting at `p_init`. If `p` is not within a small constant
    /// number of elements away from where `k` should be ordered, this
    /// function may operate in `O(n)` time instead of the `O(1)` this is
    /// intended for. Returns `None` if `p_init` is invalid or the key was not
    /// found.
    #[must_use]
    pub fn find_key_linear(&self, p_init: P, k: &K) -> Option<P> {
        if !self.a.contains(p_init) {
            return None
        }
        let mut p = p_init.inx();
        let mut direction = None;
        loop {
            let (gen, link) = self.a.get_ignore_gen(p).unwrap();
            let node = &link.t;
            match Ord::cmp(k, &node.k) {
                Ordering::Less => {
                    if direction == Some(true) {
                        break None
                    }
                    direction = Some(false);
                    if let Some(prev) = link.prev() {
                        p = prev.inx();
                    } else {
                        break None
                    }
                }
                Ordering::Equal => break Some(Ptr::_from_raw(p, gen)),
                Ordering::Greater => {
                    if direction == Some(false) {
                        break None
                    }
                    direction = Some(true);
                    if let Some(next) = link.next() {
                        p = next.inx();
                    } else {
                        break None
                    }
                }
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
    #[must_use]
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

    /// Combines the behaviors of [OrdArena::find_similar_key] and
    /// [OrdArena::find_key_linear]
    #[must_use]
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
        let (gen, _) = self.a.get_ignore_gen(p).unwrap();
        Some((Ptr::_from_raw(p, gen), ordering))
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
                    .get_ignore_gen(tmp.inx())
                    .map(|x| x.0)
                    .unwrap_or(<P::Gen as crate::utils::PtrGen>::one());
                *tmp = Ptr::_from_raw(tmp.inx(), gen);
            }
            if let Some(ref mut tmp) = res.get_mut(p).unwrap().4 {
                let gen = self
                    .a
                    .get_ignore_gen(tmp.inx())
                    .map(|x| x.0)
                    .unwrap_or(<P::Gen as crate::utils::PtrGen>::one());
                *tmp = Ptr::_from_raw(tmp.inx(), gen);
            }
            if let Some(ref mut tmp) = res.get_mut(p).unwrap().5 {
                let gen = self
                    .a
                    .get_ignore_gen(tmp.inx())
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
        let init = Ptr::_from_raw(
            self.first,
            self.a
                .get_ignore_gen(self.first)
                .map(|x| x.0)
                .unwrap_or(<P::Gen as crate::utils::PtrGen>::one()),
        );
        let mut adv = self.a.advancer_chain(init);
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
