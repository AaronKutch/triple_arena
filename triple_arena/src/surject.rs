use core::{mem, num::NonZeroUsize};

use crate::{ptr_struct, Arena, ChainArena, Link, Ptr};

// does not need generation counter
ptr_struct!(PVal());

struct Val<T> {
    t: T,
    // we ultimately need a reference count for efficient unions, and it
    // has the bonus of being able to easily query key chain lengths
    key_count: NonZeroUsize,
}

/// A `SurjectArena` is a generalization of an `Arena` that allows multiple
/// `Ptr`s to point to a single `T`. When all `Ptr`s to a single `T` are
/// removed, the `T` is removed as well.
///
/// This is a more powerful version of union-find data structures, incorporating
/// a type, cheap ref counts, single indirection for all lookups, and allowing
/// removal. Under the hood, this uses a `O(log n)` strategy for unions, but for
/// many usecases this should actually be faster than the theoretical
/// `O(iterated log n)`, because there is always only a single layer of
/// indirections at any one time (we use a clever `ChainArena` based strategy
/// that avoids any tree structures or key reinsertion).
pub struct SurjectArena<P: Ptr, T> {
    keys: ChainArena<P, PVal>,
    vals: Arena<PVal, Val<T>>,
}

impl<P: Ptr, T> SurjectArena<P, T> {
    /// Used by tests
    #[doc(hidden)]
    pub fn _check_invariants(this: &Self) -> Result<(), &'static str> {
        // there should be exactly one key chain associated with each val
        let mut count = Arena::<PVal, usize>::new();
        for key in this.keys.vals() {
            match count.get_mut(key.t) {
                Some(p) => *p += 1,
                None => return Err("key points to nonexistent val"),
            }
        }
        for (p_val, n) in &count {
            if this.vals[p_val].key_count.get() != *n {
                return Err("key count does not match actual")
            }
        }

        let (mut p, mut b) = this.keys.first_ptr();
        loop {
            if b {
                break
            }
            let mut c = count[this.keys[p].t];
            if c != 0 {
                // upon encountering a nonzero count for the first time, we follow the chain and
                // count down, and if we reach back to the beginning (verifying cyclic chain)
                // and reach a count of zero, then we know that the chain encountered all the
                // needed keys. Subsequent encounters with the rest of the chain is ignored
                // because the count is zeroed afterwards.
                let mut tmp = p;
                loop {
                    c -= 1;
                    match this.keys.get(tmp) {
                        Some(link) => {
                            if let Some(next) = Link::next(link) {
                                tmp = next;
                            } else {
                                return Err("key chain is not cyclic")
                            }
                        }
                        None => {
                            // should not be possible unless `ChainArena` itself is broken
                            return Err("broken chain")
                        }
                    }
                    // have the test after the match so that we check for single node cyclics
                    if tmp == p {
                        if c != 0 {
                            return Err("key chain did not have all keys associated with value")
                        }
                        count[this.keys[p].t] = 0;
                        break
                    }
                }
            }
            this.keys.next_ptr(&mut p, &mut b);
        }
        Ok(())
    }

    pub fn new() -> Self {
        Self {
            keys: ChainArena::new(),
            vals: Arena::new(),
        }
    }

    /// Returns the total number of `Ptr` keys in the arena. `self.len_keys() >=
    /// self.len_vals()` is always true.
    pub fn len_keys(&self) -> usize {
        self.keys.len()
    }

    /// Returns the number of values in the arena
    pub fn len_vals(&self) -> usize {
        self.vals.len()
    }

    /// Returns the size of the set of keys pointing to the same value, with `p`
    /// being one of those keys
    pub fn len_key_set(&self, p: P) -> Option<NonZeroUsize> {
        let p_val = self.keys.get(p)?;
        Some(self.vals[p_val.t].key_count)
    }

    /// Returns if the arena is empty (`self.len_keys() == 0` if and only if
    /// `self.len_vals() == 0`)
    pub fn is_empty(&self) -> bool {
        self.vals.is_empty()
    }

    /// Returns the key capacity of the arena
    pub fn key_capacity(&self) -> usize {
        self.keys.capacity()
    }

    /// Returns the value capacity of the arena
    pub fn val_capacity(&self) -> usize {
        self.vals.capacity()
    }

    /// Follows [Arena::gen]. Note that each key in a key set keeps its own
    /// generation counter.
    pub fn gen(&self) -> P::Gen {
        self.keys.gen()
    }

    /// Follows [Arena::reserve] just for keys
    pub fn reserve_keys(&mut self, additional: usize) {
        self.keys.reserve(additional)
    }

    /// Follows [Arena::reserve] just for values
    pub fn reserve_vals(&mut self, additional: usize) {
        self.vals.reserve(additional)
    }

    /// Inserts a new value and returns the first `Ptr` key to it.
    pub fn insert_val(&mut self, t: T) -> P {
        let p_val = self.vals.insert(Val {
            t,
            key_count: NonZeroUsize::new(1).unwrap(),
        });
        self.keys.insert_new_cyclic(p_val)
    }

    /// Adds a new `Ptr` key to the same set of keys that `p` is in, and returns
    /// the new key.
    #[must_use]
    pub fn insert_key(&mut self, p: P) -> Option<P> {
        let link = match self.keys.get(p) {
            None => return None,
            Some(p) => *p,
        };
        self.vals[link.t].key_count =
            NonZeroUsize::new(self.vals[link.t].key_count.get().wrapping_add(1)).unwrap();
        Some(self.keys.insert((Some(p), None), link.t).unwrap())
    }

    /// Returns if `p` is a valid `Ptr`
    pub fn contains(&self, p: P) -> bool {
        self.keys.contains(p)
    }

    /// Returns if keys `p0` and `p1` are in the same key set. This is
    /// especially useful in case two identical values were inserted (this
    /// shows the difference between a hereditary set/map and an arena).
    #[must_use]
    pub fn in_same_set(&self, p0: P, p1: P) -> Option<bool> {
        Some(self.keys.get(p0)?.t == self.keys.get(p1)?.t)
    }

    /// Returns a reference to the value pointed to by `p`.
    #[must_use]
    pub fn get(&self, p: P) -> Option<&T> {
        let link = self.keys.get(p)?;
        Some(&self.vals[link.t].t)
    }

    /// Returns a mutable reference to the value pointed to by `p`.
    #[must_use]
    pub fn get_mut(&mut self, p: P) -> Option<&mut T> {
        let link = self.keys.get(p)?;
        Some(&mut self.vals[link.t].t)
    }

    /// Gets two `&mut T` references pointed to by `p0` and `p1`. If
    /// `self.in_same_set(p0, p1)` or a pointer is invalid, `None` is
    /// returned.
    #[must_use]
    pub fn get2_mut(&mut self, p0: P, p1: P) -> Option<(&mut T, &mut T)> {
        let link0 = self.keys.get(p0)?;
        let link1 = self.keys.get(p1)?;
        match self.vals.get2_mut(link0.t, link1.t) {
            Some((val0, val1)) => Some((&mut val0.t, &mut val1.t)),
            None => None,
        }
    }

    /// Takes the union of two key sets, of which `p0` is a key in one set and
    /// `p1` is a key in the other set. If `self.len_key_set(p0) <=
    /// self.len_key_set(p1)`, then the value pointed to by `p0` is removed and
    /// returned in a tuple with `p1`, and the key set of `p0` is changed to
    /// point to the value of `p1`'s key set. If `self.len_key_set(p0) >
    /// self.len_key_set(p1)`, the value pointed to by `p1` is removed and
    /// returned in a tuple with `p0`, and the key set of `p1` is changed to
    /// point to the value of `p0`'s key set. Returns `None` if `self.
    /// in_same_set(p0, p1)`.
    ///
    /// # Note
    ///
    /// This function is defined in this way to guarantee a `O(log n)` cost
    /// for performing repeated unions in any order on a given starting arena.
    /// If the two `T`s are some kind of additive structure that also need to
    /// have their union taken, then the contents of the `T` in the return tuple
    /// can be transferred to the value pointed to by the `P` also in the
    /// return tuple. This way, users do not actually need to consider key set
    /// sizes.
    //
    // note: we purposely reverse the typical order to `(T, P)` to give a visual
    // that the returned things were not pointing to each other.
    pub fn union(&mut self, mut p0: P, mut p1: P) -> Option<(T, P)> {
        let mut p_link0 = *self.keys.get(p0)?;
        let mut p_link1 = *self.keys.get(p1)?;
        if p_link0.t == p_link1.t {
            // corresponds to same set
            return None
        }
        let len0 = self.vals[p_link0.t].key_count.get();
        let len1 = self.vals[p_link1.t].key_count.get();
        if len0 > len1 {
            mem::swap(&mut p_link0, &mut p_link1);
            mem::swap(&mut p0, &mut p1);
        }
        // overwrite the `PVal`s in the smaller chain
        let mut tmp = p1;
        loop {
            self.keys[tmp].t = p_link0.t;
            tmp = Link::next(&self.keys[tmp]).unwrap();
            if tmp == p1 {
                break
            }
        }
        // combine chains cheaply, this is why they need to be cyclic because exchanging
        // two interlinks anywhere between the chains results in a combined single
        // cyclic chain.
        self.keys.exchange_next(p0, p1).unwrap();
        // it is be impossible to overflow this, it would mean that we have already
        // inserted `usize + 1` elements
        self.vals[p_link0.t].key_count = NonZeroUsize::new(len0.wrapping_add(len1)).unwrap();
        Some((self.vals.remove(p_link1.t).unwrap().t, p0))
    }
}