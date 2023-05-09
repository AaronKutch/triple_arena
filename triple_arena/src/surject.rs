use alloc::fmt;
use core::{
    borrow::Borrow,
    mem,
    num::NonZeroUsize,
    ops::{Index, IndexMut},
};

use fmt::Debug;

use crate::{ptr_struct, Arena, ChainArena, Link, Ptr};

// does not need generation counter
ptr_struct!(PVal());

#[derive(Clone)]
pub(crate) struct Val<T> {
    pub(crate) t: T,
    // we ultimately need a reference count for efficient unions, and it
    // has the bonus of being able to easily query key chain lengths
    key_count: NonZeroUsize,
}

/// A generalization of an `Arena` that allows multiple `Ptr`s to point to a
/// single `T`. When all `Ptr`s to a single `T` are removed, the `T` is removed
/// as well. Efficient union-find functionality is also possible.
///
/// This is a more powerful version of union-find data structures, incorporating
/// a type, `O(1)` single and double element operations, and allowing generation
/// counted removal. Under the hood, this uses a `O(n log n)` strategy for
/// union-find, but for many usecases this should actually be faster than the
/// theoretical `O(n iterated log n)`, because there is always only a single
/// layer of indirections at any one time for caches to deal with (we use a
/// clever `ChainArena` based strategy that avoids any tree structures
/// or key reinsertion).
///
/// ```
/// use triple_arena::{ptr_struct, SurjectArena};
///
/// ptr_struct!(P0);
/// let mut a: SurjectArena<P0, String> = SurjectArena::new();
///
/// let p42_0 = a.insert_val("42".to_owned());
/// let p42_1 = a.insert_key(p42_0).unwrap();
/// let p42_2 = a.insert_key(p42_0).unwrap();
///
/// // any of the keys above point to the same value
/// assert_eq!(&a[p42_0], "42");
/// assert_eq!(&a[p42_1], "42");
/// assert_eq!(&a[p42_2], "42");
///
/// // even if we don't use the union-find feature, even
/// // `SurjectArena<P, ()>`  is useful for its O(1) set-like
/// // operations and adding and removing keys in any order.
/// // This is more powerful than pure reference counting or
/// // epoch-like structures.
/// assert_eq!(a.remove_key(p42_1), Some(None));
/// assert!(a.contains(p42_0));
/// assert!(!a.contains(p42_1));
/// assert!(a.contains(p42_2));
/// assert!(a.insert_key(p42_1).is_none());
/// // need to use existing valid key
/// let p42_3 = a.insert_key(p42_2).unwrap();
/// assert_eq!(&a[p42_3], "42");
///
/// let other42 = a.insert_val("42".to_owned());
/// // note this is still a general `Arena`-like structure and not a hereditary
/// // set or map, so multiple of the same exact values can exist in different
/// // surjects.
/// assert!(!a.in_same_set(p42_0, other42).unwrap());
/// a.remove_val(other42).unwrap();
///
/// let p7_0 = a.insert_val("7".to_owned());
/// let p7_1 = a.insert_key(p7_0).unwrap();
/// assert_eq!(&a[p7_0], "7");
/// assert_eq!(&a[p42_2], "42");
///
/// let (removed_t, kept_p) = a.union(p42_0, p7_1).unwrap();
/// // One of the "7" or "42" values was removed from the arena,
/// // and the other remains in the arena. Suppose we want
/// // to take a custom union of the `String`s to go along
/// // with the union of the keys, we would do something like
/// a[kept_p] = format!("{} + {}", a[kept_p], removed_t);
/// assert_eq!(&a[p7_0], "42 + 7");
/// assert_eq!(&a[p7_1], "42 + 7");
/// assert_eq!(&a[p42_0], "42 + 7");
/// assert_eq!(&a[p42_2], "42 + 7");
/// assert_eq!(&a[p42_3], "42 + 7");
/// assert_eq!(a.len_key_set(p7_0).unwrap().get(), 5);
/// // iteration over the key value pairs can repeat the same value multiple times
/// let v = "42 + 7";
/// // I know the order ahead of time because the arena is deterministic
/// let expected = [(p42_0, v), (p42_3, v), (p42_2, v), (p7_0, v), (p7_1, v)];
/// for (i, (key, val)) in a.iter().enumerate() {
///     assert_eq!(expected[i], (key, val.as_str()));
/// }
///
/// // only upon removing the last key is the value is returned
/// // (or we could use wholesale `remove_val`)
/// assert_eq!(a.remove_key(p7_0), Some(None));
/// assert_eq!(a.remove_key(p42_0), Some(None));
/// assert_eq!(a.remove_key(p42_3), Some(None));
/// assert_eq!(a.remove_key(p7_1), Some(None));
/// assert_eq!(a.remove_key(p42_2), Some(Some("42 + 7".to_owned())));
/// ```
pub struct SurjectArena<P: Ptr, T> {
    pub(crate) keys: ChainArena<P, PVal>,
    pub(crate) vals: Arena<PVal, Val<T>>,
}

/// # Note
///
/// `Ptr`s in a `SurjectArena` follow the same validity rules as `Ptr`s in a
/// regular `Arena` (see the documentation on the main
/// `impl<P: Ptr, T> Arena<P, T>`). The validity of each `Ptr` is kept separate.
impl<P: Ptr, T> SurjectArena<P, T> {
    /// Used by tests
    #[doc(hidden)]
    pub fn _check_invariants(this: &Self) -> Result<(), &'static str> {
        // there should be exactly one key chain associated with each val
        let mut count = Arena::<PVal, usize>::new();
        count.clone_from_with(&this.vals, |_, _| 0);
        for key in this.keys.vals() {
            match count.get_mut(key.t) {
                Some(p) => *p += 1,
                None => return Err("key points to nonexistent val"),
            }
        }
        for (p_val, n) in &count {
            if this.vals.get(p_val).unwrap().key_count.get() != *n {
                return Err("key count does not match actual")
            }
        }

        let (mut p, mut b) = this.keys.first_ptr();
        loop {
            if b {
                break
            }
            let mut c = *count.get(this.keys.get(p).unwrap().t).unwrap();
            if c != 0 {
                // upon encountering a nonzero count for the first time, we follow the chain and
                // count down, and if we reach back to the beginning (verifying cyclic chain)
                // and reach a count of zero, then we know that the chain encountered all the
                // needed keys. Subsequent encounters with the rest of the chain is ignored
                // because the count is zeroed afterwards.
                let mut tmp = p;
                loop {
                    if c == 0 {
                        return Err("did not reach end of key chain in expected time")
                    }
                    c -= 1;
                    let link = this.keys.get(tmp).unwrap();
                    if let Some(next) = Link::next(link) {
                        tmp = next;
                    } else {
                        return Err("key chain is not cyclic")
                    }
                    // have the test after the match so that we check for single node cyclics
                    if tmp == p {
                        if c != 0 {
                            return Err("key chain did not have all keys associated with value")
                        }
                        *count.get_mut(this.keys.get(p).unwrap().t).unwrap() = 0;
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
    /// being one of those keys. Returns `None` if `p` is invalid.
    #[must_use]
    pub fn len_key_set(&self, p: P) -> Option<NonZeroUsize> {
        let p_val = self.keys.get(p)?.t;
        Some(self.vals.get(p_val).unwrap().key_count)
    }

    /// Returns if the arena is empty (`self.len_keys() == 0` if and only if
    /// `self.len_vals() == 0`)
    pub fn is_empty(&self) -> bool {
        self.vals.is_empty()
    }

    /// Returns the key capacity of the arena
    pub fn capacity_keys(&self) -> usize {
        self.keys.capacity()
    }

    /// Returns the value capacity of the arena
    pub fn capacity_vals(&self) -> usize {
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

    /// Inserts the `T` returned by `create` into the arena and returns a `Ptr`
    /// to it. `create` is given the the same `Ptr` that is returned, which is
    /// useful for initialization of immutable structures that need to reference
    /// themselves. This function allocates if capacity in the arena runs out.
    pub fn insert_val_with<F: FnOnce(P) -> T>(&mut self, create: F) -> P {
        let mut res = P::invalid();
        self.vals.insert_with(|p_val| {
            let mut created_t = None;
            self.keys.insert_new_cyclic_with(|p| {
                res = p;
                created_t = Some(create(p));
                p_val
            });
            Val {
                t: created_t.unwrap(),
                key_count: NonZeroUsize::new(1).unwrap(),
            }
        });
        res
    }

    /// Adds a new `Ptr` key to the same key set that `p` is in (any `Ptr`
    /// from the valid key set can be used as a reference), and returns the new
    /// key.
    #[must_use]
    pub fn insert_key(&mut self, p: P) -> Option<P> {
        let p_val = match self.keys.get(p) {
            None => return None,
            Some(p) => p.t,
        };
        self.vals[p_val].key_count = NonZeroUsize::new(
            self.vals
                .get(p_val)
                .unwrap()
                .key_count
                .get()
                .wrapping_add(1),
        )
        .unwrap();
        Some(self.keys.insert((Some(p), None), p_val).unwrap())
    }

    /// Returns if `p` is a valid `Ptr`
    pub fn contains(&self, p: P) -> bool {
        self.keys.contains(p)
    }

    /// Returns if keys `p0` and `p1` are in the same key set. This is
    /// especially useful in case two identical values were inserted (this
    /// shows the difference between a hereditary set/map and a surjection
    /// arena).
    #[must_use]
    pub fn in_same_set(&self, p0: P, p1: P) -> Option<bool> {
        Some(self.keys.get(p0)?.t == self.keys.get(p1)?.t)
    }

    /// Returns a reference to the value pointed to by `p`.
    #[must_use]
    pub fn get(&self, p: P) -> Option<&T> {
        let p_val = self.keys.get(p)?.t;
        Some(&self.vals.get(p_val).unwrap().t)
    }

    /// Returns a mutable reference to the value pointed to by `p`.
    #[must_use]
    pub fn get_mut(&mut self, p: P) -> Option<&mut T> {
        let p_val = self.keys.get(p)?.t;
        Some(&mut self.vals.get_mut(p_val).unwrap().t)
    }

    /// Gets two `&mut T` references pointed to by `p0` and `p1`. If
    /// `self.in_same_set(p0, p1)` or a pointer is invalid, `None` is
    /// returned.
    #[must_use]
    pub fn get2_mut(&mut self, p0: P, p1: P) -> Option<(&mut T, &mut T)> {
        let p_val0 = self.keys.get(p0)?.t;
        let p_val1 = self.keys.get(p1)?.t;
        match self.vals.get2_mut(p_val0, p_val1) {
            Some((val0, val1)) => Some((&mut val0.t, &mut val1.t)),
            None => None,
        }
    }

    /// Takes the union of two key sets, of which `p0` is a key in one set and
    /// `p1` is a key in the other set. If `self.len_key_set(p0) <
    /// self.len_key_set(p1)`, then the value pointed to by `p0` is removed and
    /// returned in a tuple with `p1`, and the key set of `p0` is changed to
    /// point to the value of `p1`'s key set. If `self.len_key_set(p0) >=
    /// self.len_key_set(p1)`, the value pointed to by `p1` is removed and
    /// returned in a tuple with `p0`, and the key set of `p1` is changed to
    /// point to the value of `p0`'s key set. Returns `None` if
    /// `self.in_same_set(p0, p1)`.
    ///
    /// # Note
    ///
    /// No `Ptr`s are invalidated even though a value is removed, all that
    /// happens is both key sets are redirected point to a common value.
    ///
    /// This function is defined in this way to guarantee a `O(n log n)` cost
    /// for performing repeated unions in any order on a given starting arena.
    /// If the two `T`s are some kind of additive structure that also need to
    /// have their union taken, then the contents of the `T` in the return tuple
    /// can be transferred to the value pointed to by the `P` also in the
    /// return tuple. This way, users do not actually need to consider key set
    /// sizes explicitly.
    //
    // note: we purposely reverse the typical order to `(T, P)` to give a visual
    // that the returned things were not pointing to each other.
    #[must_use]
    pub fn union(&mut self, mut p0: P, mut p1: P) -> Option<(T, P)> {
        let mut p_link0 = *self.keys.get(p0)?;
        let mut p_link1 = *self.keys.get(p1)?;
        if p_link0.t == p_link1.t {
            // corresponds to same set
            return None
        }
        let len0 = self.vals.get(p_link0.t).unwrap().key_count.get();
        let len1 = self.vals.get(p_link1.t).unwrap().key_count.get();
        if len0 < len1 {
            mem::swap(&mut p_link0, &mut p_link1);
            mem::swap(&mut p0, &mut p1);
        }
        // overwrite the `PVal`s in the smaller chain
        let mut tmp = p1;
        loop {
            *self.keys.get_mut(tmp).unwrap().t = p_link0.t;
            tmp = Link::next(self.keys.get(tmp).unwrap()).unwrap();
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
        self.vals.get_mut(p_link0.t).unwrap().key_count =
            NonZeroUsize::new(len0.wrapping_add(len1)).unwrap();
        Some((self.vals.remove_internal(p_link1.t, false).unwrap().t, p0))
    }

    /// Removes the key `p`. If there were other keys still in the key set, the
    /// value is not removed and `Some(None)` is returned. If `p` was the last
    /// key in the key set, then the value is removed and returned. Returns
    /// `None` if `p` is not valid.
    #[must_use]
    pub fn remove_key(&mut self, p: P) -> Option<Option<T>> {
        let p_val = self.keys.remove(p)?.t;
        let key_count = self.vals.get(p_val).unwrap().key_count.get();
        if key_count == 1 {
            // last key, remove the value
            Some(Some(self.vals.remove(p_val).unwrap().t))
        } else {
            // decrement the key count
            self.vals.get_mut(p_val).unwrap().key_count =
                NonZeroUsize::new(key_count.wrapping_sub(1)).unwrap();
            Some(None)
        }
    }

    /// Removes the entire key set and value cheaply, returning the value. `p`
    /// should be any key from the key set. Returns `None` if `p` is invalid.
    pub fn remove_val(&mut self, p: P) -> Option<T> {
        let p_val = self.keys.get(p)?.t;
        self.keys.remove_cyclic_chain_internal(p, true);
        Some(self.vals.remove(p_val).unwrap().t)
    }

    /// Invalidates the key `p` (no other keys in the key set are invalidated),
    /// returning a new valid key. Returns `None` if `p` is not valid.
    #[must_use]
    pub fn invalidate_key(&mut self, p: P) -> Option<P> {
        // the chain arena fixes interlinks
        self.keys.invalidate(p)
    }

    /// Swaps the `T` values pointed to by keys `p0` and `p1` and keeps the
    /// generation counters as-is. If `p0` and `p1` are in the same key set,
    /// then nothing occurs. Returns `None` if `p0` or `p1` are invalid.
    #[must_use]
    pub fn swap(&mut self, p0: P, p1: P) -> Option<()> {
        let p_val0 = self.keys.get(p0)?.t;
        let p_val1 = self.keys.get(p1)?.t;
        if p_val0 != p_val1 {
            // we only want to swap the `T` and not the ref counts
            let (lhs, rhs) = self.vals.get2_mut(p_val0, p_val1).unwrap();
            mem::swap(&mut lhs.t, &mut rhs.t);
        } // else no-op and we also checked for containment earlier
        Some(())
    }

    /// Drops all keys and values from the arena and invalidates all pointers
    /// previously created from it. This has no effect on allocated
    /// capacities of keys or values.
    pub fn clear(&mut self) {
        self.keys.clear();
        self.vals.clear();
    }

    /// Performs a [SurjectArena::clear] and resets key and value capacities to
    /// 0
    pub fn clear_and_shrink(&mut self) {
        self.keys.clear_and_shrink();
        self.vals.clear_and_shrink();
    }
}

impl<P: Ptr, T, B: Borrow<P>> Index<B> for SurjectArena<P, T> {
    type Output = T;

    fn index(&self, index: B) -> &Self::Output {
        let p_val = self.keys.get(*index.borrow()).unwrap().t;
        &self.vals.get(p_val).unwrap().t
    }
}

impl<P: Ptr, T, B: Borrow<P>> IndexMut<B> for SurjectArena<P, T> {
    fn index_mut(&mut self, index: B) -> &mut Self::Output {
        let p_val = self.keys.get(*index.borrow()).unwrap().t;
        &mut self.vals.get_mut(p_val).unwrap().t
    }
}

impl<P: Ptr, T: Debug> Debug for SurjectArena<P, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<P: Ptr, T: Clone> Clone for SurjectArena<P, T> {
    fn clone(&self) -> Self {
        Self {
            keys: self.keys.clone(),
            vals: self.vals.clone(),
        }
    }
}

impl<PLink: Ptr, T> Default for SurjectArena<PLink, T> {
    fn default() -> Self {
        Self::new()
    }
}
