use alloc::fmt;
use core::{mem, num::NonZeroUsize};

use fmt::Debug;

use crate::{ptr::PtrNoGen, Arena, ChainArena, Link, Ptr};

#[derive(Clone)]
pub(crate) struct Key<P: Ptr, K> {
    pub(crate) k: K,
    // we want to have the size of `P::Inx` since we do not need the generation counter on the
    // internal indirection
    pub(crate) p_val: PtrNoGen<P>,
}

#[derive(Clone)]
pub(crate) struct Val<V> {
    pub(crate) v: V,
    // we ultimately need a reference count for efficient unions, and it
    // has the bonus of being able to easily query key chain lengths
    key_count: NonZeroUsize,
}

/// A generalization of an `Arena` with three parameters: a `P: Ptr` type, a `K`
/// key type, and a `V` value type. Each `P` points to a single `K` like in a
/// normal arena, but multiple `P` can point to a single `V` in a surjective map
/// structure. When all `Ptr`s to a single `V` are removed, the `V` is removed
/// as well. Efficient union-find functionality is also possible.
///
/// This is a more powerful version of union-find data structures, incorporating
/// types on both sides of the key-value surjection, individual pointer-key
/// validity tracking, `O(1)` single and double element operations, and allowing
/// generation counted removal. Under the hood, this uses a `O(n log n)`
/// strategy for union-find, but for many usecases this should actually be
/// faster than the theoretical `O(n iterated log n)`, because there is always
/// only a single layer of indirections at any one time for caches to deal with
/// (we use a clever `ChainArena` based strategy that avoids any tree structures
/// or key reinsertion).
///
/// `SurjectArena<P, (), V>` is more like a classic union-find structure, and
/// `SurjectArena<P, K, ()>` is a kind of non-hereditary set. Even
/// `SurjectArena<P, (), ()>` can be useful (assuming `P` has generation
/// counters) for its O(1) validity tracking capabilities under any order
/// of adding and removing of pointers. This is more powerful than pure
/// reference counting or epoch-like structures.
///
/// ```
/// use triple_arena::{ptr_struct, SurjectArena};
///
/// ptr_struct!(P0);
/// let mut a: SurjectArena<P0, String, String> = SurjectArena::new();
///
/// // There must be at least one key associated with each value
/// let p0_42 = a.insert("key0".to_owned(), "42".to_owned());
/// // If we want new keys to be associated with the same key set pointing to
/// // "42", then instead of calling `insert_val` we call `insert_key`
/// let p1_42 = a.insert_key(p0_42, "key1".to_owned()).unwrap();
/// // We could use either `p0_42` or `p1_42` as our reference to get
/// // associated with the same key set; any valid pointer in the preexisting
/// // set can be used with the same `O(1)` computational complexity incurred.
/// let p2_42 = a.insert_key(p0_42, "key2".to_owned()).unwrap();
///
/// assert_eq!(a.get_key(p0_42).unwrap(), "key0");
/// assert_eq!(a.get_key(p1_42).unwrap(), "key1");
/// assert_eq!(a.get_key(p2_42).unwrap(), "key2");
/// assert_eq!(a.get_val(p0_42).unwrap(), "42");
/// assert_eq!(a.get_val(p1_42).unwrap(), "42");
/// assert_eq!(a.get_val(p2_42).unwrap(), "42");
///
/// assert_eq!(a.remove_key(p1_42), Some(("key1".to_owned(), None)));
/// assert!(a.contains(p0_42));
/// assert!(!a.contains(p1_42));
/// assert!(a.contains(p2_42));
/// // the value is perpetuated as long as there is a nonempty set of
/// // pointer-keys associated with it
/// assert_eq!(a.get_val(p2_42).unwrap(), "42");
///
/// // We cannot use an invalidated pointer as a reference
/// assert_eq!(
///     a.insert_key(p1_42, "key3".to_owned()),
///     Err("key3".to_owned())
/// );
/// // We need to use an existing valid key
/// let p3_42 = a.insert_key(p2_42, "key3".to_owned()).unwrap();
/// assert_eq!(a.get_val(p3_42).unwrap(), "42");
///
/// let other42 = a.insert("test".to_owned(), "42".to_owned());
/// // note this is still a general `Arena`-like structure and not a hereditary
/// // set or map, so multiple of the same exact values can exist in different
/// // surjects.
/// assert!(!a.in_same_set(p0_42, other42).unwrap());
/// a.remove(other42).unwrap();
///
/// let p4_7 = a.insert("key4".to_owned(), "7".to_owned());
/// let p5_7 = a.insert_key(p4_7, "key5".to_owned()).unwrap();
///
/// assert_eq!(a.len_key_set(p0_42).unwrap().get(), 3);
/// assert_eq!(a.len_key_set(p4_7).unwrap().get(), 2);
///
/// // I know the order ahead of time because the arena is deterministic, but
/// // note that in general this will be completely unsorted with respect to
/// // keys or values.
/// let expected = [
///     (p0_42, "key0", "42"),
///     (p3_42, "key3", "42"),
///     (p2_42, "key2", "42"),
///     (p4_7, "key4", "7"),
///     (p5_7, "key5", "7"),
/// ];
/// // this iterator is not cloning the values, it is simply repeatedly
/// // indexing the values when multiple keys are associated with a single
/// // value
/// for (i, (p, key, val)) in a.iter().enumerate() {
///     assert_eq!(expected[i], (p, key.as_str(), val.as_str()));
/// }
///
/// let (removed_v, kept_p) = a.union(p0_42, p4_7).unwrap();
/// // One of the "7" or "42" values was removed from the arena,
/// // and the other remains in the arena. Suppose we want
/// // to take a custom union of the `String`s to go along
/// // with the union of the keys, we would do something like
/// *a.get_val_mut(kept_p).unwrap() = format!("{} + {}", a.get_val(kept_p).unwrap(), removed_v);
///
/// assert_eq!(a.len_key_set(p0_42).unwrap().get(), 5);
/// let expected = [
///     (p0_42, "key0", "42 + 7"),
///     (p3_42, "key3", "42 + 7"),
///     (p2_42, "key2", "42 + 7"),
///     (p4_7, "key4", "42 + 7"),
///     (p5_7, "key5", "42 + 7"),
/// ];
/// for (i, (p, key, val)) in a.iter().enumerate() {
///     assert_eq!(expected[i], (p, key.as_str(), val.as_str()));
/// }
///
/// // only upon removing the last key is the value is returned
/// // (or we could use the wholesale `remove`)
/// assert_eq!(a.remove_key(p4_7), Some(("key4".to_owned(), None)));
/// assert_eq!(a.remove_key(p0_42), Some(("key0".to_owned(), None)));
/// assert_eq!(a.remove_key(p3_42), Some(("key3".to_owned(), None)));
/// assert_eq!(a.remove_key(p5_7), Some(("key5".to_owned(), None)));
/// assert_eq!(
///     a.remove_key(p2_42),
///     Some(("key2".to_owned(), Some("42 + 7".to_owned())))
/// );
/// ```
pub struct SurjectArena<P: Ptr, K, V> {
    pub(crate) keys: ChainArena<P, Key<P, K>>,
    pub(crate) vals: Arena<PtrNoGen<P>, Val<V>>,
}

/// # Note
///
/// `Ptr`s in a `SurjectArena` follow the same validity rules as `Ptr`s in a
/// regular `Arena` (see the documentation on the main
/// `impl<P: Ptr, T> Arena<P, T>`). The validity of each `Ptr` is kept separate.
impl<P: Ptr, K, V> SurjectArena<P, K, V> {
    /// Used by tests
    #[doc(hidden)]
    pub fn _check_invariants(this: &Self) -> Result<(), &'static str> {
        // there should be exactly one key chain associated with each val
        let mut count = Arena::<PtrNoGen<P>, usize>::new();
        count.clone_from_with(&this.vals, |_, _| 0);
        for link in this.keys.vals() {
            match count.get_mut(link.t.p_val) {
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
            let mut c = *count.get(this.keys.get(p).unwrap().t.p_val).unwrap();
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
                        *count.get_mut(this.keys.get(p).unwrap().t.p_val).unwrap() = 0;
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

    /// Returns the total number of valid `Ptr`s, or equivalently the number of
    /// keys in the arena. `self.len_keys() >= self.len_vals()` is always
    /// true.
    pub fn len_keys(&self) -> usize {
        self.keys.len()
    }

    /// Returns the number of values, or equivalently the number of key sets in
    /// the arena
    pub fn len_vals(&self) -> usize {
        self.vals.len()
    }

    /// Returns the size of the set of keys pointing to the same value, with `p`
    /// being a `Ptr` to any one of those keys. Returns `None` if `p` is
    /// invalid.
    #[must_use]
    pub fn len_key_set(&self, p: P) -> Option<NonZeroUsize> {
        let p_val = self.keys.get(p)?.t.p_val;
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

    /// Follows [Arena::gen]
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

    /// Inserts a new key and associated value. Returns a `Ptr` to the key.
    pub fn insert(&mut self, k: K, v: V) -> P {
        let p_val = self.vals.insert(Val {
            v,
            key_count: NonZeroUsize::new(1).unwrap(),
        });
        self.keys.insert_new_cyclic(Key { k, p_val })
    }

    /// Inserts a surject into the arena, using the `K` and `V` returned by
    /// `create` for the new key and value. Returns a `Ptr` to the new key.
    /// `create` is given the the same `Ptr` that is returned, which is
    /// useful for initialization of immutable structures that need to reference
    /// themselves.
    pub fn insert_with<F: FnOnce(P) -> (K, V)>(&mut self, create_k_v: F) -> P {
        let mut res = P::invalid();
        self.vals.insert_with(|p_val| {
            let mut created_v = None;
            self.keys.insert_new_cyclic_with(|p| {
                res = p;
                let (k, v) = create_k_v(p);
                created_v = Some(v);
                Key { k, p_val }
            });
            Val {
                v: created_v.unwrap(),
                key_count: NonZeroUsize::new(1).unwrap(),
            }
        });
        res
    }

    /// Inserts a new key into the arena, associating it with the same key set
    /// that `p` is in (any `Ptr` from the valid key set can be used as a
    /// reference), and returns the new `Ptr` to the key. Returns `Err(k)`
    /// if `p` was invalid.
    pub fn insert_key(&mut self, p: P, k: K) -> Result<P, K> {
        let p_val = match self.keys.get(p) {
            None => return Err(k),
            Some(p) => p.t.p_val,
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
        if let Ok(p) = self.keys.insert((Some(p), None), Key { k, p_val }) {
            Ok(p)
        } else {
            unreachable!()
        }
    }

    /// The same as [SurjectArena::insert_key] except that the inserted `K` is
    /// created by `create_k`. The `Ptr` that will point to the new key is
    /// passed to `create_k`, and this `Ptr` is also returned. `create` is
    /// not called and `None` is returned if `p` is invalid.
    #[must_use]
    pub fn insert_key_with<F: FnOnce(P) -> K>(&mut self, p: P, create_k: F) -> Option<P> {
        let p_val = match self.keys.get(p) {
            None => return None,
            Some(p) => p.t.p_val,
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
        if let Some(p) = self.keys.insert_with((Some(p), None), |p_link| Key {
            k: create_k(p_link),
            p_val,
        }) {
            Some(p)
        } else {
            unreachable!()
        }
    }

    /// Returns if `p` is a valid `Ptr`
    pub fn contains(&self, p: P) -> bool {
        self.keys.contains(p)
    }

    /// Returns if `p0` and `p1` point to keys in the same key set
    #[must_use]
    pub fn in_same_set(&self, p0: P, p1: P) -> Option<bool> {
        Some(self.keys.get(p0)?.t.p_val == self.keys.get(p1)?.t.p_val)
    }

    /// Returns a reference to the key pointed to by `p`
    #[must_use]
    pub fn get_key(&self, p: P) -> Option<&K> {
        self.keys.get(p).as_ref().map(|link| &link.t.k)
    }

    /// Returns a reference to the value associated with the key pointed to by
    /// `p`
    #[must_use]
    pub fn get_val(&self, p: P) -> Option<&V> {
        let p_val = self.keys.get(p)?.p_val;
        Some(&self.vals.get(p_val).unwrap().v)
    }

    /// Returns a reference to the key-value pair pointed to by `p`
    #[must_use]
    pub fn get(&self, p: P) -> Option<(&K, &V)> {
        let link = self.keys.get(p)?;
        Some((&link.t.k, &self.vals.get(link.t.p_val).unwrap().v))
    }

    /// Returns a mutable reference to the value pointed to by `p`
    #[must_use]
    pub fn get_key_mut(&mut self, p: P) -> Option<&mut K> {
        if let Some(link) = self.keys.get_mut(p) {
            Some(&mut link.t.k)
        } else {
            None
        }
    }

    /// Returns a mutable reference to the value associated with the key pointed
    /// to by `p`
    #[must_use]
    pub fn get_val_mut(&mut self, p: P) -> Option<&mut V> {
        let p_val = self.keys.get(p)?.t.p_val;
        Some(&mut self.vals.get_mut(p_val).unwrap().v)
    }

    /// Returns a mutable reference to the key-value pair pointed to by `p`
    #[must_use]
    pub fn get_mut(&mut self, p: P) -> Option<(&mut K, &mut V)> {
        let key = self.keys.get_mut(p)?.t;
        Some((&mut key.k, &mut self.vals.get_mut(key.p_val).unwrap().v))
    }

    /// Gets two `&mut K` references pointed to by `p0` and `p1`. If
    /// `p0 == p1` or a pointer is invalid, `None` is returned.
    #[must_use]
    pub fn get2_key_mut(&mut self, p0: P, p1: P) -> Option<(&mut K, &mut K)> {
        match self.keys.get2_mut(p0, p1) {
            Some((link0, link1)) => Some((&mut link0.t.k, &mut link1.t.k)),
            None => None,
        }
    }

    /// Gets two `&mut V` references pointed to by `p0` and `p1`. If
    /// `self.in_same_set(p0, p1)` or a pointer is invalid, `None` is
    /// returned.
    #[must_use]
    pub fn get2_val_mut(&mut self, p0: P, p1: P) -> Option<(&mut V, &mut V)> {
        let p_val0 = self.keys.get(p0)?.t.p_val;
        let p_val1 = self.keys.get(p1)?.t.p_val;
        match self.vals.get2_mut(p_val0, p_val1) {
            Some((val0, val1)) => Some((&mut val0.v, &mut val1.v)),
            None => None,
        }
    }

    /// Gets two mutable references to the key-value pairs pointed to by `p0`
    /// and `p1`. If `self.in_same_set(p0, p1)` or a pointer is invalid,
    /// `None` is returned.
    #[must_use]
    #[allow(clippy::type_complexity)]
    pub fn get2_mut(&mut self, p0: P, p1: P) -> Option<((&mut K, &mut V), (&mut K, &mut V))> {
        match self.keys.get2_mut(p0, p1) {
            Some((link0, link1)) => {
                let key0 = link0.t;
                let key1 = link1.t;
                match self.vals.get2_mut(key0.p_val, key1.p_val) {
                    Some((val0, val1)) => {
                        Some(((&mut key0.k, &mut val0.v), (&mut key1.k, &mut val1.v)))
                    }
                    None => None,
                }
            }
            None => None,
        }
    }

    /// Takes the union of two key sets, of which `p0` points to a key in one
    /// set and `p1` points to a key in the other set. If
    /// `self.len_key_set(p0) < self.len_key_set(p1)`, then the value
    /// associated with `p0` is removed and returned in a tuple with `p1`,
    /// and the key set of `p0` is changed to point to the value of `p1`'s
    /// key set. If `self.len_key_set(p0) >= self.len_key_set(p1)`, the
    /// value pointed to by `p1` is removed and returned in a tuple with
    /// `p0`, and the key set of `p1` is changed to point to the value of
    /// `p0`'s key set. Returns `None` if `self.in_same_set(p0, p1)`.
    ///
    /// # Note
    ///
    /// No `Ptr`s are invalidated even though a value is removed, all that
    /// happens is both key sets are redirected point to a common value.
    ///
    /// This function is defined in this way to guarantee a `O(n log n)` cost
    /// for performing repeated unions in any order on a given starting arena.
    /// If the two `V`s are some kind of additive structure that also need to
    /// have their union taken, then the contents of the `V` in the return tuple
    /// can be transferred to the value pointed to by the `P` also in the
    /// return tuple. This way, users do not actually need to consider key set
    /// sizes explicitly.
    ///
    /// We purposely reverse the typical order from `(P, V)` to `(V, P)`
    /// to give a visual that the returned things were not pointing to each
    /// other.
    #[must_use]
    pub fn union(&mut self, mut p0: P, mut p1: P) -> Option<(V, P)> {
        let mut p_val0 = self.keys.get(p0)?.t.p_val;
        let mut p_val1 = self.keys.get(p1)?.t.p_val;
        if p_val0 == p_val1 {
            // corresponds to same set
            return None
        }
        let len0 = self.vals.get(p_val0).unwrap().key_count.get();
        let len1 = self.vals.get(p_val1).unwrap().key_count.get();
        if len0 < len1 {
            mem::swap(&mut p_val0, &mut p_val1);
            mem::swap(&mut p0, &mut p1);
        }
        // overwrite the `PVal`s in the smaller chain
        let mut tmp = p1;
        loop {
            self.keys.get_mut(tmp).unwrap().t.p_val = p_val0;
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
        self.vals.get_mut(p_val0).unwrap().key_count =
            NonZeroUsize::new(len0.wrapping_add(len1)).unwrap();
        Some((self.vals.remove_internal(p_val1, false).unwrap().v, p0))
    }

    /// Removes the key pointed to by `p`. If there were other keys still in the
    /// key set, the value is not removed and `Some((key, None))` is
    /// returned. If `p` was the last key in the key set, then the value is
    /// removed and returned like `Some((key, Some(val)))`. Returns
    /// `None` if `p` is not valid.
    #[must_use]
    pub fn remove_key(&mut self, p: P) -> Option<(K, Option<V>)> {
        let key = self.keys.remove(p)?.t;
        let p_val = key.p_val;
        let k = key.k;
        let key_count = self.vals.get(p_val).unwrap().key_count.get();
        if key_count == 1 {
            // last key, remove the value
            Some((k, Some(self.vals.remove(p_val).unwrap().v)))
        } else {
            // decrement the key count
            self.vals.get_mut(p_val).unwrap().key_count =
                NonZeroUsize::new(key_count.wrapping_sub(1)).unwrap();
            Some((k, None))
        }
    }

    /// Removes the entire key set and value cheaply, returning the value. `p`
    /// can point to any key from the key set. Returns `None` if `p` is invalid.
    #[must_use]
    pub fn remove(&mut self, p: P) -> Option<V> {
        let p_val = self.keys.get(p)?.t.p_val;
        self.keys.remove_cyclic_chain_internal(p, true);
        Some(self.vals.remove(p_val).unwrap().v)
    }

    /// Invalidates the `Ptr` `p` (no other `Ptr`s to keys in the key set are
    /// invalidated), returning a new valid `Ptr`. Returns `None` if `p` is
    /// not valid.
    #[must_use]
    pub fn invalidate(&mut self, p: P) -> Option<P> {
        // the chain arena fixes interlinks
        self.keys.invalidate(p)
    }

    /// Swaps the `K` keys pointed to by `Ptr`s `p0` and `p1` and keeps the
    /// generation counters as-is. Note that key-value associations are swapped
    /// such that if `p0` and `p1` point to two different key sets, then the
    /// first key becomes associated with the value of the second key and vice
    /// versa. If `p0` and `p1` point to the same key set, no association
    /// changes occur. If `p0 == p1`, then nothing occurs. Returns `None` if
    /// `p0` or `p1` are invalid.
    #[must_use]
    pub fn swap_keys(&mut self, p0: P, p1: P) -> Option<()> {
        if p0 == p1 {
            // still need to check for containment
            if self.contains(p0) {
                Some(())
            } else {
                None
            }
        } else {
            let (lhs, rhs) = self.keys.get2_mut(p0, p1)?;
            // be careful to swap only the inner `K` values and not the `p_val`s
            mem::swap(&mut lhs.t.k, &mut rhs.t.k);
            Some(())
        }
    }

    /// Swaps the `V` values pointed to by `Ptr`s `p0` and `p1` and keeps the
    /// generation counters as-is. If `p0` and `p1` point to keys in the same
    /// key set, then nothing occurs. Returns `None` if `p0` or `p1` are
    /// invalid.
    #[must_use]
    pub fn swap_vals(&mut self, p0: P, p1: P) -> Option<()> {
        let p_val0 = self.keys.get(p0)?.t.p_val;
        let p_val1 = self.keys.get(p1)?.t.p_val;
        if p_val0 != p_val1 {
            // we only want to swap the `V` and not the ref counts
            let (lhs, rhs) = self.vals.get2_mut(p_val0, p_val1).unwrap();
            mem::swap(&mut lhs.v, &mut rhs.v);
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

// we can't implement `Index` because the format would force `&(&K, &V)` which
// causes many further problems

impl<P: Ptr, K: Debug, V: Debug> Debug for SurjectArena<P, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<P: Ptr, K: Clone, V: Clone> Clone for SurjectArena<P, K, V> {
    fn clone(&self) -> Self {
        Self {
            keys: self.keys.clone(),
            vals: self.vals.clone(),
        }
    }
}

impl<PLink: Ptr, K, V> Default for SurjectArena<PLink, K, V> {
    fn default() -> Self {
        Self::new()
    }
}
