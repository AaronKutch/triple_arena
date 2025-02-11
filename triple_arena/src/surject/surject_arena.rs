use alloc::fmt;
use core::{mem, num::NonZeroUsize};

use fmt::Debug;

use crate::{
    arena::InternalEntry,
    utils::{ChainNoGenArena, LinkNoGen, PtrInx, PtrNoGen},
    Advancer, Arena, ChainArena, Ptr,
};

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
    pub(crate) key_count: NonZeroUsize,
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
    pub(crate) keys: ChainNoGenArena<P, Key<P, K>>,
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
        // needs to be done because of manual `InternalEntry` handling
        ChainNoGenArena::_check_invariants(&this.keys)?;
        Arena::_check_invariants(&this.vals)?;
        Self::_check_surjects(this)?;
        Ok(())
    }

    #[doc(hidden)]
    pub fn _check_surjects(this: &Self) -> Result<(), &'static str> {
        // there should be exactly one key chain associated with each val
        let mut count = Arena::<PtrNoGen<P>, usize>::new();
        count.clone_from_with(&this.vals, |_, _| 0);
        for link in this.keys.vals() {
            match count.get_mut(link.t.p_val) {
                Some(len) => *len = len.checked_add(1).unwrap(),
                None => return Err("key points to nonexistent val"),
            }
        }
        for (p_val, n) in &count {
            if this.vals.get(p_val).unwrap().key_count.get() != *n {
                return Err("key count does not match actual")
            }
        }

        let mut adv = this.keys.advancer();
        while let Some(p) = adv.advance(&this.keys) {
            let mut c = *count.get(this.keys.get(p).unwrap().p_val).unwrap();
            if c != 0 {
                // upon encountering a nonzero count for the first time, we follow the chain and
                // count down, and if we reach back to the beginning (verifying cyclic chain)
                // and reach a count of zero, then we know that the chain encountered all the
                // needed keys. Subsequent encounters with the rest of the chain is ignored
                // because the count is zeroed afterwards.
                let mut tmp = p.inx();
                loop {
                    if c == 0 {
                        return Err("did not reach end of key chain in expected time")
                    }
                    c = c.checked_sub(1).unwrap();
                    let (_, link) = this.keys.get_no_gen(tmp).unwrap();
                    if let Some(next) = link.next() {
                        tmp = next;
                    } else {
                        return Err("key chain is not cyclic")
                    }
                    // have the test after the match so that we check for single node cyclics
                    if tmp == p.inx() {
                        if c != 0 {
                            return Err("key chain did not have all keys associated with value")
                        }
                        *count.get_mut(this.keys.get(p).unwrap().p_val).unwrap() = 0;
                        break
                    }
                }
            }
        }
        Ok(())
    }

    pub fn new() -> Self {
        Self {
            keys: ChainNoGenArena::new(),
            vals: Arena::new(),
        }
    }

    /// Creates the new arena with capacity for at least `capacity_keys` keys
    /// and `capacity_vals` values
    pub fn with_capacity(capacity_keys: usize, capacity_vals: usize) -> Self {
        let mut res = Self::new();
        res.reserve_keys(capacity_keys);
        res.reserve_vals(capacity_vals);
        res
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
        let p_val = self.keys.get(p)?.p_val;
        Some(self.vals.get_inx_unwrap(p_val.inx()).key_count)
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

    /// Follows [Arena::generation]
    pub fn generation(&self) -> P::Gen {
        self.keys.generation()
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
            Some(key) => key.p_val,
        };
        self.vals[p_val].key_count = NonZeroUsize::new(
            self.vals
                .get_inx_unwrap(p_val.inx())
                .key_count
                .get()
                .wrapping_add(1),
        )
        .unwrap();
        if let Ok(p) = self.keys.insert((Some(p.inx()), None), Key { k, p_val }) {
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
            Some(key) => key.p_val,
        };
        self.vals[p_val].key_count = NonZeroUsize::new(
            self.vals
                .get_inx_unwrap(p_val.inx())
                .key_count
                .get()
                .wrapping_add(1),
        )
        .unwrap();
        if let Some(p) = self.keys.insert_with((Some(p.inx()), None), |p_link| Key {
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
        Some(self.keys.get(p0)?.p_val == self.keys.get(p1)?.p_val)
    }

    /// Returns a reference to the key pointed to by `p`
    #[must_use]
    pub fn get_key(&self, p: P) -> Option<&K> {
        self.keys.get(p).as_ref().map(|key| &key.k)
    }

    /// Returns a reference to the value associated with the key pointed to by
    /// `p`
    #[must_use]
    pub fn get_val(&self, p: P) -> Option<&V> {
        let p_val = self.keys.get(p)?.p_val;
        Some(&self.vals.get_inx_unwrap(p_val.inx()).v)
    }

    /// Returns a reference to the key-value pair pointed to by `p`
    #[must_use]
    pub fn get(&self, p: P) -> Option<(&K, &V)> {
        let key = self.keys.get(p)?;
        Some((&key.k, &self.vals.get_inx_unwrap(key.p_val.inx()).v))
    }

    /// Returns a mutable reference to the value pointed to by `p`
    #[must_use]
    pub fn get_key_mut(&mut self, p: P) -> Option<&mut K> {
        if let Some(key) = self.keys.get_mut(p) {
            Some(&mut key.k)
        } else {
            None
        }
    }

    /// Returns a mutable reference to the value associated with the key pointed
    /// to by `p`
    #[must_use]
    pub fn get_val_mut(&mut self, p: P) -> Option<&mut V> {
        let p_val = self.keys.get(p)?.p_val;
        Some(&mut self.vals.get_inx_mut_unwrap(p_val.inx()).v)
    }

    /// Returns a mutable reference to the key-value pair pointed to by `p`
    #[must_use]
    pub fn get_mut(&mut self, p: P) -> Option<(&mut K, &mut V)> {
        let key = self.keys.get_mut(p)?;
        Some((
            &mut key.k,
            &mut self.vals.get_inx_mut_unwrap(key.p_val.inx()).v,
        ))
    }

    /// Gets two `&mut K` references pointed to by `p0` and `p1`. If
    /// `p0 == p1` or a pointer is invalid, `None` is returned.
    #[must_use]
    pub fn get2_key_mut(&mut self, p0: P, p1: P) -> Option<(&mut K, &mut K)> {
        match self.keys.get2_mut(p0, p1) {
            Some((key0, key1)) => Some((&mut key0.k, &mut key1.k)),
            None => None,
        }
    }

    /// Gets two `&mut V` references pointed to by `p0` and `p1`. If
    /// `self.in_same_set(p0, p1)` or a pointer is invalid, `None` is
    /// returned.
    #[must_use]
    pub fn get2_val_mut(&mut self, p0: P, p1: P) -> Option<(&mut V, &mut V)> {
        let p_val0 = self.keys.get(p0)?.p_val;
        let p_val1 = self.keys.get(p1)?.p_val;
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
            Some((key0, key1)) => match self.vals.get2_mut(key0.p_val, key1.p_val) {
                Some((val0, val1)) => {
                    Some(((&mut key0.k, &mut val0.v), (&mut key1.k, &mut val1.v)))
                }
                None => None,
            },
            None => None,
        }
    }

    /// Returns the generation associated with `p` and a `LinkNoGen<P, &K>`, the
    /// interlinks of which point to other keys in the key set. The key set is a
    /// cyclic chain of `LinkNoGen`s.
    #[must_use]
    pub fn get_link_no_gen(&self, p: P::Inx) -> Option<(P::Gen, LinkNoGen<P, &K>)> {
        self.keys
            .get_no_gen(p)
            .map(|(p, link)| (p, LinkNoGen::new(link.prev_next(), &link.t.k)))
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
        let mut p_val0 = self.keys.get(p0)?.p_val;
        let mut p_val1 = self.keys.get(p1)?.p_val;
        if p_val0 == p_val1 {
            // corresponds to same set
            return None
        }
        let len0 = self.vals.get_inx_unwrap(p_val0.inx()).key_count.get();
        let len1 = self.vals.get_inx_unwrap(p_val1.inx()).key_count.get();
        if len0 < len1 {
            mem::swap(&mut p_val0, &mut p_val1);
            mem::swap(&mut p0, &mut p1);
        }
        // overwrite the `PVal`s in the smaller chain
        let mut tmp = p1.inx();
        loop {
            self.keys.get_inx_mut_unwrap_t(tmp).p_val = p_val0;
            tmp = self.keys.get_inx_unwrap(tmp).next().unwrap();
            if tmp == p1.inx() {
                break
            }
        }
        // combine chains cheaply, this is why they need to be cyclic because exchanging
        // two interlinks anywhere between the chains results in a combined single
        // cyclic chain.
        self.keys.exchange_next(p0, p1).unwrap();
        // it is be impossible to overflow this, it would mean that we have already
        // inserted `usize + 1` elements
        self.vals.get_inx_mut_unwrap(p_val0.inx()).key_count =
            NonZeroUsize::new(len0.wrapping_add(len1)).unwrap();
        Some((
            self.vals.remove_internal_inx_unwrap(p_val1.inx(), false).v,
            p0,
        ))
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
        let key_count = self.vals.get_inx_unwrap(p_val.inx()).key_count.get();
        if key_count == 1 {
            // last key, remove the value
            Some((k, Some(self.vals.remove(p_val).unwrap().v)))
        } else {
            // decrement the key count
            self.vals.get_inx_mut_unwrap(p_val.inx()).key_count =
                NonZeroUsize::new(key_count.wrapping_sub(1)).unwrap();
            Some((k, None))
        }
    }

    /// Removes the entire key set and value cheaply, returning the value. `p`
    /// can point to any key from the key set. Returns `None` if `p` is invalid.
    #[must_use]
    pub fn remove(&mut self, p: P) -> Option<V> {
        let p_val = self.keys.get(p)?.p_val;
        self.keys.remove_cyclic_chain_internal(p.inx(), true);
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
            mem::swap(&mut lhs.k, &mut rhs.k);
            Some(())
        }
    }

    /// Swaps the `V` values pointed to by `Ptr`s `p0` and `p1` and keeps the
    /// generation counters as-is. If `p0` and `p1` point to keys in the same
    /// key set, then nothing occurs. Returns `None` if `p0` or `p1` are
    /// invalid.
    #[must_use]
    pub fn swap_vals(&mut self, p0: P, p1: P) -> Option<()> {
        let p_val0 = self.keys.get(p0)?.p_val;
        let p_val1 = self.keys.get(p1)?.p_val;
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

    /// Compresses the arena by moving around entries to be able to shrink the
    /// capacities of the keys and values down to their respective lengths. All
    /// surject relations remain, but all `Ptr`s are invalidated. New `Ptr`s
    /// to the entries can be found again by iterators and advancers.
    /// Notably, when iterating or advancing after a call to this type of
    /// function or during `map`ping with
    /// [SurjectArena::compress_and_shrink_with], whole surjects at a time
    /// are advanced through without discontinuity. Additionally, cache locality
    /// is improved by keys within the same surject being moved close together
    /// in memory.
    pub fn compress_and_shrink(&mut self) {
        self.compress_and_shrink_with(|_, _, _, _| ())
    }

    /// The same as [SurjectArena::compress_and_shrink] except that `map` is run
    /// on every `(P, &mut K, &mut V, P)` with the first `P` being the old `Ptr`
    /// and the last `P` being the new `Ptr`.
    pub fn compress_and_shrink_with<F: FnMut(P, &mut K, &mut V, P)>(&mut self, mut map: F) {
        // we run into the problem of not being able to lookup keys from values, so we
        // do a special kind of manual compression on the values
        let mut first_unallocated = None;
        for i in self.vals.m.nziter() {
            if matches!(
                self.vals.m_get(P::Inx::new(i)).unwrap(),
                InternalEntry::Free(_)
            ) {
                first_unallocated = Some(i);
                break
            }
        }

        // first compress the keys so that their cache locality is improved
        let mut p_val_last = None;
        let mut new_p_val = None;
        self.keys.compress_and_shrink_with(|p, key, q| {
            let p_val = key.p_val;
            if Some(p_val) != p_val_last {
                let mut new_change = false;
                if let Some(i_unallocated) = first_unallocated {
                    let i = P::Inx::get(p_val.inx());
                    if i > i_unallocated {
                        // move it into the unallocated spot
                        self.vals.raw_entry_swap_special(i_unallocated, i);
                        // change all `p_val`s of the surject
                        new_p_val = Some(P::Inx::new(i_unallocated));
                        new_change = true;
                        // get the next unallocated index
                        let mut j = i_unallocated.get().wrapping_add(1);
                        loop {
                            if j > self.vals.m.len() {
                                first_unallocated = None;
                                break
                            }
                            let j_nz = NonZeroUsize::new(j).unwrap();
                            if matches!(
                                self.vals.m_get(P::Inx::new(j_nz)).unwrap(),
                                InternalEntry::Free(_)
                            ) {
                                first_unallocated = Some(j_nz);
                                break
                            }
                            j = j.wrapping_add(1);
                        }
                    }
                }
                if !new_change {
                    // the `p_val` of this new surject we are encountering does not need to be
                    // changed
                    new_p_val = None;
                }
                p_val_last = Some(p_val);
            }
            if let Some(new_p_val) = new_p_val {
                key.p_val = Ptr::_from_raw(new_p_val, ());
            }
            map(
                p,
                &mut key.k,
                &mut self.vals.get_inx_mut_unwrap(key.p_val.inx()).v,
                q,
            )
        });
        // important: remove all free entries, set freelist root to `None`, and shrink
        // to fit `self.vals`, completes the compression and fixes the likely broken
        // freelist
        while let Some(i) = NonZeroUsize::new(self.vals.m.len()) {
            if let Some(InternalEntry::Free(_)) = self.vals.m.get(i) {
                self.vals.m.pop().unwrap();
            } else {
                break
            }
        }
        self.vals.freelist_root = None;
        self.vals.m.shrink_to_fit();
    }

    /// Has the same properties of [Arena::clone_from_with]
    pub fn clone_from_with<
        K1: Ord,
        V1,
        F0: FnMut(P, &K1) -> K,
        F1: FnMut(NonZeroUsize, &V1) -> V,
    >(
        &mut self,
        source: &SurjectArena<P, K1, V1>,
        mut map_key: F0,
        mut map_val: F1,
    ) {
        self.keys.clone_from_with(&source.keys, |p, link| {
            let k = map_key(p, &link.t.k);
            Key {
                k,
                p_val: Ptr::_from_raw(p.inx(), ()),
            }
        });
        self.vals.clone_from_with(&source.vals, |_, val| {
            let v = map_val(val.key_count, &val.v);
            Val {
                v,
                key_count: val.key_count,
            }
        });
    }

    /// Overwrites `chain_arena` (dropping all preexisting `T`, overwriting the
    /// generation counter, and reusing capacity) with the `Ptr` mapping of
    /// `self`, with groups of keys preserved as cyclical chains.
    pub fn clone_keys_to_chain_arena<T, F: FnMut(P, &K) -> T>(
        &self,
        chain_arena: &mut ChainArena<P, T>,
        mut map: F,
    ) {
        self.keys
            .clone_to_chain_arena(chain_arena, |p, key| map(p, &key.k))
    }

    /// Overwrites `chain_arena` (dropping all preexisting `T`, overwriting the
    /// generation counter, and reusing capacity) with the `Ptr` mapping of
    /// `self`, with groups of keys preserved as cyclical chains.
    pub fn clone_keys_to_chain_no_gen_arena<T, F: FnMut(P, &K) -> T>(
        &self,
        chain_arena: &mut ChainNoGenArena<P, T>,
        mut map: F,
    ) {
        chain_arena.clone_from_with(&self.keys, |p, link| map(p, &link.t.k))
    }

    /// Overwrites `arena` (dropping all preexisting `T` and relations,
    /// overwriting the generation counter, and reusing capacity) with the
    /// `Ptr` mapping of `self`.
    pub fn clone_keys_to_arena<T, F: FnMut(P, &K) -> T>(
        &self,
        arena: &mut Arena<P, T>,
        mut map: F,
    ) {
        self.keys.clone_to_arena(arena, |p, link| map(p, &link.t.k))
    }
}

// we can't implement `Index` because the format would force `&(&K, &V)` which
// causes many further problems

impl<P: Ptr, K: Debug, V: Debug> Debug for SurjectArena<P, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

/// Implemented if `K: Clone` and `V: Clone`.
impl<P: Ptr, K: Clone, V: Clone> Clone for SurjectArena<P, K, V> {
    /// Has the `Ptr` preserving properties of [Arena::clone]
    fn clone(&self) -> Self {
        Self {
            keys: self.keys.clone(),
            vals: self.vals.clone(),
        }
    }

    /// Has the `Ptr` and capacity preserving properties of [Arena::clone_from]
    fn clone_from(&mut self, source: &Self) {
        self.keys.clone_from(&source.keys);
        self.vals.clone_from(&source.vals);
    }
}

impl<P: Ptr, K, V> Default for SurjectArena<P, K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P: Ptr, K: PartialEq, V: PartialEq> PartialEq<SurjectArena<P, K, V>>
    for SurjectArena<P, K, V>
{
    /// Checks if all `(P, K, V)` pairs are equal. This is sensitive to
    /// `Ptr` indexes, generation counters, and some hidden key set relations,
    /// but does not compare arena capacities, `self.generation()`, or hidden
    /// value pointers.
    fn eq(&self, other: &SurjectArena<P, K, V>) -> bool {
        // first the keys
        let mut adv0 = self.advancer();
        let mut adv1 = other.advancer();
        while let Some(p0) = adv0.advance(self) {
            if let Some(p1) = adv1.advance(other) {
                if p0 != p1 {
                    return false
                }
                let key0 = self.keys.get_inx_unwrap(p0.inx());
                let key1 = self.keys.get_inx_unwrap(p1.inx());
                // make sure not to depend on `p_val`
                if key0.prev_next() != key1.prev_next() {
                    return false
                }
                if key0.t.k != key1.t.k {
                    return false
                }
                // the surject composition is implicitly checked by the `prev_next`
                // checks
                if self.vals.get_inx_unwrap(key0.t.p_val.inx()).v
                    != other.vals.get_inx_unwrap(key1.t.p_val.inx()).v
                {
                    return false
                }
            } else {
                return false
            }
        }
        adv1.advance(other).is_none()
    }
}

impl<P: Ptr, K: Eq, V: Eq> Eq for SurjectArena<P, K, V> {}
