use core::{fmt, mem, num::NonZeroUsize};

use fmt::Debug;

use crate::{
    Arena, ChainArena, InvalidationOption, InvalidationResult, LinkInsertKind, LinkNoGen,
    arena::ArenaDirectInsertEntryTrait,
    errors::{AllocError, ChainInsertionError, NotWithinCapacityError, ReallocationError},
    traits::{
        Advancer, ArenaCloneFromWith, ArenaDirectInsertTrait, ArenaInsertEntryTrait,
        ArenaInsertTrait, ArenaTrait, ChainArenaTrait, Ptr,
    },
    utils::{
        PtrNoGen,
        traits::{ArenaBacking, PtrInx},
    },
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
/// use triple_arena::{SurjectArena, errors::ChainInsertionError, ptr_struct};
///
/// ptr_struct!(P0);
/// let mut a: SurjectArena<P0, String, String> = SurjectArena::new();
///
/// // There must be at least one key associated with each value
/// let p0_42 = a.insert("key0".to_owned(), "42".to_owned());
/// // If we want new keys to be associated with the same key set pointing to
/// // "42", then instead of calling `insert_val` we call `insert_key`
/// let p1_42 = a.insert_key(p0_42, "key1".to_owned());
/// // We could use either `p0_42` or `p1_42` as our reference to get
/// // associated with the same key set; any valid pointer in the preexisting
/// // set can be used with the same `O(1)` computational complexity incurred.
/// let p2_42 = a.insert_key(p0_42, "key2".to_owned());
///
/// assert_eq!(a.get_key(p0_42).unwrap(), "key0");
/// assert_eq!(a.get_key(p1_42).unwrap(), "key1");
/// assert_eq!(a.get_key(p2_42).unwrap(), "key2");
/// assert_eq!(a.get_val(p0_42).unwrap(), "42");
/// assert_eq!(a.get_val(p1_42).unwrap(), "42");
/// assert_eq!(a.get_val(p2_42).unwrap(), "42");
///
/// assert_eq!(a.remove_key(p1_42).allow(), Some(("key1".to_owned(), None)));
/// assert!(a.contains(p0_42));
/// assert!(!a.contains(p1_42));
/// assert!(a.contains(p2_42));
/// // the value is perpetuated as long as there is a nonempty set of
/// // pointer-keys associated with it
/// assert_eq!(a.get_val(p2_42).unwrap(), "42");
///
/// // We cannot use an invalidated pointer as a reference
/// assert_eq!(
///     a.insert_key_reallocating(p1_42, "key3".to_owned()),
///     Err(ChainInsertionError::FailedLinkRequirement)
/// );
/// // We need to use an existing valid key
/// let p3_42 = a.insert_key(p2_42, "key3".to_owned());
/// assert_eq!(a.get_val(p3_42).unwrap(), "42");
///
/// let other42 = a.insert("test".to_owned(), "42".to_owned());
/// // note this is still a general `Arena`-like structure and not a hereditary
/// // set or map, so multiple of the same exact values can exist in different
/// // surjects.
/// assert!(!a.in_same_set(p0_42, other42).unwrap());
/// a.remove_surject(other42).allow().unwrap();
///
/// let p4_7 = a.insert("key4".to_owned(), "7".to_owned());
/// let p5_7 = a.insert_key(p4_7, "key5".to_owned());
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
/// assert_eq!(a.remove_key(p4_7).allow(), Some(("key4".to_owned(), None)));
/// assert_eq!(a.remove_key(p0_42).allow(), Some(("key0".to_owned(), None)));
/// assert_eq!(a.remove_key(p3_42).allow(), Some(("key3".to_owned(), None)));
/// assert_eq!(a.remove_key(p5_7).allow(), Some(("key5".to_owned(), None)));
/// assert_eq!(
///     a.remove_key(p2_42).allow(),
///     Some(("key2".to_owned(), Some("42 + 7".to_owned())))
/// );
/// ```
pub struct SurjectArena<
    P: Ptr,
    K,
    V,
    #[cfg(feature = "alloc")] B: ArenaBacking = crate::HeapBacking,
    #[cfg(not(feature = "alloc"))] B: ArenaBacking,
> {
    pub(crate) keys: ChainArena<P, Key<P, K>, B>,
    pub(crate) vals: Arena<PtrNoGen<P>, Val<V>, B>,
}

// REF(insertion_idempotency)

/// See [ArenaInsertTrait]
pub struct SurjectArenaInsertEntry<'a, P: Ptr, K, V, B: ArenaBacking> {
    this: &'a mut SurjectArena<P, K, V, B>,
    p: P,
}

impl<'a, P: Ptr, K, V, B: ArenaBacking> SurjectArenaInsertEntry<'a, P, K, V, B> {
    pub fn ptr(&self) -> P {
        self.p
    }

    pub fn insert(self, k: K, v: V) {
        let p_val = self.this.vals.insert(Val {
            v,
            key_count: NonZeroUsize::new(1).unwrap(),
        });
        self.this
            .keys
            .insert(LinkInsertKind::SingleLinkCyclic, Key { k, p_val });
    }
}

/// See [ArenaInsertTrait]
pub struct SurjectArenaInsertKeyEntry<'a, P: Ptr, K, V, B: ArenaBacking> {
    this: &'a mut SurjectArena<P, K, V, B>,
    p_target: P::Inx,
    p_new: P,
}

impl<'a, P: Ptr, K, V, B: ArenaBacking> SurjectArenaInsertKeyEntry<'a, P, K, V, B> {
    /// Returns the `P` that the newly inserted key will be associated with, and
    /// not the `ptr_in_target_set`
    pub fn ptr(&self) -> P {
        self.p_new
    }

    pub fn insert(self, k: K) {
        let this = self.this;
        let p_val = this.keys.get_inx_mut_unwrap(self.p_target).p_val;
        let key_count = &mut this.vals.get_inx_mut_unwrap(p_val.inx()).key_count;
        *key_count = key_count.checked_add(1).unwrap();
        this.keys
            .insert(LinkInsertKind::NextToInx(self.p_target), Key { k, p_val });
    }
}

/// # Note
///
/// `Ptr`s in a `SurjectArena` follow the same validity rules as `Ptr`s in a
/// regular `Arena` (see the documentation on the main
/// `impl<P: Ptr, T> Arena<P, T>`). The validity of each `Ptr` is kept separate.
impl<P: Ptr, K, V, B: ArenaBacking> SurjectArena<P, K, V, B> {
    /// Used by tests
    #[doc(hidden)]
    pub fn _check_invariants(this: &Self) -> Result<(), &'static str> {
        // needs to be done because of manual `ArenaSlot` handling
        ChainArena::_check_invariants(&this.keys)?;
        Arena::_check_invariants(&this.vals)?;
        Self::_check_surjects(this)?;
        Ok(())
    }

    #[doc(hidden)]
    pub fn _check_surjects(this: &Self) -> Result<(), &'static str> {
        // there should be exactly one key chain associated with each val
        let mut count = Arena::<PtrNoGen<P>, usize, B>::new();
        count.clone_from_with(&this.vals, |_, _| 0).unwrap();
        for key in this.keys.vals() {
            match count.get_mut(key.p_val) {
                Some(len) => *len = len.checked_add(1).unwrap(),
                None => return Err("key points to nonexistent val"),
            }
        }
        for (p_val, n) in &count {
            if this.vals.get(p_val).unwrap().key_count.get() != *n {
                return Err("key count does not match actual");
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
                        return Err("did not reach end of key chain in expected time");
                    }
                    c = c.checked_sub(1).unwrap();
                    let (_, link) = this.keys.get_inx_link_no_gen(tmp).unwrap();
                    if let Some(next) = link.next() {
                        tmp = next;
                    } else {
                        return Err("key chain is not cyclic");
                    }
                    // have the test after the match so that we check for single node cyclics
                    if tmp == p.inx() {
                        if c != 0 {
                            return Err("key chain did not have all keys associated with value");
                        }
                        *count.get_mut(this.keys.get(p).unwrap().p_val).unwrap() = 0;
                        break;
                    }
                }
            }
        }
        Ok(())
    }

    /// Creates an empty surjection arena, which may have any capacity of keys
    /// and any capacity of values to start with
    pub fn new() -> Self {
        Self {
            keys: ChainArena::new(),
            vals: Arena::new(),
        }
    }

    /// See [ArenaTrait::with_min_capacity], this has separate capacities for
    /// the keys and vals
    pub fn with_min_capacity(
        min_capacity_keys: usize,
        min_capacity_vals: usize,
    ) -> Result<Self, AllocError> {
        Ok(Self {
            keys: ChainArena::with_min_capacity(min_capacity_keys)?,
            vals: Arena::with_min_capacity(min_capacity_vals)?,
        })
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

    /// Returns the max key capacity of the arena. See
    /// [ArenaTrait::max_capacity].
    pub fn max_capacity_keys(&self) -> Option<usize> {
        self.keys.max_capacity()
    }

    /// Returns the max value capacity of the arena
    pub fn max_capacity_vals(&self) -> Option<usize> {
        self.vals.max_capacity()
    }

    /// Follows [Arena::generation]
    pub fn generation(&self) -> P::Gen {
        self.keys.generation()
    }

    /// Follows [Arena::set_generation]
    pub fn set_generation(&mut self, new_gen: P::Gen) {
        self.keys.set_generation(new_gen)
    }

    /// Follows [Arena::inc_generation]
    pub fn inc_generation(&mut self) -> InvalidationOption<()> {
        self.keys.inc_generation()
    }

    /// Follows [ArenaTrait::reallocate_min_capacity] for keys
    pub fn reallocate_min_capacity_keys(
        &mut self,
        min_capacity: usize,
    ) -> Result<(), ReallocationError> {
        self.keys.reallocate_min_capacity(min_capacity)
    }

    /// Follows [ArenaTrait::reallocate_min_capacity] for vals
    pub fn reallocate_min_capacity_vals(
        &mut self,
        min_capacity: usize,
    ) -> Result<(), ReallocationError> {
        self.vals.reallocate_min_capacity(min_capacity)
    }

    /// Inserts a new surject into the arena, with initial key `k` for the key
    /// set and associated value `v`. Returns a `Ptr` to the key.
    pub fn insert_within_capacity(&mut self, k: K, v: V) -> Result<P, NotWithinCapacityError> {
        let entry = self.entry_insert_within_capacity()?;
        let p = entry.ptr();
        entry.insert(k, v);
        Ok(p)
    }

    /// Inserts a new surject into the arena, with initial key `k` for the key
    /// set and associated value `v`. Returns a `Ptr` to the key.
    pub fn insert_reallocating(&mut self, k: K, v: V) -> Result<P, ReallocationError> {
        let entry = self.entry_insert_reallocating()?;
        let p = entry.ptr();
        entry.insert(k, v);
        Ok(p)
    }

    /// Inserts a new surject into the arena, with initial key `k` for the key
    /// set and associated value `v`. Returns a `Ptr` to the key.
    ///
    /// # Panics
    ///
    /// Panics on allocation failure or if max capacity is used up
    #[track_caller]
    pub fn insert(&mut self, k: K, v: V) -> P {
        self.insert_reallocating(k, v)
            .expect("`SurjectArena::insert_reallocating` failed")
    }

    /// Entry version of [SurjectArena::insert_within_capacity]
    pub fn entry_insert_within_capacity(
        &mut self,
    ) -> Result<SurjectArenaInsertEntry<'_, P, K, V, B>, NotWithinCapacityError> {
        let entry = self
            .keys
            .entry_insert_within_capacity(LinkInsertKind::SingleLinkCyclic)
            .map_err(|_| NotWithinCapacityError)?;
        let p = entry.ptr();
        // will need space for a new value
        let _ = self.vals.entry_insert_within_capacity()?;
        Ok(SurjectArenaInsertEntry { this: self, p })
    }

    /// Entry version of [SurjectArena::insert_reallocating]
    pub fn entry_insert_reallocating(
        &mut self,
    ) -> Result<SurjectArenaInsertEntry<'_, P, K, V, B>, ReallocationError> {
        let p = match self
            .keys
            .entry_insert_reallocating(LinkInsertKind::SingleLinkCyclic)
        {
            Ok(entry) => entry.ptr(),
            Err(ChainInsertionError::BeyondMaxCapacity) => {
                return Err(ReallocationError::BeyondMaxCapacity);
            }
            Err(_) => return Err(ReallocationError::AllocError),
        };
        let _ = self.vals.entry_insert_reallocating()?;
        Ok(SurjectArenaInsertEntry { this: self, p })
    }

    /// Inserts a new key into the arena, associating it with an existing
    /// surject, of which `ptr_in_target_set` is an existing key in that set.
    /// Returns `ChainInsertionError::FailedLinkRequirement` if
    /// `ptr_in_target_set` is invalid.
    pub fn insert_key_within_capacity(
        &mut self,
        ptr_in_target_set: P,
        k: K,
    ) -> Result<P, ChainInsertionError> {
        let entry = self.entry_insert_key_within_capacity(ptr_in_target_set)?;
        let p = entry.ptr();
        entry.insert(k);
        Ok(p)
    }

    /// Reallocating version of [SurjectArena::insert_key_within_capacity]
    pub fn insert_key_reallocating(
        &mut self,
        ptr_in_target_set: P,
        k: K,
    ) -> Result<P, ChainInsertionError> {
        let entry = self.entry_insert_key_reallocating(ptr_in_target_set)?;
        let p = entry.ptr();
        entry.insert(k);
        Ok(p)
    }

    /// Panicking version of [SurjectArena::insert_key_within_capacity]
    ///
    /// # Panics
    ///
    /// Panics on allocation failure, or if max capacity is used up, or if
    /// `ptr_in_target_set` was invalid
    #[track_caller]
    pub fn insert_key(&mut self, ptr_in_target_set: P, k: K) -> P {
        self.insert_key_reallocating(ptr_in_target_set, k)
            .expect("`SurjectArena::insert_key_reallocating` failed")
    }

    /// Entry version of [SurjectArena::insert_key_within_capacity]
    pub fn entry_insert_key_within_capacity(
        &mut self,
        ptr_in_target_set: P,
    ) -> Result<SurjectArenaInsertKeyEntry<'_, P, K, V, B>, ChainInsertionError> {
        if !self.contains(ptr_in_target_set) {
            return Err(ChainInsertionError::FailedLinkRequirement);
        }
        // only need space for the key
        let entry = self
            .keys
            .entry_insert_within_capacity(LinkInsertKind::SingleLinkCyclic)?;
        let p = entry.ptr();
        Ok(SurjectArenaInsertKeyEntry {
            this: self,
            p_target: ptr_in_target_set.inx(),
            p_new: p,
        })
    }

    /// Entry version of [SurjectArena::insert_key_reallocating]
    pub fn entry_insert_key_reallocating(
        &mut self,
        ptr_in_target_set: P,
    ) -> Result<SurjectArenaInsertKeyEntry<'_, P, K, V, B>, ChainInsertionError> {
        if !self.contains(ptr_in_target_set) {
            return Err(ChainInsertionError::FailedLinkRequirement);
        }
        // only need space for the key
        let entry = self
            .keys
            .entry_insert_reallocating(LinkInsertKind::SingleLinkCyclic)?;
        let p = entry.ptr();
        Ok(SurjectArenaInsertKeyEntry {
            this: self,
            p_target: ptr_in_target_set.inx(),
            p_new: p,
        })
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

    /// Gets two `&mut V` references pointed to by `p0` and `p1`. If
    /// `self.in_same_set(p0, p1)` or a pointer is invalid, `None` is
    /// returned.
    #[must_use]
    pub fn get2_val_mut(&mut self, p0: P, p1: P) -> Option<(&mut V, &mut V)> {
        let p_val0 = self.keys.get(p0)?.p_val;
        let p_val1 = self.keys.get(p1)?.p_val;
        let [val0, val1] = self.vals.get_disjoint_mut([p_val0, p_val1]).ok()?;
        Some((&mut val0.v, &mut val1.v))
    }

    /// Returns the generation associated with `p` and a `LinkNoGen<P, &K>`, the
    /// interlinks of which point to other keys in the key set. The key set is a
    /// cyclic chain of `LinkNoGen`s.
    #[must_use]
    pub fn get_inx_link_no_gen(&self, p: P::Inx) -> Option<(P::Gen, LinkNoGen<P, &K>)> {
        self.keys
            .get_inx_link_no_gen(p)
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
            return None;
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
            self.keys.get_inx_mut_unwrap(tmp).p_val = p_val0;
            tmp = self
                .keys
                .get_inx_link_no_gen(tmp)
                .unwrap()
                .1
                .next()
                .unwrap();
            if tmp == p1.inx() {
                break;
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
        Some((self.vals.remove(p_val1).allow().unwrap().v, p0))
    }

    /// Removes the key pointed to by `p`. If there were other keys still in the
    /// key set, the value is not removed and `Some((key, None))` is
    /// returned. If `p` was the last key in the key set, then the value is
    /// removed and returned like `Some((key, Some(val)))`. Returns
    /// `None` if `p` is not valid.
    pub fn remove_key(&mut self, p: P) -> InvalidationResult<(K, Option<V>)> {
        let (key, o) = match self.keys.remove(p) {
            InvalidationResult::Success(key) => (key, false),
            InvalidationResult::GenerationOverflow(key) => (key, true),
            InvalidationResult::InvalidPtr => return InvalidationResult::InvalidPtr,
        };
        let p_val = key.p_val;
        let k = key.k;
        let key_count = &mut self.vals.get_inx_mut_unwrap(p_val.inx()).key_count;
        let res = if let Some(next) = NonZeroUsize::new(key_count.get() - 1) {
            // decrement the key count
            *key_count = next;
            (k, None)
        } else {
            // last key, remove the value
            (k, Some(self.vals.remove(p_val).allow().unwrap().v))
        };
        if o {
            InvalidationResult::GenerationOverflow(res)
        } else {
            InvalidationResult::Success(res)
        }
    }

    // TODO have a drain_surject instead

    /// Removes the entire key set and value cheaply, returning the value. `p`
    /// can point to any key from the key set. Returns `None` if `p` is invalid.
    pub fn remove_surject(&mut self, p: P) -> InvalidationResult<V> {
        let Some(key) = self.keys.get(p) else {
            return InvalidationResult::InvalidPtr;
        };
        let v = self.vals.remove(key.p_val).allow().unwrap().v;
        self.keys.remove_cyclic_chain_internal(p.inx(), false);
        match self.inc_generation() {
            InvalidationOption::Success(()) => InvalidationResult::Success(v),
            InvalidationOption::GenerationOverflow(()) => InvalidationResult::GenerationOverflow(v),
        }
    }

    /// Invalidates the `Ptr` `p` (no other `Ptr`s to keys in the key set are
    /// invalidated), returning a new valid `Ptr`
    pub fn invalidate(&mut self, p: P) -> InvalidationResult<P> {
        // the chain arena fixes interlinks
        self.keys.invalidate(p)
    }

    /// Drops all keys and values from the arena and invalidates all pointers
    /// previously created from it. This has no effect on allocated
    /// capacities of keys or values.
    pub fn clear(&mut self) -> InvalidationOption<()> {
        self.vals.clear().allow();
        self.keys.clear()
    }

    /// `aux_recaster` is for internal use only and is filled with arbirary data
    /// unrelated to the logical keys.
    ///
    /// This mess of a function is used like so: FIXME
    pub fn transfer_canonical_reallocating<
        Q: Ptr,
        K1,
        V1,
        B1: ArenaBacking,
        F0: FnMut(Q, InvalidationOption<K1>, P) -> K,
        F1: FnMut(V1) -> V,
        D: ArenaDirectInsertTrait<Q, P>,
        Aux: ArenaDirectInsertTrait<PtrNoGen<Q>, PtrNoGen<P>>,
    >(
        &mut self,
        new_generation: P::Gen,
        source: &mut SurjectArena<Q, K1, V1, B1>,
        mut map_key: F0,
        mut map_val: F1,
        recaster: &mut D,
        aux_recaster: &mut Aux,
    ) -> Result<(), ReallocationError> {
        // precheck both keys and values first, can't have atomic fallibility without it

        let Some(len_keys) = NonZeroUsize::new(source.len_keys()) else {
            // follow what the other path would logically do
            recaster.clear().allow();
            aux_recaster.clear().allow();
            self.clear().allow();
            self.set_generation(new_generation);
            return Ok(());
        };
        if P::Inx::try_from_usize(len_keys).is_none() {
            return Err(ReallocationError::BeyondMaxCapacity);
        };
        if len_keys.get() > self.capacity_keys() {
            // max capacity is tested here
            self.reallocate_min_capacity_keys(len_keys.get())?;
        }

        // guaranteed nonempty at this point
        let len_vals = NonZeroUsize::new(source.len_vals()).unwrap();
        if P::Inx::try_from_usize(len_vals).is_none() {
            return Err(ReallocationError::BeyondMaxCapacity);
        };
        if len_vals.get() > self.capacity_vals() {
            // max capacity is tested here
            self.reallocate_min_capacity_vals(len_vals.get())?;
        }

        // the rest should be infallible if soft invariants are followed
        recaster.clear().allow();
        aux_recaster.clear().allow();
        self.clear().allow();
        self.set_generation(new_generation);

        // setup `aux_recaster`
        self.vals
            .transfer_reallocating((), &mut source.vals, |q_val, o, p_val| {
                aux_recaster
                    .direct_insert_within_capacity(q_val)
                    .unwrap()
                    .insert(p_val);
                // internal can't overflow
                let val = o.allow();
                Val {
                    v: map_val(val.v),
                    key_count: val.key_count,
                }
            })
            .unwrap();

        self.keys
            .transfer_canonical_reallocating(
                new_generation,
                &mut source.keys,
                |q, o, p| {
                    let (key, o) = o.overflowing();
                    let arg = if o {
                        InvalidationOption::GenerationOverflow(key.k)
                    } else {
                        InvalidationOption::Success(key.k)
                    };
                    Key {
                        k: map_key(q, arg, p),
                        p_val: *aux_recaster.get(key.p_val).unwrap(),
                    }
                },
                recaster,
            )
            .unwrap();

        Ok(())
    }

    // FIXME can only be a `canonicalize` version
    /*
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
        for i in self.vals.nziter() {
            if matches!(self.vals.m.get(i).unwrap(), ArenaSlot::Free(_)) {
                first_unallocated = Some(i);
                break;
            }
        }

        // first compress the keys so that their cache locality is improved
        let mut p_val_last = None;
        let mut new_p_val = None;
        self.keys
            .compress_with(false, |p, key, q| {
                let p_val = key.p_val;
                if Some(p_val) != p_val_last {
                    let mut new_change = false;
                    if let Some(i_unallocated) = first_unallocated {
                        let i = P::Inx::try_into_usize(p_val.inx()).unwrap();
                        if i > i_unallocated {
                            // move it into the unallocated spot
                            self.vals.raw_entry_swap_special(i_unallocated, i);
                            // change all `p_val`s of the surject
                            new_p_val = Some(P::Inx::try_from_usize(i_unallocated).unwrap());
                            new_change = true;
                            // get the next unallocated index
                            let mut j = i_unallocated.get().wrapping_add(1);
                            loop {
                                if j > self.vals.m.len() {
                                    first_unallocated = None;
                                    break;
                                }
                                let j_nz = NonZeroUsize::new(j).unwrap();
                                if matches!(self.vals.m.get(j_nz).unwrap(), ArenaSlot::Free(_)) {
                                    first_unallocated = Some(j_nz);
                                    break;
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
            })
            .allow();
        // important: remove all free entries, set freelist root to `None`, and shrink
        // to fit `self.vals`, completes the compression and fixes the likely broken
        // freelist
        while let Some(i) = NonZeroUsize::new(self.vals.m.len()) {
            if let Some(ArenaSlot::Free(_)) = self.vals.m.get(i) {
                self.vals.m.pop().unwrap();
            } else {
                break;
            }
        }
        self.vals.freelist_root = None;
        let _ = self.vals.m.reallocate_min_capacity(0);
    }
    */

    /// Has the same properties of [Arena::clone_from_with]
    pub fn clone_from_with<
        K1: Ord,
        V1,
        F0: FnMut(P, &K1) -> K,
        F1: FnMut(NonZeroUsize, &V1) -> V,
    >(
        &mut self,
        source: &SurjectArena<P, K1, V1, B>,
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
        self.vals
            .clone_from_with(&source.vals, |_, val| {
                let v = map_val(val.key_count, &val.v);
                Val {
                    v,
                    key_count: val.key_count,
                }
            })
            .unwrap();
    }

    /// Overwrites `chain_arena` (dropping all preexisting `T`, overwriting the
    /// generation counter, and reusing capacity) with the `Ptr` mapping of
    /// `self`, with groups of keys preserved as cyclical chains.
    pub fn clone_keys_to_chain_arena<T, F: FnMut(P, &K) -> T>(
        &self,
        chain_arena: &mut ChainArena<P, T, B>,
        mut map: F,
    ) {
        chain_arena.clone_from_with(&self.keys, |p, link| map(p, &link.t.k))
    }

    /// Overwrites `arena` (dropping all preexisting `T` and relations,
    /// overwriting the generation counter, and reusing capacity) with the
    /// `Ptr` mapping of `self`.
    pub fn clone_keys_to_arena<T, F: FnMut(P, &K) -> T>(
        &self,
        arena: &mut Arena<P, T, B>,
        mut map: F,
    ) {
        self.keys.clone_to_arena(arena, |p, link| map(p, &link.t.k))
    }
}

// we can't implement `Index` because the format would force `&(&K, &V)` which
// causes many further problems

impl<P: Ptr, K: Debug, V: Debug, B: ArenaBacking> Debug for SurjectArena<P, K, V, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

/// Implemented if `K: Clone` and `V: Clone`.
impl<P: Ptr, K: Clone, V: Clone, B: ArenaBacking> Clone for SurjectArena<P, K, V, B> {
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

impl<P: Ptr, K, V, B: ArenaBacking> Default for SurjectArena<P, K, V, B> {
    fn default() -> Self {
        Self::new()
    }
}
