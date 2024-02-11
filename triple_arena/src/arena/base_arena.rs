use core::{
    borrow::Borrow,
    fmt, mem,
    num::NonZeroUsize,
    ops::{Index, IndexMut},
};

use crate::{
    utils::{nzusize_unchecked, ptrinx_unchecked, NonZeroInxVec, PtrGen, PtrInx},
    Advancer, Ptr,
};

/// Internal entry for an `Arena`.
#[derive(Clone)]
pub enum InternalEntry<P: Ptr, T> {
    /// A free entry with no `T`. The `usize` points to the next free entry,
    /// except if it points to the self entry in which case it is the last free
    /// entry.
    Free(P::Inx),
    /// An entry allocated for a `(P::Gen, T)` pair in the arena.
    Allocated(P::Gen, T),
}

impl<P: Ptr, T> InternalEntry<P, T> {
    #[inline]
    pub fn replace_free_with_allocated(&mut self, gen: P::Gen, t: T) -> Option<P::Inx> {
        let free = mem::replace(self, Allocated(gen, t));
        if let Free(free) = free {
            Some(free)
        } else {
            None
        }
    }

    // no `replace_allocated_with_free`, it is too easy to introduce invariant
    // breakage
}

use InternalEntry::*;

/// An arena supporting non-Clone `T` (`T` has no requirements other than
/// `Sized`, but some traits are only active if `T` implements them), deletion,
/// and optional generation counters.
///
/// `P` is a struct implementing `Ptr`, which has associated types for
/// determining what the arena's indexes and generation counters should be.
/// When using multiple arenas, it is encouraged to use different `P` in order
/// to have the type system guard against confusion and mistakenly using
/// pointers from one arena in another. The arena will use generation counters
/// to check for invalidated pointers if `P` has a generation counter.
/// ```
/// use triple_arena::{ptr_struct, Arena, Ptr};
///
/// // In implementations that always use valid indexes and only want the
/// // generation counter in debug mode, we can use `cfg`s like this:
/// /* // commented out because of doc tests
/// #[cfg(Debug)]
/// ptr_struct!(P0);
/// #[cfg(Debug)]
/// ptr_struct!(Q2);
/// #[cfg(not(Debug))]
/// ptr_struct!(P0());
/// #[cfg(not(Debug))]
/// ptr_struct!(Q2());
/// */
/// ptr_struct!(P0);
/// ptr_struct!(Q2);
///
/// // By convention we use short names for `Ptr` structs beginning with `P`,
/// // `Q`, or `R`. In simple contexts we add a single digit to differentiate
/// // the generic `P: Ptr` from a instantiated `P0`. If the number of arenas
/// // exceeds a small number or the types will be public, you should use more
/// // descriptive names like `PNode`, `PComponent`, `PNameOfEntryKind`, etc.
///
/// let mut arena: Arena<P0, String> = Arena::new();
///
/// let test_ptr: P0 = arena.insert("test".to_string());
/// let hello_ptr: P0 = arena.insert("hello".to_string());
///
/// // Nice debug representations. See also the `triple_arena_render` crate for
/// // trait-based rendering of graphs. Note that the internal indexes are
/// // starting at 1 because `NonZero` types are used. This allows for memory
/// // niche optimizations of `Option<P>` and other such things.
/// assert_eq!(
///     &format!("{:?}", arena),
///     "{P0[1](2): \"test\", P0[2](2): \"hello\"}"
/// );
///
/// // use the `Ptr`s we got from insertion to reference the stored data
/// assert_eq!(arena[hello_ptr], "hello");
///
/// // Remove objects. The `Arena` uses internal freelists to keep the capacity
/// // for future inserts to reuse.
/// let removed = arena.remove(test_ptr).unwrap();
/// assert_eq!(removed, "test");
///
/// // When using generation counters, invalidated pointers are guaranteed to
/// // never work again.
/// assert!(arena.get(test_ptr).is_none());
///
/// // Using different `Ptr` generics is extremely useful in complicated
/// // multiple arena code with self pointers and inter-arena pointers. This is
/// // an arena storing a tuple of pointers that work on the first arena and
/// // itself.
/// let mut arena2: Arena<Q2, (P0, Q2)> = Arena::new();
///
/// let p2_ptr: Q2 = arena2.insert((hello_ptr, Ptr::invalid()));
/// let another: Q2 = arena2.insert((hello_ptr, p2_ptr));
///
/// // With many arena crates, no compile time or runtime checks would prevent
/// // you from using the wrong pointers. Here, the compiler protects us.
/// // error: expected struct `P0`, found struct `Q2`
/// //let _ = arena.get(p2_ptr);
///
/// assert_eq!(arena[arena2[p2_ptr].0], "hello");
///
/// // In cases where we are forced to have the same `Ptr` struct, we can still
/// // have type guards against semantically different `Ptr`s by using generics:
/// fn example<P0: Ptr, P1: Ptr, T>(a0: &mut Arena<P0, T>, a1: &mut Arena<P1, T>, p1: P1) {
///     // error: expected type parameter `P0`, found type parameter `P1`
///     //let _ = a0.remove(p1);
///
///     a0.insert(a1.remove(p1).unwrap());
/// }
///
/// let mut arena3: Arena<Q2, String> = Arena::new();
/// example(&mut arena3, &mut arena, hello_ptr);
/// assert_eq!(arena3.iter().next().unwrap().1, "hello");
/// ```
///
/// Note: See the `triple_arena_render` crate for a trait-based way to visualize
/// graph structures in `Arena`s
pub struct Arena<P: Ptr, T> {
    /// The main memory of entries.
    ///
    /// # Capacity
    ///
    /// In earlier versions of this crate, there was an invariant that
    /// `self.m.capacity() == self.m.len()`. However, the `clone_from_with`
    /// exposed a flaw with this that is absolutely catastrophic for some use
    /// cases of this crate: `reserve` and `reserve_exact` are allowed to
    /// allocate inconsistently, e.x. one arena gets 32 capacity from doubling
    /// and another arena gets 24 from taking a half step (this has been
    /// observed in practice even with `reserve_exact` and identical arenas). If
    /// `clone_from` is called to copy the 24 capacity arena to the 32 capacity
    /// arena, then it must reserve 8 more capacity. `reserve_exact` can
    /// then choose to start allocating by only doubling, in which case the
    /// 24 capacity arena gets 24 additional capacity. If the new 48
    /// capacity arena is cloned to the 32 capacity arena, it can get 32
    /// more capacity to increase to 64 capacity despite nothing being
    /// inserted. If the arenas `clone_from` to each other in a loop, they
    /// leap frog each other exponentially. The only way to fix this is to
    /// have `clone_from` push exactly what it needs to `self.m.len()`, so
    /// they must be detached.
    ///
    /// I have decided to call `m.capacity()` the true allocated capacity and
    /// `m.len()` the virtual capacity. Only `try_insert` and friends increase
    /// the virtual capacity within the allocated capacity, everything else
    /// reads only the virtual capacity and treats it as a limit. See `remove`
    /// for more mitigations.
    ///
    /// # Invariants
    ///
    /// - The generation value starts at 2 in a new Arena, so that the
    ///   `Ptr::invalid` function works
    /// - If there are free entries, all Free entries have their freelist nodes
    ///   in a single linked list with the start being pointed to by
    ///   `freelist_root` and the end pointing to itself
    /// - If there are no free entries, `freelist_root` is `None`
    /// - During an invalidation operation, the arena `gen` is incremented _and_
    ///   the allocation in question is turned into a `Free` or has its
    ///   generation updated to equal the arena's `gen`. Newer allocations must
    ///   use the new `gen` value.
    pub(crate) m: NonZeroInxVec<InternalEntry<P, T>>,
    pub(crate) len: usize,
    /// Points to the root of the chain of freelist nodes
    pub(crate) freelist_root: Option<P::Inx>,
    gen: P::Gen,
}

/// # Note
///
/// A `Ptr` is logically invalid if:
///  - it points to a different arena than the one it is being used as an
///    argument to
///  - it points to a `T` that has been the target of some `Ptr` invalidation
///    operation such as removal
///
/// However, the functions here might not detect invalidity and return a `T`
/// different than the one a `Ptr` originally pointed to. The first case is
/// caught if different `Ptr` structs are being used for different arenas, in
/// which case Rust's type system will prevent using the wrong pointers. The
/// second case is only guaranteed to be caught if `P` has a generation counter.
/// Otherwise, it is possible for another `T` to get allocated in the same
/// allocation, and pointers to the previous `T` will now point to a different
/// `T`. If this is intentional, [Arena::replace_and_keep_gen] should be used.
///
/// # Overflow
///
/// When using the default `P::Inx = usize` and `P::Gen = NonZeroU64`, only
/// memory exhaustion should be a concern on all platforms, but if smaller types
/// are used then panics can realistically happen under these conditions: If
/// `Arena::len() == P::Inx::max()` and an insertion function is called, a
/// panic occurs. If `Arena::gen()` is the maximum value of its type and an
/// invalidation occurs, a panic occurs.
impl<P: Ptr, T> Arena<P, T> {
    /// Used by tests
    #[doc(hidden)]
    pub fn _check_invariants(this: &Self) -> Result<(), &'static str> {
        if this.gen() < P::Gen::two() {
            return Err("bad generation")
        }
        if this.capacity() != this.m.len() {
            return Err("virtual capacity != m_len")
        }
        let mut n_allocated = 0usize;
        for i in this.m.nziter() {
            if matches!(this.m.get(i).unwrap(), Allocated(..)) {
                n_allocated = n_allocated.checked_add(1).unwrap();
            }
        }
        let n_free = this.m.len() - n_allocated;
        if this.len() != n_allocated {
            return Err("len != n_allocated")
        }
        // checking freelist integrity
        let mut freelist_len = 0usize;
        if let Some(root) = this.freelist_root {
            let mut tmp_inx = root;
            for i in 0.. {
                let entry = this.m.get(P::Inx::get(tmp_inx)).unwrap();
                if let Free(inx) = entry {
                    freelist_len = freelist_len.checked_add(1).unwrap();
                    if *inx == tmp_inx {
                        // last one
                        break
                    }
                    tmp_inx = *inx;
                } else {
                    return Err("bad freelist node")
                }
                if i > this.m.len() {
                    return Err("endless loop")
                }
            }
        }
        if freelist_len != n_free {
            return Err("freelist discontinuous")
        }
        Ok(())
    }

    /// Creates a new arena of type `T`, which are pointed to by `P`s. The arena
    /// will not allocate until elements are inserted.
    pub fn new() -> Self {
        Self {
            len: 0,
            m: NonZeroInxVec::new(),
            freelist_root: None,
            gen: PtrGen::two(),
        }
    }

    /// [Arena::new] but with the initial capacity set to at least `capacity`
    pub fn with_capacity(capacity: usize) -> Self {
        let mut res = Self::new();
        res.reserve(capacity);
        res
    }

    /// Returns the number of `T` in the arena
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns if the arena is empty
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the capacity of the arena.
    ///
    /// Technical note: This is usually equal to the true allocated capacity but
    /// is sometimes less in order to prevent exponential capacity growth
    /// with some combinations of functions (see the "Capacity" section in
    /// lib.rs for details).
    pub fn capacity(&self) -> usize {
        self.m.len()
    }

    pub(crate) fn set_gen(&mut self, new_gen: P::Gen) {
        self.gen = new_gen;
    }

    /// Return the arena generation counter (unless `P::Gen` is `()` in which
    /// case there is no generation counting), which is equal to the number of
    /// invalidation operations performed on this arena plus 2
    #[inline]
    pub fn gen(&self) -> P::Gen {
        self.gen
    }

    #[inline]
    pub(crate) fn inc_gen(&mut self) {
        self.gen = PtrGen::increment(self.gen);
    }

    /// Reserves capacity such that `self.capacity()` becomes at least
    /// `self.len() + additional`.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `P::Inx::MAX`.
    pub fn reserve(&mut self, additional: usize) {
        let old_virt_cap = self.m.len();
        let old_real_cap = self.m.capacity();
        let target = old_virt_cap
            .checked_add(additional)
            .expect(" wanted arena capacity exceeds `P::Inx::MAX`");
        if target > <P::Inx as PtrInx>::max().get() {
            panic!("wanted arena capacity exceeds `P::Inx::MAX`");
        }
        // then determine if we need to reserve any real capacity
        let reserve_amt = if target <= old_real_cap {
            // this both handles the overflow case and prevents the exponential capacity
            // growth problem, because if the real capacity is greater than target virtual
            // capacity, then this is reached.
            0
        } else {
            // nonoverflowing and nonzero since `target > old_real_cap`
            target.wrapping_sub(old_real_cap)
        };
        // check for greater than zero, `reserve(0)` can trigger allocation and thus
        // exponential growth problems
        if reserve_amt > 0 {
            self.m.reserve(reserve_amt);
        }
        // Get to `target` virtual capacity and no more, do not go all way to
        // `self.m.capacity()`. Nonoverflowing since `target` is a checked add on
        // `old_virt_cap`.
        let remaining = target.wrapping_sub(old_virt_cap);
        if remaining > 0 {
            // Safety: `old_virt_cap` cannot be more than `isize::MAX`,
            // `target > 0` because `remaining > 0`, `isize::MAX` guarantees
            unsafe {
                let old_root = self.freelist_root;
                // we can choose the new root to go anywhere in the new capacity, but we choose
                // to point at the previous virtual capacity.
                self.freelist_root = Some(ptrinx_unchecked(old_virt_cap.wrapping_add(1)));
                // initialize the freelist with each entry pointing to the next
                for i in old_virt_cap.wrapping_add(2)
                    ..old_virt_cap.wrapping_add(remaining).wrapping_add(1)
                {
                    self.m.push(Free(ptrinx_unchecked(i)));
                }
                match old_root {
                    Some(old_root) => {
                        // The last `Free` points to the old root
                        self.m.push(Free(old_root));
                    }
                    None => {
                        // the last `Free` points to itself
                        self.m.push(Free(ptrinx_unchecked(target)));
                    }
                }
            }
        }
    }

    #[must_use]
    #[inline]
    pub(crate) fn m_get(&self, inx: P::Inx) -> Option<&InternalEntry<P, T>> {
        self.m.get(P::Inx::get(inx))
    }

    #[must_use]
    #[inline]
    pub(crate) fn m_get_mut(&mut self, inx: P::Inx) -> Option<&mut InternalEntry<P, T>> {
        self.m.get_mut(P::Inx::get(inx))
    }

    /// Panics if index `inx` does not point to a `Free` entry.
    #[inline]
    fn unwrap_replace_free(&mut self, inx: P::Inx, gen: P::Gen, t: T) {
        let next = self
            .m_get_mut(inx)
            .unwrap()
            .replace_free_with_allocated(gen, t)
            .unwrap();
        if next == inx {
            // end of freelist
            self.freelist_root = None;
        } else {
            // move to next node in the freelist
            self.freelist_root = Some(next);
        }
    }

    /// Tries to insert `t` into the arena without changing its capacity.
    ///
    /// # Errors
    ///
    /// Returns ownership of `t` if there are no remaining unallocated entries
    /// in the arena.
    pub fn try_insert(&mut self, t: T) -> Result<P, T> {
        if let Some(inx) = self.freelist_root {
            self.unwrap_replace_free(inx, self.gen(), t);
            self.len = self.len.wrapping_add(1);
            Ok(Ptr::_from_raw(inx, self.gen()))
        } else {
            Err(t)
        }
    }

    /// Tries to insert the `T` returned by `create` into the arena without
    /// changing its capacity. `create` is given the the same `Ptr` that is
    /// returned for referencing the `T` again.
    ///
    /// # Errors
    ///
    /// Does not run `create` and returns ownership if there are no remaining
    /// unallocated entries in the arena.
    pub fn try_insert_with<F: FnOnce(P) -> T>(&mut self, create: F) -> Result<P, F> {
        if let Some(inx) = self.freelist_root {
            let ptr = P::_from_raw(inx, self.gen());
            self.unwrap_replace_free(inx, self.gen(), create(ptr));
            self.len = self.len.wrapping_add(1);
            Ok(ptr)
        } else {
            Err(create)
        }
    }

    /// Inserts `t` into the arena and returns a `Ptr` to it. This function
    /// allocates if capacity in the arena runs out.
    pub fn insert(&mut self, t: T) -> P {
        match self.try_insert(t) {
            Ok(inx) => inx,
            Err(t) => {
                // double the allocation size
                let mut additional = self.m.len();
                if additional == 0 {
                    // need at least one
                    additional = 1;
                }
                // make sure to not make `reserve` panic
                let new_len = self
                    .len()
                    .saturating_add(additional)
                    .clamp(0, <P::Inx as PtrInx>::max().get());
                additional = new_len.wrapping_sub(self.len());
                self.reserve(additional);
                // can't unwrap unless T: Debug
                match self.try_insert(t) {
                    Ok(p) => p,
                    Err(_) => panic!(
                        "called `insert` on an `Arena<P, T>` with maximum length `P::Inx::max()`"
                    ),
                }
            }
        }
    }

    /// Inserts the `T` returned by `create` into the arena and returns a `Ptr`
    /// to it. `create` is given the the same `Ptr` that is returned, which is
    /// useful for initialization of immutable structures that need to reference
    /// themselves. This function allocates if capacity in the arena runs out.
    pub fn insert_with<F: FnOnce(P) -> T>(&mut self, create: F) -> P {
        // can't use `try_insert_with` analogously like `insert` uses `try_insert`
        // because `create` is `FnOnce`
        let inx = if let Some(inx) = self.freelist_root {
            inx
        } else {
            // double the allocation size
            let mut additional = self.m.len();
            if additional == 0 {
                // need at least one
                additional = 1;
            }
            self.reserve(additional);
            self.freelist_root.unwrap()
        };
        let ptr = P::_from_raw(inx, self.gen());
        self.unwrap_replace_free(inx, self.gen(), create(ptr));
        self.len = self.len.wrapping_add(1);
        ptr
    }

    /// Returns if `p` is a valid `Ptr`
    pub fn contains(&self, p: P) -> bool {
        match self.m_get(p.inx()) {
            Some(Allocated(gen, _)) => *gen == p.gen(),
            _ => false,
        }
    }

    /// Returns a reference to a `T` pointed to by `p`. Returns `None` if `p` is
    /// invalid.
    #[must_use]
    pub fn get(&self, p: P) -> Option<&T> {
        match self.m_get(p.inx()) {
            Some(Allocated(gen, t)) => {
                if *gen == p.gen() {
                    Some(t)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Returns a mutable reference to a `T` pointed to by `p`. Returns `None`
    /// if `p` is invalid.
    #[must_use]
    pub fn get_mut(&mut self, p: P) -> Option<&mut T> {
        match self.m_get_mut(p.inx()) {
            Some(Allocated(gen, t)) => {
                if *gen == p.gen() {
                    Some(t)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Gets two `&mut T` references pointed to by `p0` and `p1`. If `p0 == p1`
    /// or a pointer is invalid, `None` is returned.
    #[must_use]
    pub fn get2_mut(&mut self, p0: P, p1: P) -> Option<(&mut T, &mut T)> {
        if let Some((n0, n1)) = self
            .m
            .get2_mut(P::Inx::get(p0.inx()), P::Inx::get(p1.inx()))
        {
            if let (Allocated(gen0, t0), Allocated(gen1, t1)) = (n0, n1) {
                if (*gen0 == p0.gen()) && (*gen1 == p1.gen()) {
                    Some((t0, t1))
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    /// `remove` but with optional generation counter increment
    #[must_use]
    pub(crate) fn remove_internal(&mut self, p: P, inc_gen: bool) -> Option<T> {
        let freelist_ptr = if let Some(free) = self.freelist_root {
            // points to previous root
            free
        } else {
            // points to itself
            p.inx()
        };
        let allocation = self.m_get_mut(p.inx())?;
        let old = mem::replace(allocation, Free(freelist_ptr));
        match old {
            Free(old_free) => {
                // undo
                *allocation = Free(old_free);
                None
            }
            Allocated(gen, old_t) => {
                if gen != p.gen() {
                    // undo
                    *allocation = Allocated(gen, old_t);
                    None
                } else {
                    // in both cases the new root is the entry we just removed
                    self.freelist_root = Some(p.inx());
                    self.len = self.len.wrapping_sub(1);
                    if inc_gen {
                        self.inc_gen();
                    }
                    Some(old_t)
                }
            }
        }
    }

    /// Same as [Arena::remove_internal] but using an `P::Inx` and panicking if
    /// `p` is invalid
    pub(crate) fn remove_internal_inx_unwrap(&mut self, p: P::Inx, inc_gen: bool) -> T {
        let freelist_ptr = if let Some(free) = self.freelist_root {
            // points to previous root
            free
        } else {
            // points to itself
            p
        };
        let allocation = self.m_get_mut(p).unwrap();
        let old = mem::replace(allocation, Free(freelist_ptr));
        match old {
            Free(_) => {
                unreachable!()
            }
            Allocated(_, old_t) => {
                // in both cases the new root is the entry we just removed
                self.freelist_root = Some(p);
                self.len = self.len.wrapping_sub(1);
                if inc_gen {
                    self.inc_gen();
                }
                old_t
            }
        }
    }

    /// Removes the `T` pointed to by `p`, returns the `T`, and invalidates old
    /// `Ptr`s to the `T`. Does no invalidation and returns `None` if `p` is
    /// invalid.
    #[must_use]
    pub fn remove(&mut self, p: P) -> Option<T> {
        self.remove_internal(p, true)
    }

    /// For every `T` in the arena, `pred` is called with a tuple of the `Ptr`
    /// to that `T` and a mutable reference to the `T`. If `pred` returns `true`
    /// that `T` is dropped and pointers to it invalidated.
    pub fn remove_by<F: FnMut(P, &mut T) -> bool>(&mut self, mut pred: F) {
        for inx in self.m.nziter() {
            let entry = self.m.get_mut(inx).unwrap();
            let inx = P::Inx::new(inx);
            if let Allocated(gen, t) = entry {
                if pred(P::_from_raw(inx, *gen), t) {
                    self.len = self.len.wrapping_sub(1);
                    if let Some(free) = self.freelist_root {
                        // point to previous root
                        *entry = Free(free);
                    } else {
                        // point to self
                        *entry = Free(inx);
                    }
                    self.freelist_root = Some(inx);
                }
            }
        }
        // we only need one increment
        self.inc_gen();
    }

    /// Invalidates all references to the `T` pointed to by `p`, and returns a
    /// new valid reference. Does no invalidation and returns `None` if `p` is
    /// invalid.
    #[must_use]
    pub fn invalidate(&mut self, p: P) -> Option<P> {
        match self.m_get(p.inx()) {
            Some(Allocated(gen, _)) => {
                if *gen != p.gen() {
                    return None
                }
            }
            _ => return None,
        }
        // redo to get around borrowing issues
        self.inc_gen();
        let new_gen = self.gen();
        match self.m_get_mut(p.inx()) {
            Some(Allocated(gen, _)) => {
                *gen = new_gen;
                Some(P::_from_raw(p.inx(), self.gen()))
            }
            _ => unreachable!(),
        }
    }

    /// Replaces the `T` pointed to by `p` with `new`, returns the old `T`, and
    /// keeps the internal generation counter as-is so that previously
    /// constructed `Ptr`s to this allocation are still valid.
    ///
    /// # Errors
    ///
    /// Returns ownership of `new` instead if `p` is invalid
    pub fn replace_and_keep_gen(&mut self, p: P, new: T) -> Result<T, T> {
        let old_gen = match self.m_get(p.inx()) {
            Some(Allocated(gen, _)) => {
                if *gen != p.gen() {
                    return Err(new)
                }
                *gen
            }
            _ => return Err(new),
        };
        let old = mem::replace(self.m_get_mut(p.inx()).unwrap(), Allocated(old_gen, new));
        match old {
            Allocated(_, old_gen) => Ok(old_gen),
            _ => unreachable!(),
        }
    }

    /// Replaces the `T` pointed to by `p` with `new`, returns a tuple of the
    /// old `T` and new `Ptr`, and updates the internal generation counter so
    /// that previous `Ptr`s to this allocation are invalidated.
    ///
    /// # Errors
    ///
    /// Does no invalidation and returns ownership of `new` if `p` is invalid
    pub fn replace_and_update_gen(&mut self, p: P, new: T) -> Result<(T, P), T> {
        match self.m_get(p.inx()) {
            Some(Allocated(gen, _)) => {
                if *gen != p.gen() {
                    return Err(new)
                }
            }
            _ => return Err(new),
        }
        self.inc_gen();
        let new_gen = self.gen();
        let old = mem::replace(self.m_get_mut(p.inx()).unwrap(), Allocated(new_gen, new));
        match old {
            Allocated(_, old) => Ok((old, P::_from_raw(p.inx(), new_gen))),
            _ => unreachable!(),
        }
    }

    /// Swaps the `T` at indexes `p0` and `p1` and keeps the generation counters
    /// as-is. If `p0 == p1` then nothing occurs. Returns `None` if `p0` or `p1`
    /// are invalid.
    #[must_use]
    pub fn swap(&mut self, p0: P, p1: P) -> Option<()> {
        if p0.inx() == p1.inx() {
            if self.contains(p0) && self.contains(p1) {
                Some(())
            } else {
                None
            }
        } else if let Some((n0, n1)) = self
            .m
            .get2_mut(P::Inx::get(p0.inx()), P::Inx::get(p1.inx()))
        {
            if let (Allocated(gen0, t0), Allocated(gen1, t1)) = (n0, n1) {
                if (*gen0 == p0.gen()) && (*gen1 == p1.gen()) {
                    mem::swap(t0, t1);
                    Some(())
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Drops all `T` from the arena and invalidates all pointers previously
    /// created from it. This has no effect on allocated capacity.
    pub fn clear(&mut self) {
        // drop all `T` and recreate the freelist
        for i in self.m.nziter() {
            // Safety: `isize::MAX` guarantee
            unsafe {
                let next = ptrinx_unchecked(i.get().wrapping_add(1));
                *self.m_get_mut(P::Inx::new(i)).unwrap() = Free(next);
            }
        }
        if !self.m.is_empty() {
            // the last freelist node points to itself
            // Safety: `isize::MAX` guarantee, and `!self.m.is_empty()`
            unsafe {
                let last = nzusize_unchecked(self.m.len());
                *self.m.get_mut(last).unwrap() = Free(P::Inx::new(last));
                self.freelist_root = Some(ptrinx_unchecked(1));
            }
        } else {
            self.freelist_root = None;
        }
        self.inc_gen();
        self.len = 0;
    }

    /// Performs an [Arena::clear] and resets capacity to 0
    pub fn clear_and_shrink(&mut self) {
        self.m.clear();
        self.m.clear_and_shrink();
        self.freelist_root = None;
        self.inc_gen();
        self.len = 0;
    }

    /// This is currently only used by `SurjectArena::compress_and_shrink_with`
    /// in a way that avoids a broken freelist.
    pub(crate) fn raw_entry_swap_special(&mut self, i0: NonZeroUsize, i1: NonZeroUsize) {
        if i0 != i1 {
            let (entry0, entry1) = self.m.get2_mut(i0, i1).unwrap();
            mem::swap(entry0, entry1);
        }
    }

    /// Compresses the arena by moving around entries to be able to shrink the
    /// capacity down to the length. All entries remain, but all `Ptr`s are
    /// invalidated. New `Ptr`s to the entries can be found again by iterators
    /// and advancers.
    pub fn compress_and_shrink(&mut self) {
        self.compress_and_shrink_with(|_, _, _| ())
    }

    /// The same as [Arena::compress_and_shrink] except that `map` is run on
    /// `(P, &mut T, P)`, with the first `P` being the old `Ptr` and the last
    /// `P` being the new `Ptr`.
    pub fn compress_and_shrink_with<F: FnMut(P, &mut T, P)>(&mut self, mut map: F) {
        self.inc_gen();
        let gen = self.gen();
        let mut new_m = NonZeroInxVec::<InternalEntry<P, T>>::new();
        new_m.reserve(self.len());
        let mut j = 1;
        for i in self.m.nziter() {
            let entry = mem::replace(
                self.m.get_mut(i).unwrap(),
                Free(PtrInx::new(NonZeroUsize::new(1).unwrap())),
            );
            if let Allocated(old_gen, mut t) = entry {
                map(
                    Ptr::_from_raw(PtrInx::new(i), old_gen),
                    &mut t,
                    Ptr::_from_raw(PtrInx::new(NonZeroUsize::new(j).unwrap()), gen),
                );
                new_m.push(Allocated(gen, t));
                j = j.wrapping_add(1);
            }
        }
        self.m = new_m;
        self.freelist_root = None;
    }

    /// Like [Arena::clone_from] except the `Clone` bound is not required
    /// and `source` can have arbitrary `U`. For every `U`, the `P` pointing to
    /// that `U` and a reference to itself is passed to `map` to generate
    /// the corresponding `T` in `self`. Validity is cloned with a `P`
    /// being able to reference `U` in the `source` arena and `T` in `self`.
    pub fn clone_from_with<U, F: FnMut(P, &U) -> T>(&mut self, source: &Arena<P, U>, mut map: F) {
        // exponential growth mitigation factor, absolutely do not use `self.m.capacity`
        // in the extra freelist additions
        let old_virt_cap = self.m.len();
        self.gen = source.gen;
        self.len = source.len;
        // Invariants are temporarily broken, use only methods on `m`.
        // clearing first makes `self.m.reserve` cheaper by not needing to copy
        self.m.clear();
        if self.m.capacity() < source.m.len() {
            self.m
                .reserve(source.m.len().wrapping_sub(self.m.capacity()));
        }
        for i in source.m.nziter() {
            let new = match source.m.get(i).unwrap() {
                // copy `source` freelist
                Free(inx) => Free(*inx),
                // map `source` allocated
                Allocated(gen, u) => Allocated(*gen, map(P::_from_raw(P::Inx::new(i), *gen), u)),
            };
            self.m.push(new);
        }

        // Safety: `isize::MAX` guarantee
        unsafe {
            for i in self.m.len().wrapping_add(2)..old_virt_cap.wrapping_add(1) {
                // point to next
                self.m.push(Free(ptrinx_unchecked(i)));
            }
            if self.m.len() < old_virt_cap {
                // new root starting at extension of `self.m` beyond `source.m`
                self.freelist_root = Some(ptrinx_unchecked(source.m.len().wrapping_add(1)));
                self.m.push(match source.freelist_root {
                    // points to old root
                    Some(inx) => Free(inx),
                    // points to itself
                    None => Free(ptrinx_unchecked(self.m.len().wrapping_add(1))),
                });
            } else {
                self.freelist_root = source.freelist_root;
            }
        }
    }

    /// Like [Arena::get], except generation counters are ignored and the
    /// existing generation is returned.
    #[doc(hidden)]
    pub fn get_no_gen(&self, p: P::Inx) -> Option<(P::Gen, &T)> {
        match self.m_get(p) {
            Some(Allocated(gen, t)) => Some((*gen, t)),
            _ => None,
        }
    }

    /// Like [Arena::get_mut], except generation counters are ignored and the
    /// existing generation is returned.
    #[doc(hidden)]
    pub fn get_no_gen_mut(&mut self, p: P::Inx) -> Option<(P::Gen, &mut T)> {
        match self.m_get_mut(p) {
            Some(Allocated(gen, t)) => Some((*gen, t)),
            _ => None,
        }
    }

    /// Like [Arena::get], except generation counters are ignored and the
    /// result is unwrapped internally
    #[doc(hidden)]
    //#[track_caller]
    pub fn get_inx_unwrap(&self, p: P::Inx) -> &T {
        match self.m_get(p) {
            Some(Allocated(_, t)) => t,
            // if we use `panic` it induces stack management on every hot path according to the
            // assembly
            _ => unreachable!(), /* panic!("get_inx_unwrap of unallocated entry"), */
        }
    }

    /// Like [Arena::get_mut], except generation counters are ignored and the
    /// result is unwrapped internally
    #[doc(hidden)]
    //#[track_caller]
    pub fn get_inx_mut_unwrap(&mut self, p: P::Inx) -> &mut T {
        match self.m_get_mut(p) {
            Some(Allocated(_, t)) => t,
            _ => unreachable!(), /* panic!("get_inx_mut_unwrap of unallocated entry"), */
        }
    }
}

impl<T, P: Ptr> Default for Arena<P, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P: Ptr, T, B: Borrow<P>> Index<B> for Arena<P, T> {
    type Output = T;

    fn index(&self, inx: B) -> &T {
        let p: P = *inx.borrow();
        self.get(p).expect("indexed `Arena` with invalidated `Ptr`")
    }
}

impl<P: Ptr, T, B: Borrow<P>> IndexMut<B> for Arena<P, T> {
    fn index_mut(&mut self, inx: B) -> &mut T {
        let p: P = *inx.borrow();
        self.get_mut(p)
            .expect("indexed `Arena` with invalidated `Ptr`")
    }
}

impl<P: Ptr, T: fmt::Debug> fmt::Debug for Arena<P, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

/// Implemented if `T: Clone`.
impl<P: Ptr, T: Clone> Clone for Arena<P, T> {
    /// When an `Arena<P, T>` is cloned, the `P`s to an original `T` will
    /// initially be valid to the corresponding `T` in the cloned arena.
    /// Invalidations will continue independently, so the meaning of the `Ptr`
    /// with respect to the different arenas can diverge.
    fn clone(&self) -> Self {
        Self {
            len: self.len,
            m: self.m.clone(),
            freelist_root: self.freelist_root,
            gen: self.gen,
        }
    }

    /// Overwrites `self` (dropping all preexisting `T` and overwriting the
    /// generation counter) with a clone of `source`. Has the validity cloning
    /// property of arena cloning, but now the capacity of `self` is reused.
    /// Allocations may happen if the capacity of `self` is not large enough.
    fn clone_from(&mut self, source: &Self) {
        // exponential growth mitigation factor, absolutely do not use `self.m.capacity`
        // in the extra freelist additions
        let old_virt_cap = self.m.len();
        self.gen = source.gen;
        self.len = source.len;
        // Invariants are temporarily broken, use only methods on `m`.
        // clearing first makes `self.m.reserve` cheaper by not needing to copy
        self.m.clear();
        if self.m.capacity() < source.m.len() {
            self.m
                .reserve(source.m.len().wrapping_sub(self.m.capacity()));
        }
        for i in source.m.nziter() {
            self.m.push(source.m.get(i).unwrap().clone());
        }

        // Safety: `isize::MAX` guarantee
        unsafe {
            for i in self.m.len().wrapping_add(2)..old_virt_cap.wrapping_add(1) {
                // point to next
                self.m.push(Free(ptrinx_unchecked(i)));
            }
            if self.m.len() < old_virt_cap {
                // new root starting at extension of `self.m` beyond `source.m`
                self.freelist_root = Some(ptrinx_unchecked(source.m.len().wrapping_add(1)));
                self.m.push(match source.freelist_root {
                    // points to old root
                    Some(inx) => Free(inx),
                    // points to itself
                    None => Free(ptrinx_unchecked(self.m.len().wrapping_add(1))),
                });
            } else {
                self.freelist_root = source.freelist_root;
            }
        }
    }
}

impl<P: Ptr, T: PartialEq> PartialEq<Arena<P, T>> for Arena<P, T> {
    /// Checks if all `(P, T)` pairs are equal. This is sensitive to `Ptr`
    /// indexes and generation counters, but does not compare arena capacities
    /// or `self.gen()`.
    fn eq(&self, other: &Arena<P, T>) -> bool {
        let mut adv0 = self.advancer();
        let mut adv1 = other.advancer();
        while let Some(p0) = adv0.advance(self) {
            if let Some(p1) = adv1.advance(other) {
                if p0 != p1 {
                    return false
                }
                if self.get_inx_unwrap(p0.inx()) != other.get_inx_unwrap(p1.inx()) {
                    return false
                }
            } else {
                return false
            }
        }
        adv1.advance(other).is_none()
    }
}

impl<P: Ptr, T: Eq> Eq for Arena<P, T> {}
