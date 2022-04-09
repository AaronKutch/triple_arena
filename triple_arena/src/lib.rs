#![no_std]
// false positives
#![allow(clippy::while_let_on_iterator)]

mod entry;
mod misc;
mod ptr;
mod traits;
pub(crate) use entry::InternalEntry;
pub use ptr::{Ptr, PtrTrait};
pub use traits::{CapacityDrain, Drain, Iter, IterMut, Ptrs, Vals, ValsMut};

extern crate alloc;
use alloc::vec::Vec;
use core::{borrow::Borrow, mem, num::NonZeroU64};

pub mod prelude {
    pub use crate::{ptr_trait_struct, ptr_trait_struct_with_gen, Arena, Ptr, PtrTrait};
}

use InternalEntry::*;

/// An arena supporting non-Clone `T` (`T` has no requirements other than
/// `Sized`, but some traits are only active if `T` implements them), deletion,
/// and optional generation counters.
///
/// `P` is a `PtrTrait` struct shared by the `Ptr<P>` type used with this arena.
/// When using multiple arenas, it is encouraged to use different `P` in order
/// to have the type system guard against confusion and mistakenly using
/// pointers from one arena in another. If `P` has a generation value, the arena
/// will use generation counters to check for invalidated pointers if `P` has a
/// generation counter.
///
/// Panics or unexpected behaviour could result if `PtrTrait` is not implemented
/// properly for `P`. The macros should be used for quickly making `PtrTrait`
/// structs.
///
/// ```
/// use triple_arena::prelude::*;
///
/// // In implementations that always use valid indexes and only want the
/// // generation counter in debug mode, we can use `cfg`s like this:
/// //#[cfg(Debug)]
/// ptr_trait_struct_with_gen!(Ex; P2);
/// //#[cfg(not(Debug))]
/// //ptr_trait_struct!(Ex; P2);
///
/// let mut arena: Arena<Ex, String> = Arena::new();
///
/// let test_ptr: Ptr<Ex> = arena.insert("test".to_string());
/// let hello_ptr: Ptr<Ex> = arena.insert("hello".to_string());
///
/// // nice debug representations
/// assert_eq!(
///     &format!("{:?}", arena),
///     "{Ptr<Ex>(0)[2]: \"test\", Ptr<Ex>(1)[2]: \"hello\"}"
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
/// // never work again
/// assert!(arena.get(test_ptr).is_none());
///
/// // Using different `P` generics is extremely useful in complicated multiple
/// // arena code with self pointers and inter-arena pointers. This is an arena
/// // storing a tuple of pointers that work on the first arena and itself.
/// let mut arena2: Arena<P2, (Ptr<Ex>, Ptr<P2>)> = Arena::new();
///
/// let p2_ptr: Ptr<P2> = arena2.insert((hello_ptr, Ptr::invalid()));
/// let another: Ptr<P2> = arena2.insert((hello_ptr, p2_ptr));
///
/// // With other arena crates, no compile time or runtime checks would prevent
/// // you from using the wrong pointers. Here, the compiler protects us.
/// // error: expected struct `triple_arena::Ptr<Ex>`
/// //           found struct `triple_arena::Ptr<P2>`
/// //let _ = arena.get(p2_ptr);
///
/// assert_eq!(arena[arena2[p2_ptr].0], "hello");
///
/// // In cases where we are forced to have the same `P`, we can still have
/// // type guards against semantically different `Ptr`s by using generics:
/// fn example<P0: PtrTrait, P1: PtrTrait, T>(
///     a0: &mut Arena<P0, T>,
///     a1: &mut Arena<P1, T>,
///     p1: Ptr<P1>
/// ) {
///    // error: expected type parameter `P0`, found type parameter `P1`
///    //let _ = a0.remove(p1);
///
///    a0.insert(a1.remove(p1).unwrap());
/// }
///
/// let mut arena3: Arena<Ex, String> = Arena::new();
/// example(&mut arena3, &mut arena, hello_ptr);
/// assert_eq!(arena3.iter().next().unwrap().1, "hello");
/// ```
///
/// Note: See the `triple_arena_render` crate for a trait-based way to visualize
/// graph structures in `Arena`s
pub struct Arena<P: PtrTrait, T> {
    /// Number of `T` currently contained in the arena
    len: usize,
    /// The main memory of entries.
    ///
    /// # Capacity
    ///
    /// In earlier versions of this crate, there was an invariant that
    /// `self.m.capacity() == self.m.len()`. However, the `clone_from_with`
    /// exposed a flaw with this that is absolutely catastrophic for some use
    /// cases of this crate: `reserve` and `reserve_exact` can sometimes
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
    m: Vec<InternalEntry<P, T>>,
    /// Points to the root of the chain of freelist nodes
    freelist_root: Option<usize>,
    gen: P,
}

/// # Note
///
/// A `Ptr<P>` is logically invalid if:
///  - it points to a different arena than the one it is being used as an
///    argument to
///  - it points to a `T` that has been the target of some pointer invalidation
///    operation such as removal
///
/// However, the functions here might not detect invalidity and return a `T`
/// different than the one a pointer originally pointed to. The first case is
/// caught if different `P` are being used for different arenas, in which case
/// Rust's type system will prevent using the wrong pointers. The second case is
/// only guaranteed to be caught if `P` has a generation counter. Otherwise, it
/// is possible for another `T` to get allocated in the same allocation, and
/// pointers to the previous `T` will now point to a different `T`. If this is
/// intentional, [Arena::replace_and_keep_gen] should be used.
impl<P: PtrTrait, T> Arena<P, T> {
    /// Used by tests
    #[doc(hidden)]
    pub fn _check_arena_invariants(this: &Self) -> Result<(), &'static str> {
        if let Some(gen) = this.gen_nz() {
            if gen.get() < 2 {
                return Err("bad generation")
            }
        }
        let m_len = this.m.len();
        if this.capacity() != m_len {
            return Err("virtual capacity != m_len")
        }
        let n_allocated = this.iter().fold(0, |acc, _| acc + 1);
        let n_free = m_len - n_allocated;
        if this.len() != n_allocated {
            return Err("len != n_allocated")
        }
        // checking freelist integrity
        let mut freelist_len = 0;
        if let Some(root) = this.freelist_root {
            let mut tmp_inx = root;
            for i in 0.. {
                let entry = this.m.get(tmp_inx).unwrap();
                if let Free(inx) = entry {
                    freelist_len += 1;
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

    /// Creates a new arena for fast allocation for the type `T`, which are
    /// pointed to by `Ptr<P>`s.
    pub fn new() -> Arena<P, T> {
        Arena {
            len: 0,
            m: Vec::new(),
            freelist_root: None,
            gen: PtrTrait::new(Some(NonZeroU64::new(2).unwrap())),
        }
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
    /// Technical note: this is usually equal to the true allocated capacity but
    /// is sometimes less in order to prevent exponential capacity growth
    /// with some combinations of functions (see the "Capacity" section in
    /// lib.rs for details).
    pub fn capacity(&self) -> usize {
        self.m.len()
    }

    /// Return the arena generation counter (or `None` if `P` does not have a
    /// generation), which is equal to the number of invalidation operations
    /// performed on this arena plus 2
    #[inline]
    pub fn gen_nz(&self) -> Option<NonZeroU64> {
        PtrTrait::get(&self.gen)
    }

    /// Return the arena generation counter as a `P`
    #[inline]
    pub fn gen_p(&self) -> P {
        self.gen
    }

    #[inline]
    fn inc_gen(&mut self) {
        if let Some(gen) = PtrTrait::get_mut(&mut self.gen) {
            // if addition overflows, it will result in 0 and the second branch
            match NonZeroU64::new(gen.get().wrapping_add(1)) {
                Some(new_gen) => {
                    *gen = new_gen;
                }
                None => panic!("generation overflow"),
            }
        }
    }

    /// Reserves capacity for at least `additional` more `T`, in accordance
    /// with `Vec::reserve`
    pub fn reserve(&mut self, additional: usize) {
        let end = self.m.len();
        let true_remaining = self.m.capacity().wrapping_sub(end);
        let remaining = if true_remaining < additional {
            self.m.reserve(additional.wrapping_sub(true_remaining));
            self.m.capacity()
        } else {
            // because of the performance edge case with [clone_from], we need to use up
            // existing true allocated capacity first, or else even `additional == 0` can
            // cause exponential growth problems. If the doubling in `insert` or capacity
            // increase in [clone_from] causes the reserve to overstep, and if
            // `true_remaining >= additional`, then `reserve` will not be called
            // until `true_remaining < additional` again. `additional == 0` will
            // always go here.
            additional
        };

        // we will use up this remaining capacity and prepare the virtual capacity
        // with extended freelist
        if remaining > 0 {
            let old_root = self.freelist_root;
            // we can choose the new root to go anywhere in the new capacity, but we choose
            // here
            self.freelist_root = Some(end);
            // initialize the freelist with each entry pointing to the next
            for i in 1..remaining {
                self.m.push(Free(end.wrapping_add(i)));
            }
            match old_root {
                Some(old_root) => {
                    // The last `Free` points to the old root
                    self.m.push(Free(old_root));
                }
                None => {
                    // the last `Free` points to itself
                    self.m
                        .push(Free(end.wrapping_add(remaining).wrapping_sub(1)));
                }
            }
        }
    }

    /// Panics if index `inx` does not point to a `Free` entry.
    #[inline]
    fn unwrap_replace_free(&mut self, inx: usize, allocation: (P, T)) {
        let next = self
            .m
            .get_mut(inx)
            .unwrap()
            .replace_free_with_allocated(allocation)
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
    pub fn try_insert(&mut self, t: T) -> Result<Ptr<P>, T> {
        if let Some(inx) = self.freelist_root {
            self.unwrap_replace_free(inx, (self.gen_p(), t));
            self.len += 1;
            Ok(Ptr::from_raw(inx, self.gen_nz()))
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
    pub fn try_insert_with<F: FnOnce(Ptr<P>) -> T>(&mut self, create: F) -> Result<Ptr<P>, F> {
        if let Some(inx) = self.freelist_root {
            let ptr = Ptr::from_raw(inx, self.gen_nz());
            self.unwrap_replace_free(inx, (self.gen_p(), create(ptr)));
            self.len += 1;
            Ok(ptr)
        } else {
            Err(create)
        }
    }

    /// Inserts `t` into the arena and returns a `Ptr` to it. This function
    /// allocates if capacity in the arena runs out.
    pub fn insert(&mut self, t: T) -> Ptr<P> {
        match self.try_insert(t) {
            Ok(inx) => inx,
            Err(t) => {
                // double the allocation size
                let mut additional = self.m.len();
                if additional == 0 {
                    // need at least one
                    additional = 1;
                }
                self.reserve(additional);
                // can't unwrap unless T: Debug
                match self.try_insert(t) {
                    Ok(p) => p,
                    Err(_) => unreachable!(),
                }
            }
        }
    }

    /// Inserts the `T` returned by `create` into the arena and returns a `Ptr`
    /// to it. `create` is given the the same `Ptr` that is returned, which is
    /// useful for initialization of immutable structures that need to reference
    /// themselves. This function allocates if capacity in the arena runs out.
    pub fn insert_with<F: FnOnce(Ptr<P>) -> T>(&mut self, create: F) -> Ptr<P> {
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
        let ptr = Ptr::from_raw(inx, self.gen_nz());
        self.unwrap_replace_free(inx, (self.gen_p(), create(ptr)));
        self.len += 1;
        ptr
    }

    /// Returns if `p` is a valid pointer
    pub fn contains(&self, p: Ptr<P>) -> bool {
        match self.m.get(p.get_raw()) {
            Some(Allocated(gen, _)) => *gen == p.gen_p(),
            _ => false,
        }
    }

    /// Returns a reference to a `T` pointed to by `p`. Returns `None` if `p` is
    /// invalid.
    pub fn get(&self, p: Ptr<P>) -> Option<&T> {
        match self.m.get(p.get_raw()) {
            Some(Allocated(gen, t)) => {
                if *gen != p.gen_p() {
                    None
                } else {
                    Some(t)
                }
            }
            _ => None,
        }
    }

    /// Returns a mutable reference to a `T` pointed to by `p`. Returns `None`
    /// if `p` is invalid.
    pub fn get_mut(&mut self, p: Ptr<P>) -> Option<&mut T> {
        let p = *p.borrow();
        match self.m.get_mut(p.get_raw()) {
            Some(Allocated(gen, t)) => {
                if *gen != p.gen_p() {
                    None
                } else {
                    Some(t)
                }
            }
            _ => None,
        }
    }

    /// Removes the `T` pointed to by `p`, returns the `T`, and invalidates old
    /// `Ptr`s to the `T`. Does no invalidation and returns `None` if `p` is
    /// invalid.
    pub fn remove(&mut self, p: Ptr<P>) -> Option<T> {
        let freelist_ptr = if let Some(free) = self.freelist_root {
            // points to previous root
            free
        } else {
            // points to itself
            p.get_raw()
        };
        let allocation = self.m.get_mut(p.get_raw())?;
        let old = mem::replace(allocation, Free(freelist_ptr));
        match old {
            Free(old_free) => {
                // undo
                *allocation = Free(old_free);
                None
            }
            Allocated(gen, old_t) => {
                if gen != p.gen_p() {
                    // undo
                    *allocation = Allocated(gen, old_t);
                    None
                } else {
                    // in both cases the new root is the entry we just removed
                    self.freelist_root = Some(p.get_raw());
                    self.len -= 1;
                    self.inc_gen();
                    Some(old_t)
                }
            }
        }
    }

    /// For every `T` in the arena, `pred` is called with a tuple of the `Ptr`
    /// to that `T` and a mutable reference to the `T`. If `pred` returns `true`
    /// that `T` is dropped and pointers to it invalidated.
    pub fn remove_by<F: FnMut(Ptr<P>, &mut T) -> bool>(&mut self, mut pred: F) {
        for (inx, entry) in self.m.iter_mut().enumerate() {
            if let Allocated(p, t) = entry {
                if pred(Ptr::from_raw(inx, PtrTrait::get(p)), t) {
                    self.len -= 1;
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
    pub fn invalidate(&mut self, p: Ptr<P>) -> Option<Ptr<P>> {
        match self.m.get(p.get_raw()) {
            Some(Allocated(gen, _)) => {
                if *gen != p.gen_p() {
                    return None
                }
            }
            _ => return None,
        }
        // redo to get around borrowing issues
        self.inc_gen();
        let new_gen = self.gen_p();
        match self.m.get_mut(p.get_raw()) {
            Some(Allocated(gen, _)) => {
                *gen = new_gen;
                Some(Ptr::from_raw(p.get_raw(), self.gen_nz()))
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
    pub fn replace_and_keep_gen(&mut self, p: Ptr<P>, new: T) -> Result<T, T> {
        let old_gen = match self.m.get(p.get_raw()) {
            Some(Allocated(gen, _)) => {
                if *gen != p.gen_p() {
                    return Err(new)
                }
                *gen
            }
            _ => return Err(new),
        };
        let old = mem::replace(
            self.m.get_mut(p.get_raw()).unwrap(),
            Allocated(old_gen, new),
        );
        match old {
            Allocated(_, old) => Ok(old),
            _ => unreachable!(),
        }
    }

    /// Replaces the `T` pointed to by `p` with `new`, returns a tuple of the
    /// new pointer and old `T`, and updates the internal generation
    /// counter so that previous `Ptr`s to this allocation are invalidated.
    ///
    /// # Errors
    ///
    /// Does no invalidation and returns ownership of `new` if `p` is invalid
    pub fn replace_and_update_gen(&mut self, p: Ptr<P>, new: T) -> Result<(Ptr<P>, T), T> {
        match self.m.get(p.get_raw()) {
            Some(Allocated(gen, _)) => {
                if *gen != p.gen_p() {
                    return Err(new)
                }
            }
            _ => return Err(new),
        }
        self.inc_gen();
        let new_gen = self.gen_p();
        let old = mem::replace(
            self.m.get_mut(p.get_raw()).unwrap(),
            Allocated(new_gen, new),
        );
        match old {
            Allocated(_, old) => Ok((Ptr::from_raw(p.get_raw(), PtrTrait::get(&new_gen)), old)),
            _ => unreachable!(),
        }
    }

    /// Drops all `T` from the arena and invalidates all pointers previously
    /// created from it. This has no effect on allocated capacity.
    pub fn clear(&mut self) {
        // drop all `T` and recreate the freelist
        for i in 1..self.m.len() {
            *self.m.get_mut(i.wrapping_sub(1)).unwrap() = Free(i);
        }
        if !self.m.is_empty() {
            // the last freelist node points to itself
            let last = self.m.len().wrapping_sub(1);
            *self.m.get_mut(last).unwrap() = Free(last);
            self.freelist_root = Some(0);
        } else {
            self.freelist_root = None;
        }
        self.inc_gen();
        self.len = 0;
    }

    /// Performs an [Arena::clear] and resets capacity to 0
    pub fn clear_and_shrink(&mut self) {
        self.m.clear();
        self.m.shrink_to_fit();
        self.freelist_root = None;
        self.inc_gen();
        self.len = 0;
    }

    /// Like [Arena::clone_from] except the `Clone` bound is not required
    /// and `source` can have arbitrary `U`. For every `U`, the `P` pointing to
    /// that `U` and a reference to itself is passed to `map` to generate
    /// the corresponding `T` in `self`. Validity is cloned with a `Ptr<P>`
    /// being able to reference `U` in the `source` arena and `T` in `self`.
    pub fn clone_from_with<U, F: FnMut(Ptr<P>, &U) -> T>(
        &mut self,
        source: &Arena<P, U>,
        mut map: F,
    ) {
        // exponential growth mitigation factor, absolutely do not use `self.m.capacity`
        // in the extra freelist additions
        let old_virtual_capacity = self.m.len();
        self.gen = source.gen;
        self.len = source.len;
        // Invariants are temporarily broken, use only methods on `m`.
        // clearing first makes `self.m.reserve` cheaper by not needing to copy
        self.m.clear();
        if self.m.capacity() < source.m.len() {
            self.m
                .reserve(source.m.len().wrapping_sub(self.m.capacity()));
        }
        for i in 0..source.m.len() {
            let new = match source.m.get(i).unwrap() {
                // copy `source` freelist
                Free(inx) => Free(*inx),
                // map `source` allocated
                Allocated(gen, u) => Allocated(*gen, map(Ptr::from_raw(i, PtrTrait::get(gen)), u)),
            };
            self.m.push(new);
        }

        for i in self.m.len().wrapping_add(1)..old_virtual_capacity {
            // point to next
            self.m.push(Free(i));
        }
        if self.m.len() < old_virtual_capacity {
            // new root starting at extension of `self.m` beyond `source.m`
            self.freelist_root = Some(source.m.len());
            self.m.push(match source.freelist_root {
                // points to old root
                Some(inx) => Free(inx),
                // points to itself
                None => Free(self.m.len()),
            });
        } else {
            self.freelist_root = source.freelist_root;
        }
    }
}
