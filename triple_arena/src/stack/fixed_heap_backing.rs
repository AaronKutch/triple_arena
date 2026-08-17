use alloc::{boxed::Box, vec::Vec};
use core::{
    mem::{self, MaybeUninit},
    num::NonZeroUsize,
    ptr,
};

use crate::{
    errors::{AllocError, NotWithinCapacityError, ReallocationError},
    utils::traits::{NonZeroInxGenericStack, NonZeroInxGenericStackPushEntryTrait},
};

// TODO For now we are optimizing for struct size, if it happens that we add
// !Overwrite/!Move/!Drop types (for which this would be useful), then we should
// add yet one more type that is both fixed but limitable to deal with allocator
// overallocation and dynamic limit choices

/// The standard heap-based fixed capacity implementation (based on
/// `Box<[MaybeUninit<...>]>`) of [NonZeroInxGenericStack]. Note that
/// [new](NonZeroInxGenericStack::new) for this type will create an unchangeable
/// zero capacity struct,
/// [with_min_capacity](NonZeroInxGenericStack::with_min_capacity) should be
/// used instead
pub struct NonZeroInxBoxedSlice<T> {
    v: Box<[MaybeUninit<T>]>,
    len: usize,
}

impl<T> Drop for NonZeroInxBoxedSlice<T> {
    fn drop(&mut self) {
        self.clear();
    }
}

/// The [NonZeroInxBoxedSlice] implementation of
/// [NonZeroInxGenericStackPushEntryTrait]
#[must_use]
pub struct NonZeroInxBoxedSlicePushEntry<'a, T> {
    this: &'a mut NonZeroInxBoxedSlice<T>,
}

impl<'a, T> NonZeroInxGenericStackPushEntryTrait<'a, T> for NonZeroInxBoxedSlicePushEntry<'a, T> {
    fn inx(&self) -> NonZeroUsize {
        // note this assumes that `push` is the only other mutable function
        // Safety: overflow from pushing was checked for before creating the entry
        unsafe { NonZeroUsize::new_unchecked(self.this.len.wrapping_add(1)) }
    }

    fn push(self, t: T) {
        let this = self.this;
        // Safety: the boxed slice is of length `LIMIT` and we had verified that
        // `self.len() + 1 <= LIMIT`
        unsafe {
            let next_len = NonZeroUsize::new_unchecked(this.len.wrapping_add(1));
            let internal_inx = this.len;
            this.v.get_unchecked_mut(internal_inx).write(t);
            this.len = next_len.get();
        }
    }
}

// Safety: we follow the requirements of the trait
unsafe impl<T> NonZeroInxGenericStack<T> for NonZeroInxBoxedSlice<T> {
    type PushEntry<'a>
        = NonZeroInxBoxedSlicePushEntry<'a, T>
    where
        Self: 'a;

    fn new() -> Self {
        Self {
            v: Box::from(Vec::new()),
            len: 0,
        }
    }

    fn with_min_capacity(min_capacity: usize) -> Result<Self, AllocError> {
        // TODO change when `try_with_capacity` is stabilized

        // the only stable way to do it
        let mut v = Vec::new();
        v.try_reserve(min_capacity).map_err(|_| AllocError)?;
        let capacity = if size_of::<T>() == 0 {
            // `Vec` always has a capacity of `usize::MAX` when `T` is a ZST, I would
            // normally say follow it, however I think the best approach in this specific
            // context with a fixed capacity boxed slice is to follow what was asked for
            min_capacity
        } else {
            v.capacity()
        };
        // Safety: `capacity <= v.capacity()`, and every `MaybeUninit<T>` is initialized
        // in the sense that any bit pattern is a valid value of the type
        unsafe {
            v.set_len(capacity);
        }
        Ok(Self {
            v: Box::from(v),
            len: 0,
        })
    }

    fn len(&self) -> usize {
        self.len
    }

    fn capacity(&self) -> usize {
        self.v.len()
    }

    fn max_capacity(&self) -> Option<usize> {
        Some(self.v.len())
    }

    fn reallocate_min_capacity(&mut self, min_capacity: usize) -> Result<(), ReallocationError> {
        if min_capacity > self.capacity() {
            Err(ReallocationError::BeyondMaxCapacity)
        } else {
            Ok(())
        }
    }

    fn entry_push_within_capacity(
        &mut self,
    ) -> Result<Self::PushEntry<'_>, NotWithinCapacityError> {
        // this accounts for ZSTs
        if self.len < self.v.len() {
            Ok(NonZeroInxBoxedSlicePushEntry { this: self })
        } else {
            Err(NotWithinCapacityError)
        }
    }

    unsafe fn get_unchecked(&self, inx: NonZeroUsize) -> &T {
        unsafe {
            self.v
                .get_unchecked(inx.get().wrapping_sub(1))
                .assume_init_ref()
        }
    }

    unsafe fn get_unchecked_mut(&mut self, inx: NonZeroUsize) -> &mut T {
        unsafe {
            self.v
                .get_unchecked_mut(inx.get().wrapping_sub(1))
                .assume_init_mut()
        }
    }

    unsafe fn get_disjoint_unchecked_mut<const N: usize>(
        &mut self,
        indices: [NonZeroUsize; N],
    ) -> [&mut T; N] {
        unsafe {
            self.v
                .get_unchecked_mut(..self.len)
                .get_disjoint_unchecked_mut(indices.map(|inx| inx.get().wrapping_sub(1)))
                .map(|x| x.assume_init_mut())
        }
    }

    fn pop(&mut self) -> Option<T> {
        self.len = self.len.checked_sub(1)?;
        // Safety: we initialized the entry at what is now `self.len`, and we return it
        // without running drop code
        unsafe {
            Some(
                mem::replace(self.v.get_unchecked_mut(self.len), MaybeUninit::uninit())
                    .assume_init(),
            )
        }
    }

    fn clear(&mut self) {
        // REF(zero_before_drop)
        let len = mem::replace(&mut self.len, 0);
        // Safety: everything up to `len` was initialized, and is dropped exactly once.
        // `drop_in_place` on a slice keeps dropping the remaining elements if one of
        // the drops panics, so they are not leaked either.
        unsafe {
            let to_drop: *mut [T] =
                self.v.get_unchecked_mut(..len) as *mut [MaybeUninit<T>] as *mut [T];
            ptr::drop_in_place(to_drop);
        }
    }
}
