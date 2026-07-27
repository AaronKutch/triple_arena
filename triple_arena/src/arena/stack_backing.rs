use core::{
    array,
    mem::{self, MaybeUninit},
    num::NonZeroUsize,
};

use crate::{
    AllocError, NotWithinCapacityError, ReallocationError,
    utils::traits::{NonZeroInxGenericStack, NonZeroInxGenericStackPushEntryTrait},
};

// use "LIMIT" so we don't collide with usages of `const N: usize` in functions
// like `get_disjoint_unchecked`, also "LIMIT" is more immediately apparent for
// something that has a capacity

pub struct NonZeroInxArray<T, const LIMIT: usize> {
    // in actual layout with this potentially long array it is preferred for this to come first
    len: usize,
    array: [MaybeUninit<T>; LIMIT],
}

impl<T, const LIMIT: usize> Drop for NonZeroInxArray<T, LIMIT> {
    fn drop(&mut self) {
        self.clear();
    }
}

pub struct NonZeroInxArrayPushEntry<'a, T, const LIMIT: usize> {
    this: &'a mut NonZeroInxArray<T, LIMIT>,
}

impl<'a, T, const LIMIT: usize> NonZeroInxGenericStackPushEntryTrait<'a, T>
    for NonZeroInxArrayPushEntry<'a, T, LIMIT>
{
    fn inx(&self) -> NonZeroUsize {
        // note this assumes that `push` is the only other mutable function
        // Safety: overflow from pushing was checked for before creating the entry
        unsafe { NonZeroUsize::new_unchecked(self.this.len.wrapping_add(1)) }
    }

    fn push(self, t: T) {
        let this = self.this;
        // Safety: the array is of length `LIMIT` and we had verified that
        // `self.len() + 1 <= LIMIT`
        unsafe {
            let next_len = NonZeroUsize::new_unchecked(this.len.wrapping_add(1));
            let internal_inx = this.len;
            this.array.get_unchecked_mut(internal_inx).write(t);
            this.len = next_len.get();
        }
    }
}

// Safety: we follow the requirements of the trait
unsafe impl<T, const LIMIT: usize> NonZeroInxGenericStack<T> for NonZeroInxArray<T, LIMIT> {
    type PushEntry<'a>
        = NonZeroInxArrayPushEntry<'a, T, LIMIT>
    where
        Self: 'a;

    fn new() -> Self {
        Self {
            len: 0,
            array: array::from_fn(|_| MaybeUninit::uninit()),
        }
    }

    fn with_min_capacity(min_capacity: usize) -> Result<Self, AllocError> {
        if min_capacity > LIMIT {
            Err(AllocError)
        } else {
            Ok(Self::new())
        }
    }

    fn len(&self) -> usize {
        self.len
    }

    fn capacity(&self) -> usize {
        LIMIT
    }

    fn max_capacity(&self) -> Option<usize> {
        Some(LIMIT)
    }

    fn reallocate_min_capacity(&mut self, min_capacity: usize) -> Result<(), ReallocationError> {
        if min_capacity > LIMIT {
            Err(ReallocationError::BeyondMaxCapacity)
        } else {
            Ok(())
        }
    }

    fn entry_push_within_capacity(
        &mut self,
    ) -> Result<Self::PushEntry<'_>, NotWithinCapacityError> {
        // need to account for `T` being a ZST, can't rely on isize::MAX limits
        if let Some(next_len) = self.len.checked_add(1) {
            if next_len <= LIMIT {
                Ok(NonZeroInxArrayPushEntry { this: self })
            } else {
                Err(NotWithinCapacityError)
            }
        } else {
            Err(NotWithinCapacityError)
        }
    }

    unsafe fn get_unchecked(&self, inx: NonZeroUsize) -> &T {
        unsafe {
            self.array
                .get_unchecked(inx.get().wrapping_sub(1))
                .assume_init_ref()
        }
    }

    unsafe fn get_unchecked_mut(&mut self, inx: NonZeroUsize) -> &mut T {
        unsafe {
            self.array
                .get_unchecked_mut(inx.get().wrapping_sub(1))
                .assume_init_mut()
        }
    }

    unsafe fn get_disjoint_unchecked_mut<const N: usize>(
        &mut self,
        indices: [NonZeroUsize; N],
    ) -> [&mut T; N] {
        unsafe {
            self.array
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
                mem::replace(
                    self.array.get_unchecked_mut(self.len),
                    MaybeUninit::uninit(),
                )
                .assume_init(),
            )
        }
    }

    fn clear(&mut self) {
        // run drop code
        // Safety: everything up to `self.len` was initialized, we are dropping
        // everything once and setting `len` to zero
        unsafe {
            for t in self.array.get_unchecked_mut(..self.len) {
                t.assume_init_drop();
            }
            self.len = 0;
        }
    }
}
