use core::{
    array,
    mem::{self, MaybeUninit},
    num::NonZeroUsize,
};

use crate::utils::{AllocError, NonZeroInxGenericStack};

// use "LIMIT" so we don't collide with usages of `const N: usize` in functions
// like `get_disjoint_unchecked`, also "LIMIT" is more immediately apparent for
// something that has a capacity

pub struct NonZeroInxArray<T, const LIMIT: usize> {
    // in actual layout it is preferred for this to come first
    len: usize,
    array: [MaybeUninit<T>; LIMIT],
}

impl<T, const LIMIT: usize> Drop for NonZeroInxArray<T, LIMIT> {
    fn drop(&mut self) {
        self.clear();
    }
}

// Safety: we use safe ops internally and follow the requirements of the trait
unsafe impl<T, const LIMIT: usize> NonZeroInxGenericStack<T> for NonZeroInxArray<T, LIMIT> {
    fn new() -> Self {
        Self {
            len: 0,
            array: array::from_fn(|_| MaybeUninit::uninit()),
        }
    }

    fn len(&self) -> usize {
        self.len
    }

    fn capacity(&self) -> usize {
        LIMIT
    }

    fn capacity_limit(&self) -> Option<usize> {
        Some(LIMIT)
    }

    fn ensure_capacity(&mut self, min_capacity: usize) -> Result<(), AllocError> {
        if min_capacity > LIMIT {
            Err(AllocError)
        } else {
            Ok(())
        }
    }

    fn push(&mut self, t: T) -> Result<(NonZeroUsize, &mut T), T> {
        // fine because of isize::MAX limits
        if self.len.wrapping_add(1) > LIMIT {
            Err(t)
        } else {
            // Safety: the array is of length `LIMIT` and we have verified that `self.len()
            // - 1 <= LIMIT`
            unsafe {
                let internal_inx = self.len;
                self.array.get_unchecked_mut(internal_inx).write(t);
                self.len = self.len.wrapping_add(1);
                Ok((
                    NonZeroUsize::new_unchecked(self.len()),
                    self.array.get_unchecked_mut(internal_inx).assume_init_mut(),
                ))
            }
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
                .assume_init_mut()
                .get_disjoint_unchecked_mut(indices.map(|inx| inx.get().wrapping_sub(1)))
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

    fn clear_and_shrink(&mut self) {
        self.clear();
    }
}
