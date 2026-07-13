//! This is a safer implementation of the heap backing for reference

use alloc::vec::Vec;
use core::num::NonZeroUsize;

use crate::utils::{AllocError, NonZeroInxGenericStack};

// Note: an older version of `triple_arena` had manually managed allocations and
// an extreme microoptimization where we pre-offset the allocation pointer so
// that `get`s etc only need a single addition in machine code to arrive at the
// destination address. But on most architectures, even RISC-V, they can have an
// immediate offset to their loads and zero instructions are saved. Also, it
// precluded `NonNull` optimizations from existing on the struct.

/// The standard heap-based unlimited `max_capacity` implementation of
/// [NonZeroInxGenericStack]
pub struct NonZeroInxVec<T> {
    v: Vec<T>,
}

// Safety: we follow the requirements of the trait
unsafe impl<T> NonZeroInxGenericStack<T> for NonZeroInxVec<T> {
    fn new() -> Self {
        Self { v: Vec::new() }
    }

    fn len(&self) -> usize {
        self.v.len()
    }

    fn capacity(&self) -> usize {
        self.v.capacity()
    }

    fn max_capacity(&self) -> Option<usize> {
        None
    }

    fn reallocate_min_capacity(&mut self, min_capacity: usize) -> Result<(), AllocError> {
        if min_capacity > self.capacity() {
            self.v
                .try_reserve(min_capacity - self.len())
                .map_err(|_| AllocError)?;
        } else if min_capacity < self.capacity() {
            // TODO change when `try_shrink_to` is stabilized

            // the only stable way to do it
            let mut v = Vec::new();
            v.try_reserve(min_capacity).map_err(|_| AllocError)?;
            v.append(&mut self.v);
            self.v = v;
        }
        Ok(())
    }

    fn push_within_capacity(&mut self, t: T) -> Result<(NonZeroUsize, &mut T), T> {
        if self.v.len() < self.v.capacity() {
            self.v.push(t);
            Ok((
                unsafe { NonZeroUsize::new_unchecked(self.len()) },
                self.v.last_mut().unwrap(),
            ))
        } else {
            Err(t)
        }
    }

    unsafe fn get_unchecked(&self, inx: NonZeroUsize) -> &T {
        unsafe { self.v.get_unchecked(inx.get().wrapping_sub(1)) }
    }

    unsafe fn get_unchecked_mut(&mut self, inx: NonZeroUsize) -> &mut T {
        unsafe { self.v.get_unchecked_mut(inx.get().wrapping_sub(1)) }
    }

    unsafe fn get_disjoint_unchecked_mut<const N: usize>(
        &mut self,
        indices: [NonZeroUsize; N],
    ) -> [&mut T; N] {
        unsafe {
            self.v
                .get_disjoint_unchecked_mut(indices.map(|inx| inx.get().wrapping_sub(1)))
        }
    }

    fn pop(&mut self) -> Option<T> {
        self.v.pop()
    }

    fn clear(&mut self) {
        self.v.clear()
    }
}
