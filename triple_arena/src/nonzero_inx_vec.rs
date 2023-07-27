use alloc::alloc;
use core::{alloc::Layout, cmp::max, mem, num::NonZeroUsize, ptr};

// The field accesses are especially unsafe such that we want only a minimal
// subset accessing them
mod guard {
    use core::{marker::PhantomData, mem, ptr};

    /// This is intended for the backing of arena-like data structures that pass
    /// out independent indexes. It is important that these indexes can be a
    /// `NonZero` integer for memory optimization purposes. This structure is
    /// not ever intended to support slices and zero indexing like a normal
    /// `Vec`. It includes optimizations such as pre-offsetting the allocation
    /// pointer so that `get`s and `get_mut`s only need a single addition in
    /// machine code to arrive at the destination address, rather than there
    /// being an unused allocation at the beginning or there being decrement
    /// penalties for every access.
    pub struct NonZeroInxVec<T> {
        /// When `_cap != 0`, this is offset by `pointer::wrapping_offset(-1)`
        /// from the allocation
        ///
        /// We cannot use a `NonNull` because this involves an intermediate from
        /// a wrapping_offset, and `NonNull` absolutely requires that it not be
        /// null. We use `*const T` for variance and a `PhantomData`.
        _ptr: *const T,
        _cap: usize,
        _len: usize,
        _boo: PhantomData<T>,
    }

    impl<T> NonZeroInxVec<T> {
        /// Constructs a new, empty `NonZeroInxVec<T>`. The vector will not
        /// allocate until elements are pushed onto it or
        /// [NonZeroInxVec::reserve] is called.
        ///
        /// ZSTs are currently not supported.
        pub const fn new() -> Self {
            assert!(mem::size_of::<T>() != 0, "TODO: implement ZST support");
            NonZeroInxVec {
                _ptr: ptr::null(),
                _len: 0,
                _cap: 0,
                _boo: PhantomData,
            }
        }

        /// Set the pointer with respect to the start of the allocation
        #[inline]
        pub(super) unsafe fn set_allocation_ptr(&mut self, new_ptr: *const T) {
            self._ptr = new_ptr.wrapping_offset(-1);
        }

        /// Get the pointer with respect to the start of the allocation
        ///
        /// NOTE: only ever use `wrapping_add` or `wrapping_offset` with this
        /// pointer
        #[inline]
        pub(super) const fn allocation_ptr(&self) -> *const T {
            self._ptr.wrapping_offset(1)
        }

        /// Get the pointer with respect to the start of the allocation
        ///
        /// NOTE: only ever use `wrapping_add` or `wrapping_offset` with this
        /// pointer
        #[inline]
        pub(super) const fn allocation_ptr_mut(&self) -> *mut T {
            self._ptr.wrapping_offset(1) as *mut T
        }

        /// Get the pointer with respect to nonzero indexing
        ///
        /// NOTE: only ever use `wrapping_add` or `wrapping_offset` with this
        /// pointer
        #[inline]
        pub(super) const fn nonzero_index_ptr(&self) -> *const T {
            self._ptr
        }

        /// Get the pointer with respect to nonzero indexing
        ///
        /// NOTE: only ever use `wrapping_add` or `wrapping_offset` with this
        /// pointer
        #[inline]
        pub(super) const fn nonzero_index_ptr_mut(&self) -> *mut T {
            self._ptr as *mut T
        }

        /// Sets the raw capacity
        #[inline]
        pub(super) unsafe fn set_capacity(&mut self, new_capacity: usize) {
            self._cap = new_capacity;
        }

        /// Get the number of elements this vector can hold without reallocating
        #[inline]
        pub const fn capacity(&self) -> usize {
            self._cap
        }

        /// Sets the raw length
        #[inline]
        pub(super) unsafe fn set_len(&mut self, new_len: usize) {
            self._len = new_len;
        }

        /// Get the number of elements, or the length
        #[inline]
        pub const fn len(&self) -> usize {
            self._len
        }
    }
}

pub use guard::NonZeroInxVec;

unsafe impl<T: Send> Send for NonZeroInxVec<T> {}
unsafe impl<T: Sync> Sync for NonZeroInxVec<T> {}

// TODO use the `#[may_dangle]` version in the future
// https://doc.rust-lang.org/nomicon/phantom-data.html
impl<T> Drop for NonZeroInxVec<T> {
    fn drop(&mut self) {
        self.clear_and_shrink()
    }
}

impl<T> NonZeroInxVec<T> {
    #[inline]
    fn layout(&self) -> Layout {
        Layout::array::<T>(self.capacity()).unwrap()
    }

    /// Returns if `self` has no elements
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Reserves capacity such that `self.capacity()` becomes at least
    /// `self.len() + additional`.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    pub fn reserve(&mut self, additional: usize) {
        // if this is ever changed, check places in the file where `reserve` is called
        let new_cap = if self.capacity() == 0 {
            // for small types we want to allocate more than a single value of capacity
            let minimum = mem::size_of::<[usize; 32]>()
                .checked_div(mem::size_of::<T>())
                .unwrap_or(1)
                .clamp(1, isize::MAX as usize);
            // advantageous for common use cases of reserving an amount from a zero
            // capacity, where the user probably knows the exact needed amount
            max(minimum, additional)
        } else {
            let minimum = self.len().wrapping_add(additional);
            let bumped = minimum.next_power_of_two();
            if bumped <= self.capacity() {
                // already have the needed capacity
                return
            }
            bumped
        };

        // this checks that the new capacity is not larger than `isize::MAX` bytes
        let new_layout = Layout::array::<T>(new_cap)
            .expect("`NonZeroInxVec::reserve` layout capacity overflow beyond `isize::MAX` bytes");

        // Safety: layout is for a nonzero sized allocation, we choose whether
        // to allocate or reallocate correctly, nulls from the allocator are
        // handled, we set the new allocation pointer and new capacity
        // correctly
        unsafe {
            let new_ptr = if self.capacity() == 0 {
                // if we previously had no allocation
                alloc::alloc(new_layout)
            } else {
                // reallocate
                let old_layout = self.layout();
                let old_ptr = self.allocation_ptr_mut() as *mut u8;
                alloc::realloc(old_ptr, old_layout, new_layout.size())
            };
            if new_ptr.is_null() {
                alloc::handle_alloc_error(new_layout)
            }
            self.set_allocation_ptr(new_ptr as *mut T);
            self.set_capacity(new_cap)
        }
    }

    /// Clears all elements but keeps capacity
    pub fn clear(&mut self) {
        // LLVM is pretty good at removing side effect free code
        while self.pop().is_some() {}
    }

    /// Clears all elements and deallocates all capacity
    pub fn clear_and_shrink(&mut self) {
        // make sure to drop all elements properly
        self.clear();
        if self.capacity() != 0 {
            // Safety: we are only deallocating if there is nonzero capacity, and we are
            // using the right pointer and layout, we also set capacity to zero
            unsafe {
                alloc::dealloc(self.allocation_ptr() as *mut u8, self.layout());
                self.set_capacity(0);
            }
        }
    }

    /// Appends an element to the back of the collection and returns an index to
    /// it.
    pub fn push(&mut self, t: T) -> NonZeroUsize {
        if self.len() == self.capacity() {
            // does proper first initialization or next power of two expansion
            self.reserve(1);
        }
        // Safety: We use `nonzero_index_ptr_mut().wrapping_offset(new_len)` and
        // increment the length into the allocation. `self.len()` is not more than
        // `isize::MAX - 1` so that `NonZeroUsize` can be constructed from the
        // incremented `new_len`.
        unsafe {
            let new_len = self.len().wrapping_add(1);
            self.set_len(new_len);
            ptr::write(self.nonzero_index_ptr_mut().wrapping_add(new_len), t);
            NonZeroUsize::new_unchecked(new_len)
        }
    }

    /// Removes the last element from the vector and returns it, or `None` if
    /// the vector is empty.
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            // Safety: we use `nonzero_index_ptr().wrapping_offset(old_len)` and decrement
            // the length on a nonzero length vector
            unsafe {
                let old_len = self.len();
                self.set_len(old_len.wrapping_sub(1));
                Some(ptr::read(self.nonzero_index_ptr().wrapping_add(old_len)))
            }
        }
    }

    /// Gets an immutable reference to the element at `inx`. The first element
    /// is indexed by 1 instead of 0. Returns `None` if `inx.get() >
    /// self.len()`.
    #[inline]
    pub fn get(&self, inx: NonZeroUsize) -> Option<&T> {
        if inx.get() > self.len() {
            None
        } else {
            // Safety: The first element is 1 so that the `wrapping_offset(-1)` is undone,
            // we use `inx.get() > self.len()` instead of `inx.get >= self.len()`
            unsafe { Some(&*self.nonzero_index_ptr().wrapping_add(inx.get())) }
        }
    }

    /// Gets a mutable reference to the element at `inx`. The first element is
    /// indexed by 1 instead of 0. Returns `None` if `inx.get() > self.len()`.
    #[inline]
    pub fn get_mut(&mut self, inx: NonZeroUsize) -> Option<&mut T> {
        if inx.get() > self.len() {
            None
        } else {
            // Safety: The first element is 1 so that the `wrapping_offset(-1)` is undone,
            // we use `inx.get() > self.len()` instead of `inx.get >= self.len()`
            unsafe { Some(&mut *self.nonzero_index_ptr_mut().wrapping_add(inx.get())) }
        }
    }

    /// Gets two mutable references. Returns `None` if the indexes are equal or
    /// if bounds are violated.
    pub fn get2_mut(&mut self, inx0: NonZeroUsize, inx1: NonZeroUsize) -> Option<(&mut T, &mut T)> {
        if (inx0 == inx1) || (inx0.get() > self.len()) || (inx1.get() > self.len()) {
            None
        } else {
            // Safety: The first element is 1 so that the `wrapping_offset(-1)` is undone,
            // we check bounds and check that we aren't getting two mutable references from
            // the same element
            unsafe {
                Some((
                    &mut *self.nonzero_index_ptr_mut().wrapping_add(inx0.get()),
                    &mut *self.nonzero_index_ptr_mut().wrapping_add(inx1.get()),
                ))
            }
        }
    }

    /// Same as `get` except that bounds are not checked.
    ///
    /// # Safety
    ///
    /// `inx.get() <= self.len()` must be upheld
    #[inline]
    pub unsafe fn get_unchecked(&self, inx: NonZeroUsize) -> &T {
        // Safety: The first element is 1 so that the `wrapping_offset(-1)` is undone,
        // the function's safety section presupposes `inx.get <= self.len()`
        unsafe { &*self.nonzero_index_ptr().wrapping_add(inx.get()) }
    }

    /// Same as `get_mut` except that bounds are not checked.
    ///
    /// # Safety
    ///
    /// `inx.get() <= self.len()` must be upheld
    #[inline]
    pub unsafe fn get_unchecked_mut(&mut self, inx: NonZeroUsize) -> &mut T {
        // Safety: The first element is 1 so that the `wrapping_offset(-1)` is undone,
        // the function's safety section presupposes `inx.get <= self.len()`
        unsafe { &mut *self.nonzero_index_ptr_mut().wrapping_add(inx.get()) }
    }
}
