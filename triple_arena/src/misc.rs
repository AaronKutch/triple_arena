use crate::{Arena, InternalEntry::*, Ptr, PtrInx};

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
    ///
    /// # Note
    ///
    /// `self` must be treated like an entirely new arena, and old pointers
    /// should not be reused on it because of the generation counter overwrite.
    fn clone_from(&mut self, source: &Self) {
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
            self.m.push(source.m.get(i).unwrap().clone());
        }

        for i in self.m.len().wrapping_add(1)..old_virtual_capacity {
            // point to next
            self.m.push(Free(P::Inx::new(i)));
        }
        if self.m.len() < old_virtual_capacity {
            // new root starting at extension of `self.m` beyond `source.m`
            self.freelist_root = Some(P::Inx::new(source.m.len()));
            self.m.push(match source.freelist_root {
                // points to old root
                Some(inx) => Free(inx),
                // points to itself
                None => Free(P::Inx::new(self.m.len())),
            });
        } else {
            self.freelist_root = source.freelist_root;
        }
    }
}
