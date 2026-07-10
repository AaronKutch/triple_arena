use core::fmt;
use std::{cell::RefCell, num::NonZeroU64, rc::Rc};

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct CdKey(usize, NonZeroU64); // index and a generation

impl fmt::Debug for CdKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // the generation in this case is unique per key, just use it
        f.debug_tuple("CdKey").field(&self.1).finish()
    }
}

impl fmt::Display for CdKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt::Debug::fmt(&self, f)
    }
}

// a generational arena is perfect for this, but we implement a quick and dirty
// one
struct Inner<T> {
    // also the generation, and it always counts up, and 1 is invalid
    counter: NonZeroU64,
    // generation and `T`, index is implicit
    slots: Vec<(NonZeroU64, Option<T>)>,
    // unused indexes
    freelist: Vec<usize>,
}

/// When this drops, this panics if not all [Cd]s have been dropped
pub struct CdGen<T> {
    inner: Rc<RefCell<Inner<T>>>,
}

impl<T> Drop for CdGen<T> {
    fn drop(&mut self) {
        let inner = &mut self.inner.borrow_mut();
        if inner.freelist.len() != inner.slots.len() && !std::thread::panicking() {
            panic!(
                "A CdGen test struct generator has been dropped without all of its generated \
                 `Cd`s being dropped first"
            );
        }
    }
}

impl<T> CdGen<T> {
    pub fn new() -> Self {
        Self {
            inner: Rc::new(RefCell::new(Inner {
                counter: NonZeroU64::new(2).unwrap(),
                slots: vec![],
                freelist: vec![],
            })),
        }
    }

    /// Returns the `CdKey` also because it is almost always wanted
    pub fn next(&mut self, t: T) -> (CdKey, Cd<T>) {
        let mut inner = self.inner.borrow_mut();
        let counter = inner.counter;
        inner.counter = inner.counter.checked_add(1).unwrap();
        let i = if let Some(free_i) = inner.freelist.pop() {
            inner.slots[free_i] = (counter, Some(t));
            free_i
        } else {
            let new_i = inner.slots.len();
            inner.slots.push((counter, Some(t)));
            new_i
        };
        drop(inner);
        let key = CdKey(i, counter);
        (key, Cd {
            key,
            inner: Rc::clone(&self.inner),
        })
    }
}

/// A Counted Drop test struct. Records each drop with its corresponding
/// [CdGen], and panics if a double drop is seen.
pub struct Cd<T> {
    key: CdKey,
    inner: Rc<RefCell<Inner<T>>>,
}

impl<T> fmt::Debug for Cd<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Cd").field(&self.key.1).finish()
    }
}

impl<T> Cd<T> {
    // don't implement PartialEq on Cd

    /// Use this to compare `Cd`s
    pub fn key(&self) -> CdKey {
        self.key
    }

    fn check(&self) {
        let inner = &mut self.inner.borrow();
        if inner.slots[self.key.0].0 != self.key.1 && !std::thread::panicking() {
            panic!(
                "A Cd test struct would be double dropped, key: {}",
                self.key
            );
        }
    }

    pub fn t<O, F: FnOnce(&mut T) -> O>(&self, f: F) -> O {
        self.check();
        let inner = &mut self.inner.borrow_mut();
        f(inner.slots[self.key.0].1.as_mut().unwrap())
    }
}

impl<T> Drop for Cd<T> {
    fn drop(&mut self) {
        self.check();
        let inner = &mut self.inner.borrow_mut();
        // guarantee invalid
        inner.slots[self.key.0].0 = NonZeroU64::new(1).unwrap();
        inner.slots[self.key.0].1.take();
        inner.freelist.push(self.key.0);
    }
}
