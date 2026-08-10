use core::fmt;
use std::{cell::RefCell, collections::HashMap, marker::PhantomData, num::NonZeroU64, rc::Rc};

use stacked_errors::StackedError;
use star_rng::StarRng;

/// This is for test types where dropping in a certain state causes a panic (to
/// prevent silent failures), but we want to be able to cause an internal drop
/// that does the same thing but returning an error we can handle
pub trait TryInternalDrop {
    fn try_internal_drop(&mut self) -> Result<(), StackedError>;
}

// `CdGen<D>` could have potentially also been a combined random access list and
// map type that many tests use such that the `D` is what is mapped to, but
// often those become full custom constructions that map to `Ck` at the end.
// Instead, `D` is a domain separator if there are different `CdGen`s in play.
// Note that if `Ck`s from the wrong `CdGen` are used, it will always end up
// causing a failure unless perfect deterministic swaps occur

#[derive(Clone, Copy)]
pub struct Ck<D: Copy>(usize, NonZeroU64, PhantomData<fn() -> D>); // index and a generation

impl<D: Copy> core::hash::Hash for Ck<D> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
        self.1.hash(state);
    }
}

impl<D: Copy> PartialEq for Ck<D> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0 && self.1 == other.1
    }
}

impl<D: Copy> Eq for Ck<D> {}

impl<D: Copy> fmt::Debug for Ck<D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // the generation in this case is unique per key, just use it
        f.debug_tuple("Ck").field(&self.1).finish()
    }
}

impl<D: Copy> fmt::Display for Ck<D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt::Debug::fmt(&self, f)
    }
}

// a generational arena is perfect for this, but we implement a quick and dirty
// one
struct Inner<D: Copy> {
    // also the generation, and it always counts up, and 1 is invalid
    counter: NonZeroU64,
    // generation and `D`, index is implicit
    slots: Vec<(NonZeroU64, Option<D>)>,
    // unused indexes
    freelist: Vec<usize>,
    // prevent panic on drop if manually handled
    drop_handled: bool,
}

/// When this drops, this panics if not all [Cd]s generated from this have been
/// dropped. The `D` here is for domain separation.
pub struct CdGen<D: Copy + Default> {
    inner: Rc<RefCell<Inner<D>>>,
}

impl<D: Copy + Default> Drop for CdGen<D> {
    fn drop(&mut self) {
        if !self.inner.borrow().drop_handled
            && let Err(e) = self.internal_drop()
        {
            panic!("{e}");
        }
    }
}

impl<D: Copy + Default> TryInternalDrop for CdGen<D> {
    fn try_internal_drop(&mut self) -> Result<(), StackedError> {
        self.internal_drop().map_err(|e| StackedError::from_err(e))
    }
}

impl<D: Copy + Default> fmt::Debug for CdGen<D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CdGen").finish()
    }
}

impl<D: Copy + Default> CdGen<D> {
    pub fn new() -> Self {
        Self {
            inner: Rc::new(RefCell::new(Inner {
                counter: NonZeroU64::new(2).unwrap(),
                slots: vec![],
                freelist: vec![],
                drop_handled: false,
            })),
        }
    }

    /// Returns the `Ck` also because it is almost always wanted
    pub fn new_cd(&mut self) -> (Ck<D>, Cd<D>) {
        let mut inner = self.inner.borrow_mut();
        let counter = inner.counter;
        inner.counter = inner.counter.checked_add(1).unwrap();
        let i = if let Some(free_i) = inner.freelist.pop() {
            inner.slots[free_i] = (counter, Some(D::default()));
            free_i
        } else {
            let new_i = inner.slots.len();
            inner.slots.push((counter, Some(D::default())));
            new_i
        };
        drop(inner);
        let key = Ck(i, counter, PhantomData);
        (key, Cd {
            key,
            inner: Rc::clone(&self.inner),
        })
    }

    pub fn len(&self) -> usize {
        let inner = self.inner.borrow();
        inner.slots.len().checked_sub(inner.freelist.len()).unwrap()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn internal_drop(&mut self) -> Result<(), &'static str> {
        let inner = &mut self.inner.borrow_mut();
        if inner.freelist.len() != inner.slots.len() && !std::thread::panicking() {
            inner.drop_handled = true;
            Err(
                "A CdGen test struct generator has been dropped without all of its generated \
                 `Cd`s being dropped first",
            )
        } else {
            Ok(())
        }
    }
}

/// A Counted Drop test struct. Records each drop with its corresponding
/// [CdGen], and panics if a double drop is seen.
pub struct Cd<D: Copy> {
    key: Ck<D>,
    inner: Rc<RefCell<Inner<D>>>,
}

impl<D: Copy> fmt::Debug for Cd<D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Cd").field(&self.key.1).finish()
    }
}

impl<D: Copy> Cd<D> {
    // don't implement PartialEq on Cd

    /// Use this to compare `Cd`s
    pub fn key(&self) -> Ck<D> {
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
}

impl<D: Copy> Drop for Cd<D> {
    fn drop(&mut self) {
        self.check();
        let inner = &mut self.inner.borrow_mut();
        // guarantee invalid
        inner.slots[self.key.0].0 = NonZeroU64::new(1).unwrap();
        inner.slots[self.key.0].1.take();
        inner.freelist.push(self.key.0);
    }
}

/// Used for recording a set of `Ck`s and O(1) random selection
#[derive(Debug)]
pub struct CkMap<D: Copy, T> {
    map: HashMap<Ck<D>, T>,
    list: Vec<Ck<D>>,
}

impl<D: Copy, T> CkMap<D, T> {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
            list: vec![],
        }
    }

    pub fn insert(&mut self, k: Ck<D>, t: T) {
        assert!(self.map.insert(k, t).is_none());
        self.list.push(k);
    }

    pub fn len(&self) -> usize {
        self.list.len()
    }

    pub fn is_empty(&self) -> bool {
        self.list.is_empty()
    }

    pub fn get(&self, k: Ck<D>) -> Option<&T> {
        self.map.get(&k)
    }

    pub fn get_rand(&self, rng: &mut StarRng) -> Option<(Ck<D>, &T)> {
        let i = rng.index(self.list.len())?;
        let k = self.list.get(i).unwrap();
        Some((*k, self.map.get(k).unwrap()))
    }

    pub fn get_mut_rand(&mut self, rng: &mut StarRng) -> Option<(Ck<D>, &mut T)> {
        let i = rng.index(self.list.len())?;
        let k = self.list.get(i).unwrap();
        Some((*k, self.map.get_mut(k).unwrap()))
    }

    pub fn remove(&mut self, i: usize) -> Option<(Ck<D>, T)> {
        if i > self.len() {
            return None;
        }
        let k = self.list.swap_remove(i);
        Some((k, self.map.remove(&k).unwrap()))
    }

    pub fn remove_rand(&mut self, rng: &mut StarRng) -> Option<(Ck<D>, T)> {
        let i = rng.index(self.list.len())?;
        let k = self.list.swap_remove(i);
        Some((k, self.map.remove(&k).unwrap()))
    }

    pub fn clear(&mut self) {
        self.map.clear();
        self.list.clear();
    }
}
