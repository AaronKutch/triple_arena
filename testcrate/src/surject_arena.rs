use core::fmt;
use std::{
    cmp::max,
    collections::{HashMap, HashSet},
};

use expect_test::Expect;
use stacked_errors::{StackableErr, StackedError, ensure, ensure_eq};
use star_rng::StarRng;
use triple_arena::{
    Arena, ChainArena, DirectArena, InvalidationResult, StackBacking, SurjectArena,
    errors::{ChainInsertionError, MaxCapacityReductionError, ReallocationError},
    traits::{Advancer, ArenaCloneFromWith, ArenaTrait, ChainArenaTrait, Ptr},
    utils::traits::{ArenaBacking, PtrGen, PtrInx},
};

use crate::{
    TestGen,
    basic_arena::{common_compact_fuzz_step250, gen_invalid},
    cdgen::{Cd, CdGen, Ck, CkMap, TryInternalDrop},
    misc::{D1, D2, D3, Meta},
};

/// The length that the fuzz stays around. This is large enough that surjects
/// commonly have several elements and that the canonicalizing operations have
/// long permutations to work through, and small enough that the `O(n^2)`
/// [ArenaTrait::compress_with] stays cheap.
pub const LIMIT: usize = 24;

/// The element type of the fuzzed arena
pub type TElement = Cd<()>;
/// The shared value type of the fuzzed arena
pub type TShared = Cd<D1>;
/// The arena that the interarena operations use
pub type A1<P> = SurjectArena<P, Cd<D2>, Cd<D3>, StackBacking<{ 4 * LIMIT }>>;

pub struct Stats {
    /// The limit that the test stays around (this is not necessarily exactly
    /// followed)
    pub test_limit: usize,
    /// If the capacity is fixed
    pub fixed_cap: Option<usize>,
    pub n: usize,
    pub iters999: Option<Expect>,
    /// The maximum `len` that the arena reached over the whole fuzz, to check
    /// that the test is actually stressing the lengths that it should be
    pub max_len: Option<Expect>,
    /// The maximum number of elements that a single surject reached
    pub max_len_surject: Option<Expect>,
    pub cd_gen: CdGen<()>,
    pub cd_gen1: CdGen<D1>,
    pub cd_gen2: CdGen<D2>,
    pub cd_gen3: CdGen<D3>,
}

impl fmt::Debug for Stats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Stats")
            .field("test_limit", &self.test_limit)
            .field("fixed_cap", &self.fixed_cap)
            .field("n", &self.n)
            .finish_non_exhaustive()
    }
}

impl TryInternalDrop for Stats {
    fn try_internal_drop(&mut self) -> Result<(), StackedError> {
        // every one of these has to be reached, or else the `CdGen`s that were
        // skipped would panic in their `Drop` and mask the real error
        let res0 = self.cd_gen.try_internal_drop().stack_err("cd_gen");
        let res1 = self.cd_gen1.try_internal_drop().stack_err("cd_gen1");
        let res2 = self.cd_gen2.try_internal_drop().stack_err("cd_gen2");
        let res3 = self.cd_gen3.try_internal_drop().stack_err("cd_gen3");
        let mut res = Ok(());
        for next in [res0, res1, res2, res3] {
            if let Err(e) = next {
                res = match res {
                    Ok(()) => Err(e),
                    Err(e0) => Err(e0.chain_errors(e)),
                };
            }
        }
        res
    }
}

/// The reference model of one element. The chain interlinks and the surject
/// membership are recorded as `Ck`s rather than as `Ptr`s, so that operations
/// which change every `Ptr` do not need to change them.
#[derive(Debug, Clone, Copy)]
pub struct TElem<P> {
    pub p: P,
    /// The shared value of the surject that this element is in
    pub s: Ck<D1>,
    /// Every surject is a cyclic chain, so these are never `None`
    pub prev: Ck<()>,
    pub next: Ck<()>,
}

/// The reference model of one surject
#[derive(Debug, Clone, Copy)]
pub struct TSurject {
    /// Any one element of the surject, for entering its chain
    pub any: Ck<()>,
    pub len: usize,
}

pub struct Model<P> {
    pub elements: CkMap<(), TElem<P>>,
    pub surjects: CkMap<D1, TSurject>,
}

impl<P: Ptr> Model<P> {
    pub fn new() -> Self {
        Self {
            elements: CkMap::new(),
            surjects: CkMap::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.elements.len()
    }

    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    pub fn len_shared(&self) -> usize {
        self.surjects.len()
    }

    pub fn clear(&mut self) {
        self.elements.clear();
        self.surjects.clear();
    }

    pub fn p(&self, k: Ck<()>) -> P {
        self.elements.get(k).unwrap().p
    }

    /// The chain of the surject that `k_init` is in, in the order that
    /// `advancer_surject` should advance over it
    pub fn chain(&self, k_init: Ck<()>) -> Vec<Ck<()>> {
        let mut res = vec![k_init];
        let mut cur = self.elements.get(k_init).unwrap().next;
        while cur != k_init {
            res.push(cur);
            cur = self.elements.get(cur).unwrap().next;
        }
        res
    }

    /// Inserts a whole new surject of the single element `k`
    pub fn insert_surject(&mut self, k: Ck<()>, s: Ck<D1>, p: P) {
        self.elements.insert(k, TElem {
            p,
            s,
            prev: k,
            next: k,
        });
        self.surjects.insert(s, TSurject { any: k, len: 1 });
    }

    /// Inserts `k` right after `k_target` in the chain of `k_target`
    pub fn insert(&mut self, k: Ck<()>, k_target: Ck<()>, p: P) {
        let target = *self.elements.get(k_target).unwrap();
        // handle the single link cyclic chain case by writing through the map twice
        // rather than through a stale copy
        self.elements.get_mut(k_target).unwrap().next = k;
        self.elements.get_mut(target.next).unwrap().prev = k;
        self.elements.insert(k, TElem {
            p,
            s: target.s,
            prev: k_target,
            next: target.next,
        });
        self.surjects.get_mut(target.s).unwrap().len += 1;
    }

    /// Removes just the element `k`, returning the shared value key if `k` was
    /// the last element of its surject
    pub fn remove(&mut self, k: Ck<()>) -> Option<Ck<D1>> {
        let e = self.elements.remove_key(k).unwrap();
        if e.next == k {
            // single link cyclic chain, the whole surject goes away
            self.surjects.remove_key(e.s).unwrap();
            return Some(e.s);
        }
        self.elements.get_mut(e.prev).unwrap().next = e.next;
        self.elements.get_mut(e.next).unwrap().prev = e.prev;
        let surject = self.surjects.get_mut(e.s).unwrap();
        surject.len -= 1;
        if surject.any == k {
            surject.any = e.next;
        }
        None
    }

    /// Removes the whole surject that `k` is in, returning the shared value key
    pub fn remove_surject(&mut self, k: Ck<()>) -> Ck<D1> {
        let s = self.elements.get(k).unwrap().s;
        for k in self.chain(k) {
            self.elements.remove_key(k).unwrap();
        }
        self.surjects.remove_key(s).unwrap();
        s
    }

    /// The model side of [SurjectArena::union], with `k0` being the element
    /// that keeps its shared value
    pub fn union(&mut self, k0: Ck<()>, k1: Ck<()>) -> Ck<D1> {
        let s0 = self.elements.get(k0).unwrap().s;
        let s1 = self.elements.get(k1).unwrap().s;
        for k in self.chain(k1) {
            self.elements.get_mut(k).unwrap().s = s0;
        }
        // `exchange_next` swaps the `next` endpoints of `k0` and `k1`, which joins
        // the two cyclic chains into one
        let n0 = self.elements.get(k0).unwrap().next;
        let n1 = self.elements.get(k1).unwrap().next;
        self.elements.get_mut(k0).unwrap().next = n1;
        self.elements.get_mut(k1).unwrap().next = n0;
        self.elements.get_mut(n1).unwrap().prev = k0;
        self.elements.get_mut(n0).unwrap().prev = k1;
        let len1 = self.surjects.remove_key(s1).unwrap().len;
        let surject0 = self.surjects.get_mut(s0).unwrap();
        surject0.len += len1;
        s1
    }
}

impl<P: Ptr> Default for Model<P> {
    fn default() -> Self {
        Self::new()
    }
}

/// The `Ck` that identifies an element
fn ck(t: &TElement) -> Ck<()> {
    t.key()
}

fn get_mut_rand<'a, P: Ptr>(b: &'a mut Model<P>, rng: &mut StarRng) -> Option<(Ck<()>, &'a mut P)> {
    b.elements.get_mut_rand(rng).map(|(k, e)| (k, &mut e.p))
}

/// Checks the entire element, interlink, and surjection structure of `a`
/// against the model `b`. This is a stronger statement than
/// `_check_invariants`, which can only see that the structure is internally
/// consistent and not whether it is the structure that the operations should
/// have produced.
pub fn check_model<P: Ptr, B: ArenaBacking>(
    a: &SurjectArena<P, TElement, TShared, B>,
    b: &Model<P>,
) -> Result<(), StackedError> {
    ensure_eq!(a.len(), b.len());
    ensure_eq!(a.is_empty(), b.is_empty());
    ensure_eq!(a.len_shared(), b.len_shared());

    // every element is where the model says it is, with the interlinks and the
    // shared value that the model says
    let mut n = 0usize;
    for (p, t) in a.iter() {
        let e = b.elements.get(ck(t)).stack()?;
        ensure_eq!(e.p, p);
        ensure!(a.contains(p));
        let (generation, link) = a.get_inx_link_no_gen(p.inx()).stack()?;
        ensure_eq!(generation, p.generation());
        ensure_eq!(ck(link.t), ck(t));
        ensure_eq!(link.prev(), Some(b.p(e.prev).inx()));
        ensure_eq!(link.next(), Some(b.p(e.next).inx()));
        ensure_eq!(
            a.len_surject(p).stack()?.get(),
            b.surjects.get(e.s).stack()?.len
        );
        ensure_eq!(a.get_shared(p).stack()?.key(), e.s);
        n = n.checked_add(1).stack()?;
    }
    ensure_eq!(n, b.len());

    // every surject is one cyclic chain of exactly the elements that the model
    // says, in the order that the model says
    let mut seen = HashSet::new();
    for (s, surject) in b.surjects.iter() {
        let chain = b.chain(surject.any);
        ensure_eq!(chain.len(), surject.len);
        let p_init = b.p(surject.any);
        let advanced: Vec<Ck<()>> = {
            let mut res = vec![];
            let mut adv = a.advancer_surject(p_init).stack()?;
            while let Some(p) = adv.advance(a) {
                res.push(ck(a.get(p).stack()?));
            }
            res
        };
        ensure_eq!(advanced, chain);
        // `iter_surject` uses the same advancer but also fixes the shared value
        // reference for the whole iteration
        let mut n = 0usize;
        for (p, t, shared) in a.iter_surject(p_init).stack()? {
            ensure_eq!(ck(t), chain[n]);
            ensure_eq!(b.p(chain[n]), p);
            ensure_eq!(shared.key(), s);
            n = n.checked_add(1).stack()?;
        }
        ensure_eq!(n, chain.len());
        for k in chain {
            ensure!(seen.insert(k));
        }
    }
    ensure_eq!(seen.len(), b.len());

    // the shared values are exactly the ones the model has, and `shared_vals`
    // iterates over each of them once
    let mut shared: Vec<Ck<D1>> = a.shared_vals().map(|s| s.key()).collect();
    ensure_eq!(shared.len(), b.len_shared());
    let mut expected: Vec<Ck<D1>> = b.surjects.iter().map(|(s, _)| s).collect();
    shared.sort_unstable_by_key(|k| format!("{k:?}"));
    expected.sort_unstable_by_key(|k| format!("{k:?}"));
    ensure_eq!(shared, expected);

    // `iter_combined` and the `IntoIterator` impl repeat the shared value for
    // every element of a surject
    let mut n = 0usize;
    for (p, t, s) in a.iter_combined() {
        let e = b.elements.get(ck(t)).stack()?;
        ensure_eq!(e.p, p);
        ensure_eq!(s.key(), e.s);
        n = n.checked_add(1).stack()?;
    }
    ensure_eq!(n, b.len());
    ensure_eq!(a.into_iter().count(), b.len());

    Ok(())
}

/// Checks the layout that the canonicalizing operations produce: the element
/// raw indexes are `1..=len`, each surject occupies one contiguous run of them
/// in chain order, and the shared value of the `k`th run is at raw index `k`
fn check_canonical_layout<P: Ptr, B: ArenaBacking>(
    a: &SurjectArena<P, TElement, TShared, B>,
) -> Result<(), StackedError> {
    let ptrs: Vec<P> = a.ptrs().collect();
    ensure_eq!(ptrs.len(), a.len());
    for (i, p) in ptrs.iter().enumerate() {
        ensure_eq!(PtrInx::try_into_usize(p.inx()).stack()?.get(), i + 1);
    }
    // walking the runs in index order has to reach every element exactly once
    let mut i = 0usize;
    let mut k = 0usize;
    while i < ptrs.len() {
        let p_init = ptrs[i];
        let len = a.len_surject(p_init).stack()?.get();
        let mut adv = a.advancer_surject(p_init).stack()?;
        let mut j = 0usize;
        while let Some(p) = adv.advance(a) {
            ensure_eq!(p, *ptrs.get(i + j).stack()?);
            j = j.checked_add(1).stack()?;
        }
        ensure_eq!(j, len);
        // the shared value of the `k`th run is at raw index `k + 1`
        k = k.checked_add(1).stack()?;
        let shared: Vec<Ck<D1>> = a.shared_vals().map(|s| s.key()).collect();
        ensure_eq!(
            *shared.get(k - 1).stack()?,
            a.get_shared(p_init).stack()?.key()
        );
        i = i.checked_add(len).stack()?;
    }
    ensure_eq!(i, ptrs.len());
    ensure_eq!(k, a.len_shared());
    Ok(())
}

/// The [check_canonical_layout] counterpart for the interarena arena, which
/// only needs the index and run structure and not the `Cd` identities
fn check_canonical_layout_1<P: Ptr>(a: &A1<P>) -> Result<(), StackedError> {
    let ptrs: Vec<P> = a.ptrs().collect();
    ensure_eq!(ptrs.len(), a.len());
    for (i, p) in ptrs.iter().enumerate() {
        ensure_eq!(PtrInx::try_into_usize(p.inx()).stack()?.get(), i + 1);
    }
    let mut i = 0usize;
    let mut k = 0usize;
    while i < ptrs.len() {
        let p_init = ptrs[i];
        let len = a.len_surject(p_init).stack()?.get();
        let mut adv = a.advancer_surject(p_init).stack()?;
        let mut j = 0usize;
        while let Some(p) = adv.advance(a) {
            ensure_eq!(p, *ptrs.get(i + j).stack()?);
            j = j.checked_add(1).stack()?;
        }
        ensure_eq!(j, len);
        k = k.checked_add(1).stack()?;
        i = i.checked_add(len).stack()?;
    }
    ensure_eq!(i, ptrs.len());
    ensure_eq!(k, a.len_shared());
    Ok(())
}

/// How an insertion function is reached
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum How {
    WithinCapacity,
    Reallocating,
    Panicking,
    EntryWithinCapacity,
    EntryReallocating,
    /// Creates an entry and then drops it without inserting, which must leave
    /// the arena logically unchanged
    Cancel,
}

/// Returns whether an insertion should be attempted at all. The fallible
/// insertion functions are allowed to be reached in states where they fail,
/// which is most of the point of having them, but the panicking ones are only
/// ever reached where there is already enough capacity.
fn should_insert<P: Ptr, B: ArenaBacking>(
    a: &SurjectArena<P, TElement, TShared, B>,
    how: How,
    new_surject: bool,
    test_limit: usize,
) -> bool {
    if a.len() >= test_limit {
        // keep the fuzz around the target length
        return false;
    }
    if how == How::Panicking {
        if a.capacity() < a.len() + 1 {
            return false;
        }
        if new_surject && a.capacity_shared() < a.len_shared() + 1 {
            return false;
        }
    }
    true
}

#[allow(clippy::too_many_arguments)]
fn try_insert_surject<P: Ptr, B: ArenaBacking>(
    a: &mut SurjectArena<P, TElement, TShared, B>,
    b: &mut Model<P>,
    cd_gen: &mut CdGen<()>,
    cd_gen1: &mut CdGen<D1>,
    how: How,
) -> Result<(), StackedError> {
    let len = a.len();
    let len_shared = a.len_shared();
    match how {
        How::WithinCapacity | How::Reallocating | How::Panicking => {
            let (k, t) = cd_gen.new_cd();
            let (s, shared) = cd_gen1.new_cd();
            let p = match how {
                How::WithinCapacity => match a.insert_surject_within_capacity(t, shared) {
                    Ok(p) => p,
                    Err(_) => {
                        ensure_eq!(a.len(), len);
                        ensure_eq!(a.len_shared(), len_shared);
                        return Ok(());
                    }
                },
                How::Reallocating => match a.insert_surject_reallocating(t, shared) {
                    Ok(p) => p,
                    Err(_) => {
                        ensure_eq!(a.len(), len);
                        ensure_eq!(a.len_shared(), len_shared);
                        return Ok(());
                    }
                },
                How::Panicking => a.insert_surject(t, shared),
                _ => unreachable!(),
            };
            b.insert_surject(k, s, p);
        }
        How::EntryWithinCapacity | How::EntryReallocating | How::Cancel => {
            let p = {
                let entry = match how {
                    How::EntryWithinCapacity => match a.entry_insert_surject_within_capacity() {
                        Ok(entry) => entry,
                        Err(_) => {
                            ensure_eq!(a.len(), len);
                            ensure_eq!(a.len_shared(), len_shared);
                            return Ok(());
                        }
                    },
                    _ => match a.entry_insert_surject_reallocating() {
                        Ok(entry) => entry,
                        Err(_) => {
                            ensure_eq!(a.len(), len);
                            ensure_eq!(a.len_shared(), len_shared);
                            return Ok(());
                        }
                    },
                };
                let p = entry.ptr();
                // REF(insertion_idempotency)
                ensure_eq!(p, entry.ptr());
                if how == How::Cancel {
                    // the entry has no `Drop`, letting it go is the cancellation
                    let _ = entry;
                    ensure_eq!(a.len(), len);
                    ensure_eq!(a.len_shared(), len_shared);
                    return Ok(());
                }
                let (k, t) = cd_gen.new_cd();
                let (s, shared) = cd_gen1.new_cd();
                entry.insert(t, shared);
                b.insert_surject(k, s, p);
                p
            };
            ensure!(a.contains(p));
        }
    }
    ensure_eq!(a.len(), len + 1);
    ensure_eq!(a.len_shared(), len_shared + 1);
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn try_insert<P: Ptr, B: ArenaBacking>(
    a: &mut SurjectArena<P, TElement, TShared, B>,
    b: &mut Model<P>,
    cd_gen: &mut CdGen<()>,
    k_target: Option<Ck<()>>,
    p_target: P,
    how: How,
) -> Result<(), StackedError> {
    let len = a.len();
    let len_shared = a.len_shared();
    let valid = k_target.is_some();
    match how {
        How::WithinCapacity | How::Reallocating | How::Panicking => {
            let (k, t) = cd_gen.new_cd();
            let res = match how {
                How::WithinCapacity => a.insert_within_capacity(p_target, t),
                How::Reallocating => a.insert_reallocating(p_target, t),
                How::Panicking => {
                    if !valid {
                        // the panicking version is only ever given a valid target
                        drop(t);
                        return Ok(());
                    }
                    Ok(a.insert(p_target, t))
                }
                _ => unreachable!(),
            };
            match res {
                Ok(p) => {
                    ensure!(valid);
                    b.insert(k, k_target.stack()?, p);
                }
                Err(ChainInsertionError::FailedLinkRequirement) => {
                    ensure!(!valid);
                    ensure_eq!(a.len(), len);
                    ensure_eq!(a.len_shared(), len_shared);
                    return Ok(());
                }
                Err(_) => {
                    ensure_eq!(a.len(), len);
                    ensure_eq!(a.len_shared(), len_shared);
                    return Ok(());
                }
            }
        }
        How::EntryWithinCapacity | How::EntryReallocating | How::Cancel => {
            let entry = match how {
                How::EntryWithinCapacity => a.entry_insert_within_capacity(p_target),
                _ => a.entry_insert_reallocating(p_target),
            };
            let entry = match entry {
                Ok(entry) => {
                    ensure!(valid);
                    entry
                }
                Err(ChainInsertionError::FailedLinkRequirement) => {
                    ensure!(!valid);
                    ensure_eq!(a.len(), len);
                    ensure_eq!(a.len_shared(), len_shared);
                    return Ok(());
                }
                Err(_) => {
                    ensure_eq!(a.len(), len);
                    ensure_eq!(a.len_shared(), len_shared);
                    return Ok(());
                }
            };
            let p = entry.ptr();
            // REF(insertion_idempotency)
            ensure_eq!(p, entry.ptr());
            if how == How::Cancel {
                // the entry has no `Drop`, letting it go is the cancellation
                let _ = entry;
                ensure_eq!(a.len(), len);
                ensure_eq!(a.len_shared(), len_shared);
                return Ok(());
            }
            let (k, t) = cd_gen.new_cd();
            entry.insert(t);
            b.insert(k, k_target.stack()?, p);
        }
    }
    ensure_eq!(a.len(), len + 1);
    // an element insertion never creates a shared value
    ensure_eq!(a.len_shared(), len_shared);
    Ok(())
}

/// Rebuilds the `p` fields of the model from `a`, which is what the operations
/// that move entries around without being able to report the new `Ptr`s need.
/// The chain and surjection structure in the model is left alone so that
/// `check_model` still verifies it.
fn refresh_model_ptrs<P: Ptr, B: ArenaBacking>(
    a: &SurjectArena<P, TElement, TShared, B>,
    b: &mut Model<P>,
) -> Result<(), StackedError> {
    for (p, t) in a.iter() {
        b.elements.get_mut(ck(t)).stack()?.p = p;
    }
    Ok(())
}

/// Rebuilds the whole model from `a`. This is only used where the structure has
/// already been checked against what it was before the operation.
fn rebuild_model<P: Ptr, B: ArenaBacking>(
    a: &SurjectArena<P, TElement, TShared, B>,
    b: &mut Model<P>,
) -> Result<(), StackedError> {
    let mut by_inx = HashMap::new();
    for (p, t) in a.iter() {
        by_inx.insert(p.inx(), ck(t));
    }
    b.clear();
    for (p, t) in a.iter() {
        let (_, link) = a.get_inx_link_no_gen(p.inx()).stack()?;
        b.elements.insert(ck(t), TElem {
            p,
            s: a.get_shared(p).stack()?.key(),
            prev: *by_inx.get(&link.prev().stack()?).stack()?,
            next: *by_inx.get(&link.next().stack()?).stack()?,
        });
    }
    let mut seen = HashSet::new();
    for (p, t) in a.iter() {
        let s = a.get_shared(p).stack()?.key();
        if seen.insert(s) {
            b.surjects.insert(s, TSurject {
                any: ck(t),
                len: a.len_surject(p).stack()?.get(),
            });
        }
    }
    Ok(())
}

/// The `Ck`s of every element of `a`, in index order
fn keys<P: Ptr, B: ArenaBacking>(a: &SurjectArena<P, TElement, TShared, B>) -> Vec<Ck<()>> {
    a.iter().map(|(_, t)| ck(t)).collect()
}

pub fn fuzz<P: Ptr, B: ArenaBacking>(
    meta: &mut Meta<Stats>,
    a: &mut SurjectArena<P, TElement, TShared, B>,
    mut check_invariants: impl FnMut(&SurjectArena<P, TElement, TShared, B>) -> Result<(), StackedError>,
    // set iff `SetMaxCapacity` is implemented
    set_max_capacity: Option<
        fn(
            &mut SurjectArena<P, TElement, TShared, B>,
            usize,
        ) -> Result<(), MaxCapacityReductionError>,
    >,
) -> Result<(), StackedError> {
    let rng = &mut meta.rng;
    let stats = meta.stats.as_mut().stack()?;
    let test_limit = stats.test_limit;
    let n = stats.n;
    let mut fixed_cap = stats.fixed_cap;
    let cd_gen = &mut stats.cd_gen;
    let cd_gen1 = &mut stats.cd_gen1;
    let cd_gen2 = &mut stats.cd_gen2;
    let cd_gen3 = &mut stats.cd_gen3;

    let mut b = Model::<P>::new();
    let mut b_capacity = a.capacity();
    let mut g = TestGen::<P>(a.generation());

    // set and used by the interarena sections
    let mut a1 = A1::<P>::new();
    let mut recaster = DirectArena::<P, P, StackBacking<{ 4 * LIMIT }>>::new();
    let mut chain_arena = ChainArena::<P, Cd<D2>, StackBacking<{ 4 * LIMIT }>>::new();
    let mut arena = Arena::<P, Cd<D2>, StackBacking<{ 4 * LIMIT }>>::new();

    // counts the rare reconstruction op, which makes sure there is not some
    // problem with the test harness itself or determinism
    let mut iters999 = 0;
    let mut max_len = 0usize;
    let mut max_len_surject = 0usize;

    for i in 0..n {
        let len = b.len();
        max_len = max(max_len, len);
        for (_, surject) in b.surjects.iter() {
            max_len_surject = max(max_len_surject, surject.len);
        }
        ensure_eq!(cd_gen.len(), len);
        ensure_eq!(cd_gen1.len(), b.len_shared());
        ensure_eq!(a.len(), len);
        ensure_eq!(a.is_empty(), b.is_empty());
        ensure_eq!(a.capacity(), b_capacity);
        ensure!(len <= a.capacity());
        ensure!(a.len_shared() <= a.capacity_shared());
        ensure!(a.len_shared() <= a.len());
        // nothing the fuzz does is allowed to leave the two max capacities
        // disagreeing, because `reallocate_min_capacity` acts on both of them but
        // only reports the element limit through `max_capacity`
        ensure_eq!(a.max_capacity(), a.max_capacity_shared());
        if let Some(fixed_cap) = fixed_cap {
            ensure_eq!(a.capacity(), fixed_cap);
        }
        if let Some(max_capacity) = a.max_capacity() {
            ensure!(a.capacity() <= max_capacity);
        }
        if let Some(max_capacity) = a.max_capacity_shared() {
            ensure!(a.capacity_shared() <= max_capacity);
        }
        ensure_eq!(a.singular_generation().stack()?, g.0);
        ensure_eq!(a.generation(), g.0);
        check_invariants(a).stack()?;
        check_model(a, &b).stack()?;

        meta.i = i;
        meta.op_inx = rng.index_inclusive(1023);
        match meta.op_inx {
            0..250 => {
                common_compact_fuzz_step250(
                    rng,
                    a,
                    test_limit,
                    meta.op_inx,
                    &mut b,
                    &mut b_capacity,
                    Some(&mut g),
                    // handled separately because the generic predicate cannot see
                    // the shared value side
                    None,
                    get_mut_rand,
                    ck,
                )
                .stack()?;
            }
            250..380 => {
                // all of the surject insertion functions
                let how = match rng.index_inclusive(5) {
                    0 => How::WithinCapacity,
                    1 => How::Reallocating,
                    2 => How::Panicking,
                    3 => How::EntryWithinCapacity,
                    4 => How::EntryReallocating,
                    5 => How::Cancel,
                    _ => unreachable!(),
                };
                if should_insert(a, how, true, test_limit) {
                    try_insert_surject(a, &mut b, cd_gen, cd_gen1, how).stack()?;
                }
                b_capacity = a.capacity();
            }
            380..560 => {
                // all of the element insertion functions
                let how = match rng.index_inclusive(5) {
                    0 => How::WithinCapacity,
                    1 => How::Reallocating,
                    2 => How::Panicking,
                    3 => How::EntryWithinCapacity,
                    4 => How::EntryReallocating,
                    5 => How::Cancel,
                    _ => unreachable!(),
                };
                let (k_target, p_target) = if rng.index_inclusive(15) == 0 {
                    (None, gen_invalid(rng, a))
                } else if let Some((k, e)) = b.elements.get_rand(rng) {
                    (Some(k), e.p)
                } else {
                    (None, gen_invalid(rng, a))
                };
                if should_insert(a, how, false, test_limit) {
                    try_insert(a, &mut b, cd_gen, k_target, p_target, how).stack()?;
                }
                b_capacity = a.capacity();
            }
            560..700 => {
                // `remove_element`, `remove_element_inx`, `ArenaTrait::remove`, and
                // `ArenaTrait::remove_inx`
                let Some((k, e)) = b.elements.get_rand(rng) else {
                    let p = gen_invalid(rng, a);
                    ensure!(matches!(
                        a.remove_element(p),
                        InvalidationResult::InvalidPtr
                    ));
                    ensure!(matches!(a.remove(p), InvalidationResult::InvalidPtr));
                    ensure!(matches!(
                        a.remove_element_inx(p.inx()),
                        InvalidationResult::InvalidPtr
                    ));
                    ensure!(matches!(
                        a.remove_inx(p.inx()),
                        InvalidationResult::InvalidPtr
                    ));
                    continue;
                };
                let p = e.p;
                let expected_last = b.surjects.get(e.s).stack()?.len == 1;
                match rng.index_inclusive(3) {
                    0 => {
                        let (res, o) = a.remove_element(p).overflowing();
                        let (t, shared) = res.stack()?;
                        ensure_eq!(ck(&t), k);
                        ensure_eq!(shared.is_some(), expected_last);
                        if let Some(shared) = shared {
                            ensure_eq!(shared.key(), e.s);
                        }
                        ensure_eq!(o, g.invalidate());
                    }
                    1 => {
                        let (res, o) = a.remove_element_inx(p.inx()).overflowing();
                        let (generation, t, shared) = res.stack()?;
                        ensure_eq!(generation, p.generation());
                        ensure_eq!(ck(&t), k);
                        ensure_eq!(shared.is_some(), expected_last);
                        ensure_eq!(o, g.invalidate());
                    }
                    2 => {
                        let (res, o) = a.remove(p).overflowing();
                        let t = res.stack()?;
                        ensure_eq!(ck(&t), k);
                        ensure_eq!(o, g.invalidate());
                    }
                    3 => {
                        let (res, o) = a.remove_inx(p.inx()).overflowing();
                        let (generation, t) = res.stack()?;
                        ensure_eq!(generation, p.generation());
                        ensure_eq!(ck(&t), k);
                        ensure_eq!(o, g.invalidate());
                    }
                    _ => unreachable!(),
                }
                let removed_shared = b.remove(k);
                ensure_eq!(removed_shared.is_some(), expected_last);
                ensure!(!a.contains(p));
            }
            700..760 => {
                // `union`
                let (Some((k0, e0)), Some((k1, e1))) =
                    (b.elements.get_rand(rng), b.elements.get_rand(rng))
                else {
                    let p = gen_invalid(rng, a);
                    ensure!(a.union(p, p).is_none());
                    continue;
                };
                let (p0, p1) = (e0.p, e1.p);
                let (s0, s1) = (e0.s, e1.s);
                if rng.index_inclusive(15) == 0 {
                    // one side invalid
                    let invalid = gen_invalid(rng, a);
                    ensure!(a.union(invalid, p1).is_none());
                    ensure!(a.union(p0, invalid).is_none());
                    continue;
                }
                if s0 == s1 {
                    ensure!(a.union(p0, p1).is_none());
                    continue;
                }
                let len0 = b.surjects.get(s0).stack()?.len;
                let len1 = b.surjects.get(s1).stack()?.len;
                // the smaller surject is the one that loses its shared value
                let (k_keep, s_lose) = if len0 < len1 { (k1, s0) } else { (k0, s1) };
                let k_lose = if len0 < len1 { k0 } else { k1 };
                let (shared, p_keep) = a.union(p0, p1).stack()?;
                ensure_eq!(shared.key(), s_lose);
                ensure_eq!(p_keep, b.p(k_keep));
                let s_removed = b.union(k_keep, k_lose);
                ensure_eq!(s_removed, s_lose);
                ensure_eq!(a.len_surject(p_keep).stack()?.get(), len0 + len1);
            }
            760..815 => {
                // the shared value accessors, `in_same_surject`, and `Index`
                if let Some((k0, e0)) = b.elements.get_rand(rng) {
                    let p0 = e0.p;
                    ensure_eq!(a.get_shared(p0).stack()?.key(), e0.s);
                    ensure_eq!(a.get_shared_mut(p0).stack()?.key(), e0.s);
                    ensure_eq!(ck(&a[p0]), k0);
                    ensure_eq!(ck(&a[&p0]), k0);
                    ensure_eq!(ck(&a[p0]), ck(&a[p0]));
                    {
                        let t: &mut TElement = &mut a[p0];
                        ensure_eq!(ck(t), k0);
                    }
                    if let Some((_, e1)) = b.elements.get_rand(rng) {
                        let p1 = e1.p;
                        ensure_eq!(a.in_same_surject(p0, p1).stack()?, e0.s == e1.s);
                        match a.get_disjoint_shared_mut([p0, p1]) {
                            Ok([s0, s1]) => {
                                ensure!(e0.s != e1.s);
                                ensure_eq!(s0.key(), e0.s);
                                ensure_eq!(s1.key(), e1.s);
                            }
                            Err(_) => ensure!(e0.s == e1.s),
                        }
                    }
                    let invalid = gen_invalid(rng, a);
                    ensure!(a.get_shared(invalid).is_none());
                    ensure!(a.get_shared_mut(invalid).is_none());
                    ensure!(a.in_same_surject(p0, invalid).is_none());
                    ensure!(a.in_same_surject(invalid, p0).is_none());
                    ensure!(a.get_disjoint_shared_mut([p0, invalid]).is_err());
                    ensure!(a.len_surject(invalid).is_none());
                    // this one ignores the generation, so it only agrees with
                    // `get_inx` about the index
                    ensure_eq!(
                        a.get_inx_link_no_gen(invalid.inx()).is_none(),
                        a.get_inx(invalid.inx()).is_none()
                    );
                    ensure!(a.advancer_surject(invalid).is_none());
                    ensure!(a.iter_surject(invalid).is_none());
                    ensure!(a.drain_surject(invalid).is_none());
                } else {
                    let invalid = gen_invalid(rng, a);
                    ensure!(a.get_shared(invalid).is_none());
                    ensure!(a.get_shared_mut(invalid).is_none());
                    ensure!(a.len_surject(invalid).is_none());
                    let [] = a.get_disjoint_shared_mut([]).stack()?;
                }
                // `shared_vals_mut` reaches each shared value once
                let mut count = 0usize;
                for _ in a.shared_vals_mut() {
                    count = count.checked_add(1).stack()?;
                }
                ensure_eq!(count, b.len_shared());
            }
            815..830 => {
                // the capacity operations that are specific to having two internal
                // arenas
                match rng.index_inclusive(2) {
                    0 => {
                        if let Some(set_max_capacity) = set_max_capacity {
                            let next = rng.index_inclusive(4 * test_limit);
                            match set_max_capacity(a, next) {
                                Ok(()) => {
                                    ensure_eq!(a.max_capacity(), Some(next));
                                    ensure_eq!(a.max_capacity_shared(), Some(next));
                                }
                                Err(MaxCapacityReductionError) => {
                                    // the two limits are always left in agreement
                                    ensure_eq!(a.max_capacity(), a.max_capacity_shared());
                                    ensure!(a.max_capacity().stack()? > next);
                                }
                            }
                            ensure!(a.len() <= a.capacity());
                            ensure!(a.len_shared() <= a.capacity_shared());
                        }
                    }
                    1 => {
                        let next = rng.index_inclusive(test_limit);
                        if a.reallocate_min_capacity_elements(next).is_ok() {
                            ensure!(a.capacity() >= next);
                        }
                    }
                    2 => {
                        let next = rng.index_inclusive(test_limit);
                        if a.reallocate_min_capacity_shared(next).is_ok() {
                            ensure!(a.capacity_shared() >= next);
                        }
                    }
                    _ => unreachable!(),
                }
                b_capacity = a.capacity();
            }
            830..880 => {
                // `remove_shared` and `drain_surject`
                let Some((k, e)) = b.elements.get_rand(rng) else {
                    let p = gen_invalid(rng, a);
                    ensure!(matches!(a.remove_shared(p), InvalidationResult::InvalidPtr));
                    continue;
                };
                let p = e.p;
                let chain = b.chain(b.surjects.get(e.s).stack()?.any);
                if rng.next_bool() {
                    let (res, o) = a.remove_shared(p).overflowing();
                    let shared = res.stack()?;
                    ensure_eq!(shared.key(), e.s);
                    ensure_eq!(o, g.invalidate());
                    b.remove_surject(k);
                } else {
                    // drain part of the surject and let the drop finish the rest
                    let chain_from_k = b.chain(k);
                    let take = rng.index_inclusive(chain_from_k.len());
                    let mut drain = a.drain_surject(p).stack()?;
                    for (j, k_expected) in chain_from_k.iter().enumerate().take(take) {
                        let (p1, t, shared) = drain.next().stack()?.allow();
                        ensure_eq!(ck(&t), *k_expected);
                        ensure_eq!(p1, b.p(*k_expected));
                        ensure_eq!(shared.is_some(), j + 1 == chain_from_k.len());
                    }
                    drop(drain);
                    // every removal of the surject invalidates
                    for _ in 0..chain.len() {
                        g.invalidate();
                    }
                    b.remove_surject(k);
                }
                ensure!(!a.contains(p));
            }
            880..900 => {
                // `drain_combined`, `ArenaTrait::drain`, and `clear`
                match rng.index_inclusive(2) {
                    0 => {
                        let mut count = 0usize;
                        let mut shared_count = 0usize;
                        for o in a.drain_combined() {
                            let ((_, _, shared), _) = o.overflowing();
                            if shared.is_some() {
                                shared_count = shared_count.checked_add(1).stack()?;
                            }
                            count = count.checked_add(1).stack()?;
                        }
                        ensure_eq!(count, len);
                        ensure_eq!(shared_count, b.len_shared());
                    }
                    1 => {
                        // partial drain, the drop clears the rest
                        let take = rng.index_inclusive(len);
                        let mut drain = a.drain();
                        let mut count = 0usize;
                        for _ in 0..take {
                            if drain.next().is_none() {
                                break;
                            }
                            count = count.checked_add(1).stack()?;
                        }
                        drop(drain);
                        ensure!(count <= len);
                    }
                    2 => {
                        a.clear().allow();
                    }
                    _ => unreachable!(),
                }
                // the removals and the clear all invalidate
                if len > 0 {
                    g.0 = a.generation();
                }
                ensure!(a.is_empty());
                ensure_eq!(a.len_shared(), 0);
                b.clear();
                b_capacity = a.capacity();
            }
            900..960 => {
                // `compress`, `compress_with`, and `compress_canonical`
                let old_keys = keys(a);
                let reset_generation = rng.next_bool();
                match rng.index_inclusive(2) {
                    0 => {
                        a.compress(reset_generation).allow();
                        refresh_model_ptrs(a, &mut b).stack()?;
                    }
                    1 => {
                        let mut mapped = vec![];
                        a.compress_with(reset_generation, |p, t, q| {
                            mapped.push((p, ck(t), q));
                        })
                        .allow();
                        refresh_model_ptrs(a, &mut b).stack()?;
                        for (_, k, q) in mapped {
                            ensure_eq!(b.p(k), q);
                        }
                    }
                    2 => {
                        a.compress_canonical(reset_generation).allow();
                        rebuild_model(a, &mut b).stack()?;
                        check_canonical_layout(a).stack()?;
                    }
                    _ => unreachable!(),
                }
                if reset_generation {
                    g.0 = PtrGen::two();
                } else if len > 0 {
                    g.invalidate();
                }
                ensure_eq!(a.generation(), g.0);
                // the compressing operations keep every element, and only the
                // canonical one is allowed to reorder them
                let new_keys = keys(a);
                ensure_eq!(new_keys.len(), old_keys.len());
                b_capacity = a.capacity();
            }
            960..1000 => {
                // `transfer_canonical_reallocating` round trip through `a1`, with the
                // recaster pattern from its documentation on the way out
                let old_keys = keys(a);
                let old: Vec<(Ck<()>, P)> = b.elements.iter().map(|(k, e)| (k, e.p)).collect();
                // this is what makes the recaster a mapping keyed by every `Ptr` of
                // the pre-transfer `a`, and it also exercises the
                // `CompactArenaTrait` impl of `SurjectArena` as a clone source
                if recaster.clone_from_with(&*a, |_, _| P::invalid()).is_err() {
                    continue;
                }
                let next_gen = PtrGen::generational_inc(g.0).0;
                let mut fwd = HashMap::new();
                let mut shared_lens = vec![];
                if a1
                    .transfer_canonical_reallocating(
                        next_gen,
                        a,
                        |q, o, p| {
                            recaster[q] = p;
                            let (t, _) = o.overflowing();
                            fwd.insert(ck(&t), p);
                            cd_gen2.new_cd().1
                        },
                        |_| {
                            shared_lens.push(());
                            cd_gen3.new_cd().1
                        },
                    )
                    .is_err()
                {
                    continue;
                }
                ensure!(a.is_empty());
                ensure_eq!(a1.len(), old_keys.len());
                ensure_eq!(fwd.len(), old_keys.len());
                ensure_eq!(shared_lens.len(), b.len_shared());
                check_canonical_layout_1(&a1).stack()?;
                // every old `Ptr` recasts onto the element that it was pointing at
                for (k, p_old) in &old {
                    let mut p = *p_old;
                    ensure!(p.recast(&recaster).is_ok());
                    ensure_eq!(p, *fwd.get(k).stack()?);
                    ensure!(a1.contains(p));
                }

                let next_gen1 = PtrGen::generational_inc(next_gen).0;
                let mut back = 0usize;
                a.transfer_canonical_reallocating(
                    next_gen1,
                    &mut a1,
                    |_, _, _| {
                        back += 1;
                        cd_gen.new_cd().1
                    },
                    |_| cd_gen1.new_cd().1,
                )
                .stack()?;
                ensure!(a1.is_empty());
                ensure_eq!(back, old_keys.len());
                g.0 = next_gen1;
                ensure_eq!(a.generation(), g.0);
                // the model is rebuilt because the round trip made brand new `Cd`s
                rebuild_model(a, &mut b).stack()?;
                check_canonical_layout(a).stack()?;
                b_capacity = a.capacity();
            }
            1000..1015 => {
                // `clone_from_with`, `clone_to_chain_arena`, and `clone_to_arena`
                match rng.index_inclusive(2) {
                    0 => {
                        // a full round trip through `a1`, which preserves every `Ptr`
                        // and the whole surjection
                        let mut lens = vec![];
                        if a1
                            .clone_from_with(
                                &*a,
                                |_, _| cd_gen2.new_cd().1,
                                |element_count, _| {
                                    lens.push(element_count.get());
                                    cd_gen3.new_cd().1
                                },
                            )
                            .is_err()
                        {
                            continue;
                        }
                        ensure_eq!(a1.len(), len);
                        ensure_eq!(a1.len_shared(), b.len_shared());
                        ensure_eq!(lens.len(), b.len_shared());
                        ensure_eq!(lens.iter().sum::<usize>(), len);
                        for (_, e) in b.elements.iter() {
                            ensure!(a1.contains(e.p));
                        }
                        // and back, which replaces every `Cd` with a fresh one
                        a.clone_from_with(&a1, |_, _| cd_gen.new_cd().1, |_, _| cd_gen1.new_cd().1)
                            .stack()?;
                        ensure_eq!(a.len(), len);
                        rebuild_model(a, &mut b).stack()?;
                        a1.clear().allow();
                        b_capacity = a.capacity();
                    }
                    1 => {
                        if chain_arena.clone_to_chain_arena_helper(a, cd_gen2).is_err() {
                            continue;
                        }
                        ensure_eq!(chain_arena.len(), len);
                        // each surject arrives as one cyclic chain
                        for (_, e) in b.elements.iter() {
                            ensure!(chain_arena.contains(e.p));
                            let link = chain_arena.get_link(e.p).stack()?;
                            ensure_eq!(link.prev().stack()?, b.p(e.prev));
                            ensure_eq!(link.next().stack()?, b.p(e.next));
                        }
                        chain_arena.clear().allow();
                    }
                    2 => {
                        if a.clone_to_arena(&mut arena, |_, _| cd_gen2.new_cd().1)
                            .is_err()
                        {
                            continue;
                        }
                        ensure_eq!(arena.len(), len);
                        for (_, e) in b.elements.iter() {
                            ensure!(arena.contains(e.p));
                        }
                        arena.clear().allow();
                    }
                    _ => unreachable!(),
                }
            }
            1015..1024 => {
                // reconstruct the arena from scratch, which also covers the
                // separated and unified minimum capacity constructors
                // the same request is used for both halves, because the backings
                // with a max capacity set it from the request and the rest of the
                // fuzz relies on the two max capacities agreeing. The asymmetric
                // case is covered by `surject_separated_capacity` instead.
                let min_capacity = rng.index_inclusive(test_limit);
                if rng.next_bool() {
                    *a = SurjectArena::with_min_capacity_separated(min_capacity, min_capacity)
                        .stack()?;
                } else {
                    *a = SurjectArena::with_min_capacity(min_capacity).stack()?;
                }
                ensure!(a.capacity() >= min_capacity);
                ensure!(a.capacity_shared() >= min_capacity);
                ensure!(a.is_empty());
                ensure_eq!(a.len_shared(), 0);
                if fixed_cap.is_some() {
                    fixed_cap = Some(a.capacity());
                }
                g.0 = a.singular_generation().stack()?;
                b_capacity = a.capacity();
                b.clear();
                iters999 += 1;
            }
            1024.. => unreachable!(),
        }
    }

    let stats = meta.stats.as_mut().stack()?;
    if let Some(expect) = &stats.iters999 {
        expect.assert_debug_eq(&iters999);
    }
    if let Some(expect) = &stats.max_len {
        expect.assert_debug_eq(&max_len);
    }
    if let Some(expect) = &stats.max_len_surject {
        expect.assert_debug_eq(&max_len_surject);
    }

    // clean up so that the `CdGen`s can be dropped
    a.clear().allow();
    a1.clear().allow();
    chain_arena.clear().allow();
    arena.clear().allow();
    recaster.clear().allow();
    b.clear();
    Ok(())
}

/// Helper trait so that the `clone_to_chain_arena` call site stays readable
trait CloneToChainArenaHelper<P: Ptr> {
    fn clone_to_chain_arena_helper<B: ArenaBacking>(
        &mut self,
        a: &SurjectArena<P, TElement, TShared, B>,
        cd_gen2: &mut CdGen<D2>,
    ) -> Result<(), ReallocationError>;
}

impl<P: Ptr, B1: ArenaBacking> CloneToChainArenaHelper<P> for ChainArena<P, Cd<D2>, B1> {
    fn clone_to_chain_arena_helper<B: ArenaBacking>(
        &mut self,
        a: &SurjectArena<P, TElement, TShared, B>,
        cd_gen2: &mut CdGen<D2>,
    ) -> Result<(), ReallocationError> {
        a.clone_to_chain_arena(self, |_, _| cd_gen2.new_cd().1)
    }
}
