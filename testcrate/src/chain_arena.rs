use std::{cmp::max, collections::HashMap};

use stacked_errors::{StackableErr, StackedError, bail, ensure, ensure_eq};
use star_rng::StarRng;
use triple_arena::{
    ChainArena, DirectArena, InvalidationOption, InvalidationResult, LinkInsertKind, LinkNoGen,
    StackBacking,
    errors::{AllocError, ChainInsertionError, MaxCapacityReductionError, ReallocationError},
    traits::{
        Advancer, ArenaInsertEntryTrait, ArenaTrait, ChainArenaTrait, CompactArenaTrait,
        DisjointableArenaTrait, Ptr,
    },
    utils::traits::{ArenaBacking, NonZeroInxGenericStack, PtrGen, PtrInx},
};

// similar enough that we can reuse them
pub use crate::basic_arena::{MultiStats, Stats};
use crate::{
    TestGen,
    basic_arena::{common_compact_fuzz_step250, gen_invalid},
    cdgen::{Cd, CdGen, Ck, CkMap},
    misc::{D1, Meta},
};

/// The reference model of one link. The interlinks are recorded as the `Ck`s of
/// the neighbors rather than as `Ptr`s, so that operations which change `Ptr`s
/// do not need to change the reference interlinks
pub struct TLink<P> {
    pub p: P,
    pub prev: Option<Ck<()>>,
    pub next: Option<Ck<()>>,
}

type Model<P> = CkMap<(), TLink<P>>;

fn m_p<P: Ptr>(b: &Model<P>, k: Ck<()>) -> P {
    b.get(k).unwrap().p
}

fn m_prev<P: Ptr>(b: &Model<P>, k: Ck<()>) -> Option<Ck<()>> {
    b.get(k).unwrap().prev
}

fn m_next<P: Ptr>(b: &Model<P>, k: Ck<()>) -> Option<Ck<()>> {
    b.get(k).unwrap().next
}

fn m_set_prev<P: Ptr>(b: &mut Model<P>, k: Ck<()>, prev: Option<Ck<()>>) {
    b.get_mut(k).unwrap().prev = prev;
}

fn m_set_next<P: Ptr>(b: &mut Model<P>, k: Ck<()>, next: Option<Ck<()>>) {
    b.get_mut(k).unwrap().next = next;
}

/// The model side of the `remove*` functions, splicing the neighbors of the
/// already removed `k` together
fn m_splice<P: Ptr>(b: &mut Model<P>, k: Ck<()>, removed: &TLink<P>) {
    if removed.prev == Some(k) {
        // single link cyclic chain, there is nothing left to splice
        return;
    }
    if let Some(prev) = removed.prev {
        m_set_next(b, prev, removed.next);
    }
    if let Some(next) = removed.next {
        m_set_prev(b, next, removed.prev);
    }
}

/// The chain that `k_init` is a part of, in the order that `advancer_chain` and
/// `drain_chain` should produce
fn m_chain<P: Ptr>(b: &Model<P>, k_init: Ck<()>) -> Vec<Ck<()>> {
    let mut res = vec![k_init];
    let mut cur = m_next(b, k_init);
    while let Some(k) = cur {
        if k == k_init {
            // cyclic, and the whole chain has been seen
            return res;
        }
        res.push(k);
        cur = m_next(b, k);
    }
    // ran off the end, resume from the previous link to `k_init`
    let mut cur = m_prev(b, k_init);
    while let Some(k) = cur {
        res.push(k);
        cur = m_prev(b, k);
    }
    res
}

/// Checks that the whole interlink structure of `a` matches the model `b`. This
/// is a stronger statement than `_check_invariants`, which can only see that
/// the interlinks are transitive and not whether they are the ones that the
/// operations should have produced.
pub fn check_model<P: Ptr, A: ChainArenaTrait<P, Cd<()>>>(
    a: &A,
    b: &Model<P>,
) -> Result<(), StackedError> {
    let mut n = 0usize;
    for (p, link) in a.iter_link_no_gen() {
        let t = b.get(link.t.key()).stack()?;
        ensure_eq!(t.p, p);
        let expected_prev = match t.prev {
            Some(k) => Some(b.get(k).stack()?.p.inx()),
            None => None,
        };
        let expected_next = match t.next {
            Some(k) => Some(b.get(k).stack()?.p.inx()),
            None => None,
        };
        ensure_eq!(link.prev(), expected_prev);
        ensure_eq!(link.next(), expected_next);
        // `get_link` has to chase down the generations of the neighbors
        let full = a.get_link(p).stack()?;
        ensure_eq!(full.prev().map(|q| q.inx()), expected_prev);
        ensure_eq!(full.next().map(|q| q.inx()), expected_next);
        for q in [full.prev(), full.next()].into_iter().flatten() {
            ensure!(a.contains(q));
        }
        ensure_eq!(full.t.key(), link.t.key());
        // and this is the generationless lookup
        let (generation, link1) = a.get_inx_link_no_gen(p.inx()).stack()?;
        ensure_eq!(generation, p.generation());
        ensure_eq!(link1.prev_next(), link.prev_next());
        n = n.checked_add(1).stack()?;
    }
    ensure_eq!(n, b.len());
    Ok(())
}

/// Checks the layout that the canonicalizing operations produce: the raw
/// indexes are `1..=len`, and each chain occupies one contiguous run of them in
/// `Link::next` order
fn check_canonical_layout<P: Ptr, A: ChainArenaTrait<P, Cd<()>>>(
    a: &A,
) -> Result<(), StackedError> {
    let ptrs: Vec<P> = a.ptrs().collect();
    ensure_eq!(ptrs.len(), a.len());
    for (i, p) in ptrs.iter().enumerate() {
        ensure_eq!(
            PtrInx::try_into_usize(p.inx()).stack()?.get(),
            i.checked_add(1).stack()?
        );
    }
    let mut i = 0usize;
    while i < ptrs.len() {
        // find where the run of this chain ends, following only the `next`
        // interlinks so that a chain that is not contiguous fails here
        let chain_start = i;
        loop {
            let link = a.get_link_no_gen(ptrs[i]).stack()?;
            match link.next() {
                // the end of an acyclic chain
                None => break,
                // the end of a cyclic chain, which wraps to the start of the run
                Some(next) if next == ptrs[chain_start].inx() => break,
                Some(next) => {
                    ensure_eq!(next, ptrs.get(i.checked_add(1).stack()?).stack()?.inx());
                    i = i.checked_add(1).stack()?;
                }
            }
        }
        let chain_end = i;
        let cyclic = a.get_link_no_gen(ptrs[chain_end]).stack()?.next().is_some();
        // the `prev` interlinks have to mirror the `next` ones
        for j in chain_start..=chain_end {
            let expected = if j > chain_start {
                Some(ptrs[j - 1].inx())
            } else if cyclic {
                Some(ptrs[chain_end].inx())
            } else {
                None
            };
            ensure_eq!(a.get_link_no_gen(ptrs[j]).stack()?.prev(), expected);
        }
        i = i.checked_add(1).stack()?;
    }
    Ok(())
}

/// What the model says a [LinkInsertKind] should do
enum Expect {
    /// The requirements of the kind are not met
    Fail,
    /// The new link is its own single link cyclic chain
    SingleLinkCyclic,
    /// The `(prev, next)` that the new link ends up with, and which the model
    /// also has to write the other side of
    Normal(Option<Ck<()>>, Option<Ck<()>>),
}

/// The `Ck` of the link at `p`, which is also how the model is looked up from a
/// `Ptr`
fn key_of<P: Ptr, A: ChainArenaTrait<P, Cd<()>>>(a: &A, p: P) -> Option<Ck<()>> {
    a.get(p).map(|t| t.key())
}

fn key_of_inx<P: Ptr, A: ChainArenaTrait<P, Cd<()>>>(a: &A, inx: P::Inx) -> Option<Ck<()>> {
    a.get_inx(inx).map(|(_, t)| t.key())
}

/// Works out what `kind` should do purely from the model. Note that the "*Inx"
/// variants only differ in that they resolve the link without a generation
/// check.
fn expect_kind<P: Ptr, A: ChainArenaTrait<P, Cd<()>>>(
    a: &A,
    b: &Model<P>,
    kind: LinkInsertKind<P>,
) -> Expect {
    let by_gen = |p: P| key_of(a, p);
    let inx = |inx: P::Inx| key_of_inx(a, inx);
    let start = |k: Option<Ck<()>>| match k {
        Some(k) if m_prev(b, k).is_none() => Expect::Normal(None, Some(k)),
        _ => Expect::Fail,
    };
    let end = |k: Option<Ck<()>>| match k {
        Some(k) if m_next(b, k).is_none() => Expect::Normal(Some(k), None),
        _ => Expect::Fail,
    };
    let prev_to = |k: Option<Ck<()>>| match k {
        Some(k) => Expect::Normal(m_prev(b, k), Some(k)),
        None => Expect::Fail,
    };
    let next_to = |k: Option<Ck<()>>| match k {
        Some(k) => Expect::Normal(Some(k), m_next(b, k)),
        None => Expect::Fail,
    };
    let at_interlink = |k0: Option<Ck<()>>, k1: Option<Ck<()>>| match (k0, k1) {
        (Some(k0), Some(k1)) if m_next(b, k0) == Some(k1) => Expect::Normal(Some(k0), Some(k1)),
        _ => Expect::Fail,
    };
    let bridge = |k0: Option<Ck<()>>, k1: Option<Ck<()>>| match (k0, k1) {
        (Some(k0), Some(k1)) if m_next(b, k0).is_none() && m_prev(b, k1).is_none() => {
            Expect::Normal(Some(k0), Some(k1))
        }
        _ => Expect::Fail,
    };
    match kind {
        LinkInsertKind::Disconnected => Expect::Normal(None, None),
        LinkInsertKind::SingleLinkCyclic => Expect::SingleLinkCyclic,
        LinkInsertKind::ChainStart(p) => start(by_gen(p)),
        LinkInsertKind::ChainStartInx(i) => start(inx(i)),
        LinkInsertKind::ChainEnd(p) => end(by_gen(p)),
        LinkInsertKind::ChainEndInx(i) => end(inx(i)),
        LinkInsertKind::PrevTo(p) => prev_to(by_gen(p)),
        LinkInsertKind::PrevToInx(i) => prev_to(inx(i)),
        LinkInsertKind::NextTo(p) => next_to(by_gen(p)),
        LinkInsertKind::NextToInx(i) => next_to(inx(i)),
        LinkInsertKind::AtInterlink { next_to, prev_to } => {
            at_interlink(by_gen(next_to), by_gen(prev_to))
        }
        LinkInsertKind::AtInterlinkInx { next_to, prev_to } => {
            at_interlink(inx(next_to), inx(prev_to))
        }
        LinkInsertKind::Bridge { end, start } => bridge(by_gen(end), by_gen(start)),
        LinkInsertKind::BridgeInx { end, start } => bridge(inx(end), inx(start)),
    }
}

/// Applies to the model what a successful insertion of `k` at `p` did
fn m_insert<P: Ptr>(b: &mut Model<P>, k: Ck<()>, p: P, expect: &Expect) {
    let (prev, next) = match expect {
        Expect::Fail => unreachable!(),
        Expect::SingleLinkCyclic => (Some(k), Some(k)),
        Expect::Normal(prev, next) => (*prev, *next),
    };
    b.insert(k, TLink { p, prev, next });
    // the other side of each interlink, note that this handles the cases where a
    // neighbor is the new link itself
    if let Some(prev) = prev {
        m_set_next(b, prev, Some(k));
    }
    if let Some(next) = next {
        m_set_prev(b, next, Some(k));
    }
}

/// Picks a random `LinkInsertKind`, biased towards ones that will succeed but
/// regularly producing unmet requirements and invalid `Ptr`s as well
fn rand_kind<P: Ptr, A: CompactArenaTrait<P, Cd<()>> + ChainArenaTrait<P, Cd<()>>>(
    rng: &mut StarRng,
    a: &A,
    b: &Model<P>,
) -> LinkInsertKind<P> {
    // a random existing link, or an invalid `Ptr` some of the time so that the
    // `Ptr` taking variants get to reject and the "*Inx" variants get to act on
    // whatever index happens to be there
    fn rand_p<P: Ptr, A: CompactArenaTrait<P, Cd<()>> + ChainArenaTrait<P, Cd<()>>>(
        rng: &mut StarRng,
        a: &A,
        b: &Model<P>,
    ) -> P {
        if let Some((_, t)) = b.get_rand(rng)
            && (rng.index_inclusive(7) != 0)
        {
            t.p
        } else {
            gen_invalid(rng, a)
        }
    }
    let p0 = rand_p(rng, a, b);
    // half of the time this is the actual next link of `p0`, which is what makes
    // `AtInterlink` and `Bridge` reach their success cases often
    let p1 = if rng.next_bool()
        && let Some(k) = key_of(a, p0)
        && let Some(next) = m_next(b, k)
    {
        m_p(b, next)
    } else {
        rand_p(rng, a, b)
    };
    match rng.index_inclusive(13) {
        0 => LinkInsertKind::Disconnected,
        1 => LinkInsertKind::SingleLinkCyclic,
        2 => LinkInsertKind::ChainStart(p0),
        3 => LinkInsertKind::ChainStartInx(p0.inx()),
        4 => LinkInsertKind::ChainEnd(p0),
        5 => LinkInsertKind::ChainEndInx(p0.inx()),
        6 => LinkInsertKind::PrevTo(p0),
        7 => LinkInsertKind::PrevToInx(p0.inx()),
        8 => LinkInsertKind::NextTo(p0),
        9 => LinkInsertKind::NextToInx(p0.inx()),
        10 => LinkInsertKind::AtInterlink {
            next_to: p0,
            prev_to: p1,
        },
        11 => LinkInsertKind::AtInterlinkInx {
            next_to: p0.inx(),
            prev_to: p1.inx(),
        },
        12 => LinkInsertKind::Bridge { end: p0, start: p1 },
        13 => LinkInsertKind::BridgeInx {
            end: p0.inx(),
            start: p1.inx(),
        },
        _ => unreachable!(),
    }
}

/// Which of the parallel insertion functions to use
#[derive(Clone, Copy, PartialEq, Eq)]
enum How {
    WithinCapacity,
    Reallocating,
    Panicking,
    EntryWithinCapacity,
    EntryReallocating,
    EntryPanicking,
    /// An entry that is dropped instead of inserted into
    Cancel,
}

impl How {
    fn is_panicking(self) -> bool {
        matches!(self, How::Panicking | How::EntryPanicking)
    }

    fn is_reallocating(self) -> bool {
        matches!(
            self,
            How::Reallocating | How::EntryReallocating | How::Panicking | How::EntryPanicking
        )
    }
}

/// Attempts an insertion of `kind`, determining the expected outcome from the
/// model beforehand and recording a successful insertion in `b`
fn try_chain_insert<
    P: Ptr,
    A: CompactArenaTrait<P, Cd<()>> + DisjointableArenaTrait<P, Cd<()>> + ChainArenaTrait<P, Cd<()>>,
>(
    a: &mut A,
    b: &mut Model<P>,
    cd_gen: &mut CdGen<()>,
    g: &TestGen<P>,
    kind: LinkInsertKind<P>,
    how: How,
    test_limit: usize,
) -> Result<(), StackedError> {
    let len = a.len();
    let cap = a.capacity();
    let expect = expect_kind(a, b, kind);
    let max_reached = a
        .max_capacity()
        .is_some_and(|max_capacity| max_capacity == len);
    // what a met link requirement would then run into, if anything
    let capacity_err = if len < cap {
        None
    } else if !how.is_reallocating() {
        Some(ChainInsertionError::NotWithinCapacity)
    } else if max_reached {
        Some(ChainInsertionError::BeyondMaxCapacity)
    } else {
        None
    };
    if how.is_panicking() && capacity_err.is_some() {
        // these would panic, and the parallel fallible functions already cover the
        // error paths
        return Ok(());
    }
    if matches!(expect, Expect::Fail) {
        // the link requirement is checked before any capacity is used, so it takes
        // priority over what the capacity is doing
        let res = match how {
            How::WithinCapacity | How::Panicking => a
                .insert_within_capacity(kind, cd_gen.new_cd().1)
                .map(|_| ()),
            How::Reallocating => a.insert_reallocating(kind, cd_gen.new_cd().1).map(|_| ()),
            How::EntryWithinCapacity | How::EntryPanicking | How::Cancel => {
                a.entry_insert_within_capacity(kind).map(|_| ())
            }
            How::EntryReallocating => a.entry_insert_reallocating(kind).map(|_| ()),
        };
        ensure_eq!(res, Err(ChainInsertionError::FailedLinkRequirement));
        ensure_eq!(a.len(), len);
        ensure_eq!(a.capacity(), cap);
        return Ok(());
    }
    if let Some(capacity_err) = capacity_err {
        let res = match how {
            How::WithinCapacity => a
                .insert_within_capacity(kind, cd_gen.new_cd().1)
                .map(|_| ()),
            How::Reallocating => a.insert_reallocating(kind, cd_gen.new_cd().1).map(|_| ()),
            How::EntryWithinCapacity | How::Cancel => {
                a.entry_insert_within_capacity(kind).map(|_| ())
            }
            How::EntryReallocating => a.entry_insert_reallocating(kind).map(|_| ()),
            How::Panicking | How::EntryPanicking => unreachable!(),
        };
        ensure_eq!(res, Err(capacity_err));
        ensure_eq!(a.len(), len);
        ensure_eq!(a.capacity(), cap);
        return Ok(());
    }
    if (len == cap) && (len >= test_limit) {
        // stay around the limit instead of growing without bound
        return Ok(());
    }
    let (k, t) = cd_gen.new_cd();
    let p = match how {
        How::WithinCapacity => a.insert_within_capacity(kind, t).ok().stack()?,
        How::Reallocating => a.insert_reallocating(kind, t).ok().stack()?,
        How::Panicking => a.insert(kind, t),
        How::EntryWithinCapacity => {
            let Ok(entry) = a.entry_insert_within_capacity(kind) else {
                bail!("expected capacity to be available")
            };
            let p = entry.ptr();
            entry.insert(t);
            p
        }
        How::EntryReallocating => {
            let Ok(entry) = a.entry_insert_reallocating(kind) else {
                bail!("expected the capacity to be able to grow")
            };
            let p = entry.ptr();
            entry.insert(t);
            p
        }
        How::EntryPanicking => {
            let entry = a.entry_insert(kind);
            let p = entry.ptr();
            entry.insert(t);
            p
        }
        How::Cancel => {
            let Ok(entry) = a.entry_insert_within_capacity(kind) else {
                bail!("expected capacity to be available")
            };
            let p = entry.ptr();
            ensure_eq!(p.generation(), g.0);
            // REF(insertion_idempotency)
            drop(entry);
            drop(t);
            ensure!(!a.contains(p));
            ensure_eq!(a.len(), len);
            ensure_eq!(a.capacity(), cap);
            // and the chain that the entry was going to attach to was not touched
            check_model(a, b).stack()?;
            return Ok(());
        }
    };
    ensure_eq!(p.generation(), g.0);
    ensure_eq!(a.len(), len + 1);
    ensure_eq!(a.get(p).stack()?.key(), k);
    if how.is_reallocating() && (len == cap) {
        ensure!(a.capacity() > cap);
    } else {
        ensure_eq!(a.capacity(), cap);
    }
    m_insert(b, k, p, &expect);
    Ok(())
}

/// Rebuilds the `p` fields of the model from `a`, which is what the operations
/// that move entries around without being able to report the new `Ptr`s need.
/// The chain structure in the model is left alone so that `check_model` still
/// verifies it.
fn refresh_model_ptrs<P: Ptr, A: ChainArenaTrait<P, Cd<()>>>(
    a: &A,
    b: &mut Model<P>,
) -> Result<(), StackedError> {
    for (p, t) in a.iter() {
        b.get_mut(t.key()).stack()?.p = p;
    }
    Ok(())
}

/// Rebuilds the whole model from `a`. This is only used where the structure has
/// already been checked against what it was before the operation.
fn rebuild_model<P: Ptr, A: ChainArenaTrait<P, Cd<()>>>(
    a: &A,
    b: &mut Model<P>,
) -> Result<(), StackedError> {
    let mut by_inx = HashMap::new();
    for (p, t) in a.iter() {
        by_inx.insert(p.inx(), t.key());
    }
    b.clear();
    for (p, link) in a.iter_link_no_gen() {
        let prev = match link.prev() {
            Some(inx) => Some(*by_inx.get(&inx).stack()?),
            None => None,
        };
        let next = match link.next() {
            Some(inx) => Some(*by_inx.get(&inx).stack()?),
            None => None,
        };
        b.insert(link.t.key(), TLink { p, prev, next });
    }
    Ok(())
}

/// The `(p, prev_next)` of every link of a concrete chain arena
fn snapshot<P: Ptr, T, B: ArenaBacking>(
    a: &ChainArena<P, T, B>,
) -> Vec<(P, (Option<P::Inx>, Option<P::Inx>))> {
    a.iter_link_no_gen()
        .map(|(p, link)| (p, link.prev_next()))
        .collect()
}

pub fn fuzz<
    P: Ptr,
    A: CompactArenaTrait<P, Cd<()>> + ChainArenaTrait<P, Cd<()>> + DisjointableArenaTrait<P, Cd<()>>,
    B1: ArenaBacking,
>(
    meta: &mut Meta<Stats>,
    a: &mut A,
    mut check_invariants: impl FnMut(&mut A) -> Result<(), StackedError>,
    // set iff `SetMaxCapacity` is implemented
    set_max_capacity: Option<fn(&mut A, usize) -> Result<(), MaxCapacityReductionError>>,
    // `ChainArena::clone_from_with` is inherent and needs a concrete chain arena on
    // both sides, so both directions are passed in
    clone_to_a1: fn(
        &mut ChainArena<P, Cd<D1>, B1>,
        &A,
        &mut dyn FnMut(P, &LinkNoGen<P, Cd<()>>) -> Cd<D1>,
    ) -> Result<(), ReallocationError>,
    clone_from_a1: fn(
        &mut A,
        &ChainArena<P, Cd<D1>, B1>,
        &mut dyn FnMut(P, &LinkNoGen<P, Cd<D1>>) -> Cd<()>,
    ) -> Result<(), ReallocationError>,
    transfer_from_a1: fn(
        &mut A,
        P::Gen,
        &mut ChainArena<P, Cd<D1>, B1>,
        &mut dyn FnMut(P, InvalidationOption<Cd<D1>>, P) -> Cd<()>,
        &mut DirectArena<P, P, StackBacking<128>>,
    ) -> Result<(), ReallocationError>,
) -> Result<(), StackedError> {
    let rng = &mut meta.rng;
    let stats = meta.stats.as_mut().stack()?;
    let cd_gen = &mut stats.cd_gen;
    let cd_gen1 = &mut stats.cd_gen1;

    let mut b = Model::<P>::new();
    let mut b_capacity = a.capacity();
    let mut g = TestGen::<P>(PtrGen::two());

    // set and used by the clone_from and transfer sections
    let mut a1 = ChainArena::<P, Cd<D1>, B1>::new();
    let mut recaster = DirectArena::<P, P, StackBacking<128>>::new();

    // makes sure there is not some problem with the test harness itself or
    // determinism
    let mut iters999 = 0;
    let mut max_len = 0usize;

    for i in 0..stats.n {
        let len = b.len();
        max_len = max(max_len, len);
        ensure_eq!(cd_gen.len(), len);
        ensure_eq!(a.len(), len);
        ensure_eq!(a.is_empty(), b.is_empty());
        ensure_eq!(a.capacity(), b_capacity);
        ensure!(len <= a.capacity());
        if let Some(fixed_cap) = stats.fixed_cap {
            ensure_eq!(a.capacity(), fixed_cap);
        }
        if let Some(max_capacity) = a.max_capacity() {
            ensure!(a.capacity() <= max_capacity);
        }
        // if not incremented explicitly and the arena increments, then we get a
        // mismatch
        ensure_eq!(a.singular_generation().stack()?, g.0);
        check_invariants(a).stack()?;
        check_model(a, &b).stack()?;

        meta.i = i;
        meta.op_inx = rng.index_inclusive(1023);
        // note: insertions and removals are balanced except for clears which we make
        // rare
        match meta.op_inx {
            0..250 => common_compact_fuzz_step250(
                rng,
                a,
                stats.test_limit,
                meta.op_inx,
                &mut b,
                &mut b_capacity,
                Some(&mut g),
                set_max_capacity,
                |b, rng| b.get_mut_rand(rng).map(|(k, t)| (k, &mut t.p)),
                Cd::key,
            )
            .stack()?,
            250..500 => {
                // all of the insertion functions with all of the `LinkInsertKind`s
                let kind = rand_kind(rng, a, &b);
                let how = match rng.index_inclusive(5) {
                    0 => How::WithinCapacity,
                    1 => How::Reallocating,
                    2 => How::Panicking,
                    3 => How::EntryWithinCapacity,
                    4 => How::EntryReallocating,
                    5 => How::EntryPanicking,
                    _ => unreachable!(),
                };
                try_chain_insert(a, &mut b, cd_gen, &g, kind, how, stats.test_limit).stack()?;
                b_capacity = a.capacity();
            }
            500..525 => {
                // insertion with cancellation
                let kind = rand_kind(rng, a, &b);
                try_chain_insert(a, &mut b, cd_gen, &g, kind, How::Cancel, stats.test_limit)
                    .stack()?;
            }
            525..625 => {
                // remove and remove_link_no_gen
                if let Some((k, t)) = b.get_rand(rng) {
                    let (p, prev, next) = (t.p, t.prev, t.next);
                    let expected_prev_next = (
                        prev.map(|k| m_p(&b, k).inx()),
                        next.map(|k| m_p(&b, k).inx()),
                    );
                    if rng.next_bool() {
                        match a.remove(p) {
                            InvalidationResult::Success(u) => {
                                ensure_eq!(k, u.key());
                                ensure!(!g.invalidate());
                            }
                            InvalidationResult::GenerationOverflow(u) => {
                                ensure_eq!(k, u.key());
                                ensure!(g.invalidate());
                            }
                            InvalidationResult::InvalidPtr => bail!(),
                        }
                    } else {
                        // the removed link still carries the interlinks it had
                        let link = match a.remove_link_no_gen(p) {
                            InvalidationResult::Success(link) => {
                                ensure!(!g.invalidate());
                                link
                            }
                            InvalidationResult::GenerationOverflow(link) => {
                                ensure!(g.invalidate());
                                link
                            }
                            InvalidationResult::InvalidPtr => bail!(),
                        };
                        ensure_eq!(link.t.key(), k);
                        ensure_eq!(link.prev_next(), expected_prev_next);
                    }
                    let t = b.remove_key(k).stack()?;
                    m_splice(&mut b, k, &t);
                } else {
                    let invalid = gen_invalid(rng, a);
                    ensure!(matches!(a.remove(invalid), InvalidationResult::InvalidPtr));
                    ensure!(matches!(
                        a.remove_link_no_gen(invalid),
                        InvalidationResult::InvalidPtr
                    ));
                }
            }
            625..725 => {
                // remove_inx and remove_inx_link_no_gen
                if let Some((k, t)) = b.get_rand(rng) {
                    let (p, prev, next) = (t.p, t.prev, t.next);
                    let expected_prev_next = (
                        prev.map(|k| m_p(&b, k).inx()),
                        next.map(|k| m_p(&b, k).inx()),
                    );
                    if rng.next_bool() {
                        match a.remove_inx(p.inx()) {
                            InvalidationResult::Success((generation, u)) => {
                                ensure_eq!(generation, p.generation());
                                ensure_eq!(k, u.key());
                                ensure!(!g.invalidate());
                            }
                            InvalidationResult::GenerationOverflow((generation, u)) => {
                                ensure_eq!(generation, p.generation());
                                ensure_eq!(k, u.key());
                                ensure!(g.invalidate());
                            }
                            InvalidationResult::InvalidPtr => bail!(),
                        }
                    } else {
                        let (generation, link) = match a.remove_inx_link_no_gen(p.inx()) {
                            InvalidationResult::Success(x) => {
                                ensure!(!g.invalidate());
                                x
                            }
                            InvalidationResult::GenerationOverflow(x) => {
                                ensure!(g.invalidate());
                                x
                            }
                            InvalidationResult::InvalidPtr => bail!(),
                        };
                        ensure_eq!(generation, p.generation());
                        ensure_eq!(link.t.key(), k);
                        ensure_eq!(link.prev_next(), expected_prev_next);
                    }
                    let t = b.remove_key(k).stack()?;
                    m_splice(&mut b, k, &t);
                } else {
                    let invalid = gen_invalid(rng, a);
                    if a.get_inx(invalid.inx()).is_none() {
                        ensure!(matches!(
                            a.remove_inx(invalid.inx()),
                            InvalidationResult::InvalidPtr
                        ));
                        ensure!(matches!(
                            a.remove_inx_link_no_gen(invalid.inx()),
                            InvalidationResult::InvalidPtr
                        ));
                    }
                }
            }
            725..750 => {
                // removes and link lookups all invalid
                let invalid = gen_invalid(rng, a);
                ensure!(matches!(a.remove(invalid), InvalidationResult::InvalidPtr));
                ensure!(matches!(
                    a.remove_link_no_gen(invalid),
                    InvalidationResult::InvalidPtr
                ));
                ensure!(a.get_link(invalid).is_none());
                ensure!(a.get_link_no_gen(invalid).is_none());
                if a.get_inx(invalid.inx()).is_none() {
                    ensure!(a.get_inx_link_no_gen(invalid.inx()).is_none());
                    ensure!(matches!(
                        a.remove_inx(invalid.inx()),
                        InvalidationResult::InvalidPtr
                    ));
                    ensure!(matches!(
                        a.remove_inx_link_no_gen(invalid.inx()),
                        InvalidationResult::InvalidPtr
                    ));
                }
            }
            750..800 => {
                // are_neighbors and are_neighbors_inx
                let (p0, k0) = if let Some((k, t)) = b.get_rand(rng) {
                    (t.p, Some(k))
                } else {
                    (gen_invalid(rng, a), None)
                };
                // half of the time use the actual next link, so that the true case is
                // reached often
                let (p1, k1) = if rng.next_bool()
                    && let Some(k0) = k0
                    && let Some(next) = m_next(&b, k0)
                {
                    (m_p(&b, next), Some(next))
                } else if let Some((k, t)) = b.get_rand(rng) {
                    (t.p, Some(k))
                } else {
                    (gen_invalid(rng, a), None)
                };
                let expected = match (k0, k1) {
                    (Some(k0), Some(k1)) => m_next(&b, k0) == Some(k1),
                    _ => false,
                };
                ensure_eq!(a.are_neighbors(p0, p1), expected);
                // the index version additionally accepts a stale generation on either
                // side, which only differs when the index does hold a link
                let expected_inx = match (key_of_inx(a, p0.inx()), key_of_inx(a, p1.inx())) {
                    (Some(k0), Some(k1)) => m_next(&b, k0) == Some(k1),
                    _ => false,
                };
                ensure_eq!(a.are_neighbors_inx(p0.inx(), p1.inx()), expected_inx);
            }
            800..860 => {
                // connect, break_prev, break_next
                let (p0, k0) = if let Some((k, t)) = b.get_rand(rng) {
                    (t.p, Some(k))
                } else {
                    (gen_invalid(rng, a), None)
                };
                match rng.index_inclusive(2) {
                    0 => {
                        // connect, where `p1` is invalid independently of `p0` so that
                        // the short circuit on either side is reached
                        let (p1, k1) = if rng.index_inclusive(3) != 0
                            && let Some((k, t)) = b.get_rand(rng)
                        {
                            (t.p, Some(k))
                        } else {
                            (gen_invalid(rng, a), None)
                        };
                        let expected = match (k0, k1) {
                            (Some(k0), Some(k1)) => {
                                m_next(&b, k0).is_none() && m_prev(&b, k1).is_none()
                            }
                            _ => false,
                        };
                        ensure_eq!(a.connect(p0, p1).is_some(), expected);
                        if expected {
                            let (k0, k1) = (k0.stack()?, k1.stack()?);
                            m_set_next(&mut b, k0, Some(k1));
                            m_set_prev(&mut b, k1, Some(k0));
                        }
                    }
                    1 => {
                        // break_prev
                        let expected = k0.map(|k| m_prev(&b, k)).unwrap_or(None);
                        ensure_eq!(a.break_prev(p0).is_some(), expected.is_some());
                        if let Some(prev) = expected {
                            let k0 = k0.stack()?;
                            m_set_next(&mut b, prev, None);
                            m_set_prev(&mut b, k0, None);
                        }
                    }
                    2 => {
                        // break_next
                        let expected = k0.map(|k| m_next(&b, k)).unwrap_or(None);
                        ensure_eq!(a.break_next(p0).is_some(), expected.is_some());
                        if let Some(next) = expected {
                            let k0 = k0.stack()?;
                            m_set_next(&mut b, k0, None);
                            m_set_prev(&mut b, next, None);
                        }
                    }
                    _ => unreachable!(),
                }
            }
            860..900 => {
                // exchange_next
                let (p0, k0) = if let Some((k, t)) = b.get_rand(rng) {
                    (t.p, Some(k))
                } else {
                    (gen_invalid(rng, a), None)
                };
                // often use a link from the same chain, which is what splits and merges
                // cycles
                let (p1, k1) = if rng.next_bool()
                    && let Some(k0) = k0
                    && let Some(next) = m_next(&b, k0)
                {
                    (m_p(&b, next), Some(next))
                } else if let Some((k, t)) = b.get_rand(rng) {
                    (t.p, Some(k))
                } else {
                    (gen_invalid(rng, a), None)
                };
                let expected = match (k0, k1) {
                    (Some(k0), Some(k1)) => match (m_next(&b, k0), m_next(&b, k1)) {
                        (Some(d0), Some(d1)) => Some((k0, k1, d0, d1)),
                        _ => None,
                    },
                    _ => None,
                };
                ensure_eq!(a.exchange_next(p0, p1).is_some(), expected.is_some());
                if let Some((k0, k1, d0, d1)) = expected {
                    // this has to follow the same order that the arena uses, because
                    // the links can alias each other
                    m_set_next(&mut b, k0, Some(d1));
                    m_set_next(&mut b, k1, Some(d0));
                    m_set_prev(&mut b, d0, Some(k1));
                    m_set_prev(&mut b, d1, Some(k0));
                }
            }
            900..940 => {
                // advancer_chain and iter_chain
                if let Some((k, t)) = b.get_rand(rng) {
                    let p_init = t.p;
                    let expected = m_chain(&b, k);
                    let mut i = 0;
                    let mut adv = a.advancer_chain(p_init).stack()?;
                    while let Some(p) = adv.advance(a) {
                        ensure_eq!(p, m_p(&b, *expected.get(i).stack()?));
                        i += 1;
                    }
                    ensure_eq!(i, expected.len());
                    let mut i = 0;
                    for (p, link) in a.iter_chain(p_init).stack()? {
                        let k = *expected.get(i).stack()?;
                        ensure_eq!(p, m_p(&b, k));
                        ensure_eq!(link.t.key(), k);
                        i += 1;
                    }
                    ensure_eq!(i, expected.len());
                } else {
                    let invalid = gen_invalid(rng, a);
                    ensure!(a.advancer_chain(invalid).is_none());
                    ensure!(a.iter_chain(invalid).is_none());
                }
            }
            // extra room
            940..1008 => {
                if let Some((_, t)) = b.get_rand(rng) {
                    let p = t.p;
                    ensure!(a.contains(p));
                } else {
                    let p = gen_invalid(rng, a);
                    ensure!(!a.contains(p));
                }
            }
            1008 => {
                // drain_chain
                if let Some((k, t)) = b.get_rand(rng) {
                    let p_init = t.p;
                    let expected = m_chain(&b, k);
                    let mut i = 0;
                    // the whole chain is removed even though only part is iterated
                    let stop_at = rng.index_inclusive(expected.len());
                    {
                        let mut drain = a.drain_chain(p_init).stack()?;
                        while i < stop_at
                            && let Some(o) = drain.next()
                        {
                            ensure_eq!(o.is_overflow(), g.invalidate());
                            let (p, link) = o.allow();
                            let k = *expected.get(i).stack()?;
                            ensure_eq!(p, m_p(&b, k));
                            ensure_eq!(link.t.key(), k);
                            i += 1;
                        }
                    }
                    // the rest was dropped by the `Drop` impl
                    for _ in i..expected.len() {
                        ensure!(!g.invalidate());
                    }
                    for k in expected {
                        b.remove_key(k).stack()?;
                    }
                    // the links that were spliced out of other chains are gone, and the
                    // model has no dangling keys because whole chains are removed
                    for (_, t) in b.iter() {
                        ensure!(t.prev.map(|k| b.get(k).is_some()).unwrap_or(true));
                    }
                } else {
                    let invalid = gen_invalid(rng, a);
                    ensure!(a.drain_chain(invalid).is_none());
                }
            }
            1009..1015 => {
                // compress_canonical
                let reset = rng.next_bool();
                let o = a.compress_canonical(reset).is_overflow();
                if reset {
                    g.0 = PtrGen::two();
                    ensure!(!o);
                } else if a.is_empty() {
                    ensure!(!o);
                } else {
                    ensure_eq!(o, g.invalidate());
                }
                refresh_model_ptrs(a, &mut b).stack()?;
                check_canonical_layout(a).stack()?;
            }
            1015 => {
                // compress
                let reset = rng.next_bool();
                let o = a.compress(reset).is_overflow();
                if reset {
                    g.0 = PtrGen::two();
                    ensure!(!o);
                } else if a.is_empty() {
                    ensure!(!o);
                } else {
                    ensure_eq!(o, g.invalidate());
                }
                refresh_model_ptrs(a, &mut b).stack()?;
                if len > 0 {
                    ensure_eq!(
                        PtrInx::try_into_usize(a.find_last_inx_ptr().stack()?.inx())
                            .stack()?
                            .get(),
                        a.len()
                    );
                }
            }
            1016 => {
                // compress_with
                let mut new_map = vec![];
                let mut res = Ok(());
                let reset = rng.next_bool();
                let o = a
                    .compress_with(reset, |p_old, t, p_new| {
                        if *b.get(t.key()).map(|t| &t.p).unwrap() != p_old {
                            res = Err(());
                        }
                        new_map.push((p_new, t.key()));
                    })
                    .is_overflow();
                ensure!(res.is_ok());
                if reset {
                    g.0 = PtrGen::two();
                    ensure!(!o);
                } else if a.is_empty() {
                    ensure!(!o);
                } else {
                    ensure_eq!(o, g.invalidate());
                }
                ensure_eq!(new_map.len(), len);
                for (p, k) in new_map {
                    b.get_mut(k).stack()?.p = p;
                }
                if len > 0 {
                    ensure_eq!(
                        PtrInx::try_into_usize(a.find_last_inx_ptr().stack()?.inx())
                            .stack()?
                            .get(),
                        a.len()
                    );
                }
            }
            // these are mainly tested in `multi_chain_arena`, but we want them here to test if
            // `self.m.len()` and `self.m.capacity()` detachments cause issues
            1017 => {
                // clone_to_a1

                // `a1` and the like are set here, `a` will diverge again

                let mut i = 0;
                clone_to_a1(&mut a1, a, &mut |p, u| {
                    assert_eq!(a.get(p).unwrap().key(), u.t.key());
                    let (_, t) = cd_gen1.new_cd();
                    i += 1;
                    t
                })
                .unwrap();
                ensure_eq!(len, i);
                // the `Ptr`s and the whole interlink structure were cloned
                for (p, link) in a.iter_link_no_gen() {
                    ensure_eq!(a1.get_link_no_gen(p).stack()?.prev_next(), link.prev_next());
                }
                ensure_eq!(a1.len(), len);
            }
            1018 => {
                // clone_from_a1

                // `a1` was unlimited, `a` can be limited and grow capacity and run into
                // changed limits

                if rng.next_bool() {
                    // add a high `Ptr` for fixed capacity cases to deal with
                    for _ in 0..stats.test_limit {
                        if a1
                            .insert_reallocating(LinkInsertKind::Disconnected, cd_gen1.new_cd().1)
                            .is_err()
                        {
                            break;
                        }
                    }
                }

                let before = a.capacity();
                let max_before = a.max_capacity();
                let a1_snapshot = snapshot(&a1);
                let mut on_first_call = true;
                let res = clone_from_a1(a, &a1, &mut |p, u| {
                    assert_eq!(a1.get(p).unwrap().key(), u.t.key());
                    if on_first_call {
                        b.clear();
                        on_first_call = false;
                    }
                    let (_, t) = cd_gen.new_cd();
                    t
                });
                if let Some(max) = max_before
                    && let Some(last) = a1.find_last_inx_ptr()
                    && PtrInx::try_into_usize(last.inx()).stack()?.get() > max
                {
                    ensure!(on_first_call);
                    ensure_eq!(res, Err(ReallocationError::BeyondMaxCapacity));
                } else {
                    // if `a1` was empty
                    if on_first_call {
                        b.clear();
                    }
                    ensure_eq!(res, Ok(()));
                    // the `Ptr`s and the whole interlink structure were cloned
                    for (p, prev_next) in a1_snapshot {
                        ensure_eq!(a.get_link_no_gen(p).stack()?.prev_next(), prev_next);
                    }
                    ensure_eq!(a.max_capacity(), max_before);
                    ensure!(a.capacity() >= before);
                    g.0 = a1.singular_generation().stack()?;
                    b_capacity = a.capacity();
                    rebuild_model(a, &mut b).stack()?;
                }
            }
            1019 => {
                // transfer_canonical_reallocating into `a1`

                let mut list = vec![];
                // do something that isn't setting to a low constant
                let next_gen = PtrGen::generational_inc(g.0).0;
                a1.transfer_canonical_reallocating(
                    next_gen,
                    a,
                    |q, o, p| {
                        assert_eq!(o.is_overflow(), g.invalidate());
                        let u = o.allow();
                        list.push((u.key(), q, p));
                        let (_, t) = cd_gen1.new_cd();
                        t
                    },
                    &mut recaster,
                )
                .unwrap();
                ensure!(a.is_empty());
                ensure_eq!(list.len(), len);
                // the chain structure survived the transfer
                let mut new_p = HashMap::new();
                for (k, q, p) in &list {
                    ensure_eq!(*recaster.get(*q).stack()?, *p);
                    ensure_eq!(p.generation(), next_gen);
                    new_p.insert(*k, *p);
                }
                for (k, t) in b.iter() {
                    let p = *new_p.get(&k).stack()?;
                    let link = a1.get_link_no_gen(p).stack()?;
                    let expected_prev = match t.prev {
                        Some(k) => Some(new_p.get(&k).stack()?.inx()),
                        None => None,
                    };
                    let expected_next = match t.next {
                        Some(k) => Some(new_p.get(&k).stack()?.inx()),
                        None => None,
                    };
                    ensure_eq!(link.prev(), expected_prev);
                    ensure_eq!(link.next(), expected_next);
                }
                b.clear();
            }
            1020 => {
                // transfer_canonical_reallocating from `a1`

                if rng.next_bool() {
                    // add a high `Ptr` for fixed capacity cases to deal with
                    for _ in 0..stats.test_limit {
                        if a1
                            .insert_reallocating(LinkInsertKind::Disconnected, cd_gen1.new_cd().1)
                            .is_err()
                        {
                            break;
                        }
                    }
                }

                let before = a.capacity();
                let max_before = a.max_capacity();
                let a1_len = a1.len();
                let a1_snapshot = snapshot(&a1);
                let mut on_first_call = true;
                let mut map = |_q: P, _o: InvalidationOption<Cd<D1>>, _p: P| -> Cd<()> {
                    if on_first_call {
                        b.clear();
                        on_first_call = false;
                    }
                    let (_, t) = cd_gen.new_cd();
                    t
                };
                let next_gen = PtrGen::generational_inc(g.0).0;
                let res = transfer_from_a1(a, next_gen, &mut a1, &mut map, &mut recaster);
                if let Some(max) = max_before
                    && a1_len > max
                {
                    ensure!(on_first_call);
                    ensure_eq!(res, Err(ReallocationError::BeyondMaxCapacity));
                } else {
                    // if `a1` was empty
                    if on_first_call {
                        b.clear();
                    }
                    ensure_eq!(res, Ok(()));
                    ensure!(a1.is_empty());
                    ensure_eq!(a.len(), a1_len);
                    ensure_eq!(a.max_capacity(), max_before);
                    ensure!(a.capacity() >= before);
                    // the chain structure survived, and is canonically laid out
                    for (q, prev_next) in a1_snapshot {
                        let p = *recaster.get(q).stack()?;
                        ensure_eq!(p.generation(), next_gen);
                        let link = a.get_link_no_gen(p).stack()?;
                        let expected_prev = match prev_next.0 {
                            Some(inx) => Some(recaster.get_inx(inx).stack()?.1.inx()),
                            None => None,
                        };
                        let expected_next = match prev_next.1 {
                            Some(inx) => Some(recaster.get_inx(inx).stack()?.1.inx()),
                            None => None,
                        };
                        ensure_eq!(link.prev(), expected_prev);
                        ensure_eq!(link.next(), expected_next);
                    }
                    check_canonical_layout(a).stack()?;
                    g.0 = next_gen;
                    b_capacity = a.capacity();
                    rebuild_model(a, &mut b).stack()?;
                }
            }
            1021 => {
                // drain
                for tmp in a.drain() {
                    ensure_eq!(tmp.is_overflow(), g.invalidate());
                    let (p, t) = tmp.allow();
                    ensure_eq!(m_p(&b, t.key()), p);
                }
                ensure!(a.is_empty());
                b.clear();
            }
            1022 => {
                // clear
                b.clear();
                if a.is_empty() {
                    ensure_eq!(a.clear(), InvalidationOption::Success(()));
                } else {
                    ensure_eq!(a.clear().is_overflow(), g.invalidate());
                }
            }
            1023 => {
                // with_min_capacity and the `Drop` impl
                b.clear();
                // note that we bypass max capacity limits since they are set to begin with in
                // some cases from this function

                // could succeed for ZSTs
                ensure_eq!(
                    A::with_min_capacity(usize::MAX).map(|_| ()),
                    Err(AllocError)
                );

                let min_capacity = rng.index_inclusive(stats.test_limit);
                *a = A::with_min_capacity(min_capacity).stack()?;
                ensure!(a.capacity() >= min_capacity);
                if stats.fixed_cap.is_some() {
                    stats.fixed_cap = Some(a.capacity());
                }
                g.0 = a.singular_generation().stack()?;
                b_capacity = a.capacity();
                iters999 += 1;
            }
            1024.. => unreachable!(),
        }
    }
    if let Some(x) = &stats.iters999 {
        x.assert_debug_eq(&iters999);
    }
    if let Some(x) = &stats.max_len {
        x.assert_debug_eq(&max_len);
    }
    a.clear().allow();
    a1.clear().allow();
    Ok(())
}

/// A small chain arena fuzz step that only needs the concrete type, used to
/// build up interesting chain structures on both sides of the operations that
/// interact between two arenas
pub fn fuzz_multi_chain_arena_step<D: Copy + Default, P: Ptr>(
    rng: &mut StarRng,
    a: &mut ChainArena<P, Cd<D>, StackBacking<128>>,
    g: &mut TestGen<P>,
    b: &mut CkMap<D, P>,
    cd_gen: &mut CdGen<D>,
) -> Result<(), StackedError> {
    let len: usize = a.len();
    ensure_eq!(len, b.len());
    ensure_eq!(a.singular_generation().stack()?, g.0);
    ensure_eq!(a.is_empty(), b.is_empty());
    if !cfg!(miri) {
        ChainArena::_check_invariants(a).unwrap();
    }
    // a random existing link
    let rand_p = |rng: &mut StarRng, b: &CkMap<D, P>| b.get_rand(rng).map(|(_, p)| *p);
    match rng.index_inclusive(127) {
        0..48 => {
            // insert, which grows chains in every direction
            let kind = match (rand_p(rng, b), rng.index_inclusive(5)) {
                (_, 0) => LinkInsertKind::Disconnected,
                (_, 1) => LinkInsertKind::SingleLinkCyclic,
                (Some(p), 2) => LinkInsertKind::NextTo(p),
                (Some(p), 3) => LinkInsertKind::PrevTo(p),
                (Some(p), 4) => LinkInsertKind::ChainEnd(p),
                (Some(p), _) => LinkInsertKind::ChainStart(p),
                (None, _) => LinkInsertKind::Disconnected,
            };
            let (k, t) = cd_gen.new_cd();
            match a.insert_reallocating(kind, t) {
                Ok(p) => b.insert(k, p),
                Err(e) => ensure_eq!(e, ChainInsertionError::FailedLinkRequirement),
            }
        }
        48..64 => {
            // connect and bridge, which is what creates cycles and joins chains
            if let (Some(p0), Some(p1)) = (rand_p(rng, b), rand_p(rng, b)) {
                if rng.next_bool() {
                    let _ = a.connect(p0, p1);
                } else {
                    let (k, t) = cd_gen.new_cd();
                    match a.insert_reallocating(LinkInsertKind::Bridge { end: p0, start: p1 }, t) {
                        Ok(p) => b.insert(k, p),
                        Err(e) => ensure_eq!(e, ChainInsertionError::FailedLinkRequirement),
                    }
                }
            }
        }
        64..80 => {
            // break and exchange, which is what splits chains and cycles apart
            if let (Some(p0), Some(p1)) = (rand_p(rng, b), rand_p(rng, b)) {
                match rng.index_inclusive(2) {
                    0 => {
                        let _ = a.break_prev(p0);
                    }
                    1 => {
                        let _ = a.break_next(p0);
                    }
                    _ => {
                        let _ = a.exchange_next(p0, p1);
                    }
                }
            }
        }
        80..127 => {
            // remove
            if len != 0 {
                let (k, p) = b.remove_rand(rng).unwrap();
                ensure_eq!(k, a.remove(p).allow().stack()?.key());
                g.invalidate();
            }
        }
        127 => {
            // clear and shrink
            if !a.is_empty() {
                ensure_eq!(a.clear().strict().is_err(), g.invalidate());
            }
            a.reallocate_min_capacity(0).unwrap();
            b.clear();
        }
        128.. => unreachable!(),
    }
    Ok(())
}

/// Checks that a transfer between two chain arenas preserved the interlink
/// structure that `source_snapshot` recorded, and left `dst` canonical
fn check_transfer<P: Ptr, T, B: ArenaBacking, B1: ArenaBacking>(
    dst: &ChainArena<P, T, B>,
    source_snapshot: &[(P, (Option<P::Inx>, Option<P::Inx>))],
    recaster: &DirectArena<P, P, B1>,
    new_generation: P::Gen,
) -> Result<(), StackedError> {
    for (q, prev_next) in source_snapshot {
        let p = *recaster.get(*q).stack()?;
        ensure_eq!(p.generation(), new_generation);
        let link = dst.get_link_no_gen(p).stack()?;
        let expected_prev = match prev_next.0 {
            Some(inx) => Some(recaster.get_inx(inx).stack()?.1.inx()),
            None => None,
        };
        let expected_next = match prev_next.1 {
            Some(inx) => Some(recaster.get_inx(inx).stack()?.1.inx()),
            None => None,
        };
        ensure_eq!(link.prev(), expected_prev);
        ensure_eq!(link.next(), expected_next);
    }
    ensure_eq!(dst.len(), source_snapshot.len());
    Ok(())
}

/// After any of the canonicalizing operations, the internal slot length must be
/// trimmed to exactly the last allocated index. This is what keeps repeatedly
/// cloning and transferring between two arenas from creeping upwards, see
/// REF(exponential_double_buffer_blowup).
fn ensure_canonical_len<P: Ptr, T, B: ArenaBacking>(
    a: &ChainArena<P, T, B>,
) -> Result<(), StackedError> {
    let expected = match a.find_last_inx_ptr() {
        Some(last) => PtrInx::try_into_usize(last.inx()).stack()?.get(),
        None => 0,
    };
    ensure_eq!(a.backing().len(), expected);
    Ok(())
}

// for testing `clone_from_with` and `transfer_canonical_reallocating` which
// interact between multiple arenas, we just hardcode the stack backed arena in
// here
pub fn fuzz_multi_chain_arena<P: Ptr>(
    rng: &mut StarRng,
    stats: MultiStats,
    cd_gen0: &mut CdGen<()>,
    cd_gen1: &mut CdGen<D1>,
) -> Result<(), StackedError> {
    let mut a0 = ChainArena::<P, Cd<()>, StackBacking<128>>::new();
    let mut a1 = ChainArena::<P, Cd<D1>, StackBacking<128>>::new();
    let mut g0 = TestGen(a0.generation());
    let mut g1 = TestGen(a1.generation());
    let mut b0 = CkMap::<(), P>::new();
    let mut b1 = CkMap::<D1, P>::new();
    let mut recaster = DirectArena::<P, P, StackBacking<128>>::new();

    // makes sure there is not some problem with the test harness itself or
    // determinism
    let mut max_len = 0;

    for _ in 0..stats.n {
        fuzz_multi_chain_arena_step(rng, &mut a0, &mut g0, &mut b0, cd_gen0).stack()?;
        fuzz_multi_chain_arena_step(rng, &mut a1, &mut g1, &mut b1, cd_gen1).stack()?;
        max_len = max(max_len, a0.len());
        match rng.index_inclusive(1023) {
            // do no major operations most of the time, rack up some random chain
            // building in the steps above
            0..800 => (),
            800..850 => {
                let len = b1.len();
                let snapshot1 = snapshot(&a1);
                // don't set to just anything, don't want to cause the fuzzer to never hit
                // overflow
                let transfer_generation = PtrGen::generational_inc(a1.generation()).0;
                b0.clear();
                a0.transfer_canonical_reallocating(
                    transfer_generation,
                    &mut a1,
                    |q, o, p| {
                        assert_eq!(o.is_overflow(), g1.invalidate());
                        assert_eq!(*b1.get(o.allow().key()).unwrap(), q);
                        let (k, t) = cd_gen0.new_cd();
                        b0.insert(k, p);
                        t
                    },
                    &mut recaster,
                )
                .unwrap();
                g0.0 = transfer_generation;
                b1.clear();
                ensure!(a1.is_empty());
                ensure_eq!(b0.len(), len);
                check_transfer(&a0, &snapshot1, &recaster, transfer_generation).stack()?;
                ensure_canonical_len(&a0).stack()?;
            }
            850..900 => {
                let len = b0.len();
                let snapshot0 = snapshot(&a0);
                let transfer_generation = PtrGen::generational_inc(a0.generation()).0;
                b1.clear();
                a1.transfer_canonical_reallocating(
                    transfer_generation,
                    &mut a0,
                    |q, o, p| {
                        assert_eq!(o.is_overflow(), g0.invalidate());
                        assert_eq!(*b0.get(o.allow().key()).unwrap(), q);
                        let (k, t) = cd_gen1.new_cd();
                        b1.insert(k, p);
                        t
                    },
                    &mut recaster,
                )
                .unwrap();
                g1.0 = transfer_generation;
                b0.clear();
                ensure!(a0.is_empty());
                ensure_eq!(b1.len(), len);
                check_transfer(&a1, &snapshot0, &recaster, transfer_generation).stack()?;
                ensure_canonical_len(&a1).stack()?;
            }
            900..950 => {
                let snapshot1 = snapshot(&a1);
                b0.clear();
                a0.clone_from_with(&a1, |p, u| {
                    assert_eq!(a1.get(p).unwrap().key(), u.t.key());
                    let (k, t) = cd_gen0.new_cd();
                    b0.insert(k, p);
                    t
                })
                .unwrap();
                for (p, prev_next) in snapshot1 {
                    ensure_eq!(a0.get_link_no_gen(p).stack()?.prev_next(), prev_next);
                }
                ensure_eq!(a0.len(), b1.len());
                ensure_canonical_len(&a0).stack()?;
                g0.0 = a1.singular_generation().stack()?;
            }
            950..1024 => {
                let snapshot0 = snapshot(&a0);
                b1.clear();
                a1.clone_from_with(&a0, |p, u| {
                    assert_eq!(a0.get(p).unwrap().key(), u.t.key());
                    let (k, t) = cd_gen1.new_cd();
                    b1.insert(k, p);
                    t
                })
                .unwrap();
                for (p, prev_next) in snapshot0 {
                    ensure_eq!(a1.get_link_no_gen(p).stack()?.prev_next(), prev_next);
                }
                ensure_eq!(a1.len(), b0.len());
                ensure_canonical_len(&a1).stack()?;
                g1.0 = a0.singular_generation().stack()?;
            }
            1024.. => unreachable!(),
        }
    }
    if let Some(max) = stats.max_len {
        max.assert_debug_eq(&max_len);
    }
    Ok(())
}
