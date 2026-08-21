use std::cmp::{Ordering, max};

use stacked_errors::{StackableErr, StackedError, bail, ensure, ensure_eq};
use star_rng::StarRng;
use triple_arena::{
    Arena, ChainArena, DirectArena, InvalidationOption, InvalidationResult, OrdEntryKind,
    OrdInsertKind, OrdPair, SimpleOrdArena, StackBacking,
    errors::{AllocError, MaxCapacityReductionError, OrdInsertionError, ReallocationError},
    traits::{Advancer, ArenaCloneFromWith, ArenaTrait, ChainArenaTrait, Ptr},
    utils::traits::{ArenaBacking, PtrGen, PtrInx},
};

// similar enough that we can reuse it
pub use crate::basic_arena::Stats;
use crate::{
    TestGen,
    basic_arena::{common_compact_fuzz_step250, gen_invalid},
    cdgen::{Cd, CdGen, Ck},
    misc::{D1, Meta},
};

/// The item type of the fuzzed arenas. `OrdPair` is the recommended item type,
/// the `u8` key is what the ordering is over, and the `Cd` value is what tracks
/// the drops and identifies the entry.
pub type TItem<D> = OrdPair<u8, Cd<D>>;

/// The second domain counterpart of [TItem]
pub type TItem1 = TItem<D1>;

/// The arena that the interarena operations use
pub type A1<P> = SimpleOrdArena<P, TItem1, StackBacking<{ 2 * LIMIT }>>;

/// The length that the fuzz stays around, chosen to be large enough that the
/// WAVL tree reaches several rank levels and that all of the rebalancing and
/// displacement cases show up
pub const LIMIT: usize = 80;

/// Keys are generated in `0..KEY_LIMIT`. This is a little larger than [LIMIT]
/// so that hereditary insertions keep growing the arena often enough to reach
/// the limit, while still being small enough that equal keys and thus the
/// nonhereditary and replacement cases are common.
pub const KEY_LIMIT: u8 = 96;

/// The `Ck` that identifies an entry
fn ck(t: &TItem<()>) -> Ck<()> {
    t.v().key()
}

/// The second domain counterpart of [ck]
fn ck1(t: &TItem1) -> Ck<D1> {
    t.v().key()
}

/// One entry of the reference model
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TEntry<P> {
    /// Uniquely identifies the entry
    pub c: Ck<()>,
    pub p: P,
    pub k: u8,
}

/// The reference model, which is the exact ordering that the arena is supposed
/// to have. Note that because equal keys are allowed this records more than
/// just the sorted key sequence. Everything is positional rather than hashed,
/// so that checking the whole model on every iteration stays cheap even at the
/// lengths this fuzz reaches.
#[derive(Debug)]
pub struct Model<P> {
    order: Vec<TEntry<P>>,
}

impl<P: Ptr> Model<P> {
    fn new() -> Self {
        Self { order: vec![] }
    }

    fn len(&self) -> usize {
        self.order.len()
    }

    fn is_empty(&self) -> bool {
        self.order.is_empty()
    }

    fn at(&self, i: usize) -> TEntry<P> {
        self.order[i]
    }

    fn p_at(&self, i: usize) -> P {
        self.order[i].p
    }

    fn k_at(&self, i: usize) -> u8 {
        self.order[i].k
    }

    fn pos_of_ck(&self, c: Ck<()>) -> Option<usize> {
        self.order.iter().position(|e| e.c == c)
    }

    fn pos_of_inx(&self, inx: P::Inx) -> Option<usize> {
        self.order.iter().position(|e| e.p.inx() == inx)
    }

    /// `lo..hi` are the positions of the entries that already have the key `k`,
    /// and `lo..=hi` are also all the positions that a new entry with the key
    /// `k` could be inserted at while keeping the ordering
    fn bounds(&self, k: u8) -> (usize, usize) {
        let lo = self.order.partition_point(|e| e.k < k);
        let hi = self.order.partition_point(|e| e.k <= k);
        (lo, hi)
    }

    fn insert_at(&mut self, i: usize, c: Ck<()>, p: P, k: u8) {
        self.order.insert(i, TEntry { c, p, k });
    }

    fn remove_at(&mut self, i: usize) -> TEntry<P> {
        self.order.remove(i)
    }

    fn clear(&mut self) {
        self.order.clear();
    }

    /// Also returns the position, which is almost always wanted
    fn get_rand(&self, rng: &mut StarRng) -> Option<(usize, TEntry<P>)> {
        let i = rng.index(self.len())?;
        Some((i, self.order[i]))
    }
}

/// The random entry selection that `common_compact_fuzz_step250` needs
fn get_mut_rand<'a, P: Ptr>(b: &'a mut Model<P>, rng: &mut StarRng) -> Option<(Ck<()>, &'a mut P)> {
    let i = rng.index(b.len())?;
    let e = b.order.get_mut(i)?;
    Some((e.c, &mut e.p))
}

/// Checks that the whole ordering of `a` matches the model. This is a stronger
/// statement than `_check_invariants`, which can only see that the ordering is
/// self consistent and not whether it is the one that the operations should
/// have produced.
pub fn check_model<P: Ptr, B: ArenaBacking>(
    a: &SimpleOrdArena<P, TItem<()>, B>,
    b: &Model<P>,
) -> Result<(), StackedError> {
    ensure_eq!(a.len(), b.len());
    ensure_eq!(a.is_empty(), b.is_empty());
    ensure_eq!(a.first(), b.order.first().map(|e| e.p));
    ensure_eq!(a.last(), b.order.last().map(|e| e.p));
    let mut i = 0usize;
    for (p, t) in a.iter_ordered() {
        let e = *b.order.get(i).stack()?;
        ensure_eq!(p, e.p);
        ensure_eq!(ck(t), e.c);
        ensure_eq!(*t.k(), e.k);
        // the neighboring keys
        let expected_prev = if i == 0 {
            None
        } else {
            Some(b.p_at(i.wrapping_sub(1)).inx())
        };
        let expected_next = if i.wrapping_add(1) == b.len() {
            None
        } else {
            Some(b.p_at(i.wrapping_add(1)).inx())
        };
        let (generation, link) = a.get_inx_link_no_gen(p.inx()).stack()?;
        ensure_eq!(generation, p.generation());
        ensure_eq!(link.prev_next(), (expected_prev, expected_next));
        ensure_eq!(ck(link.t), e.c);
        // the same thing through the whole internal node
        let (generation, node) = a.get_inx_node(p.inx()).stack()?;
        ensure_eq!(generation, p.generation());
        ensure_eq!(node.prev_next(), (expected_prev, expected_next));
        ensure_eq!(ck(&node.t.t), e.c);
        i = i.checked_add(1).stack()?;
    }
    ensure_eq!(i, b.len());
    Ok(())
}

/// After any of the canonicalizing operations, the entries are at the indexes
/// `1..=len` in key order, and the internal slot length is trimmed to exactly
/// the last index, see REF(exponential_double_buffer_blowup).
fn check_canonical_layout<P: Ptr, D: Copy + Default, B: ArenaBacking>(
    a: &SimpleOrdArena<P, TItem<D>, B>,
) -> Result<(), StackedError> {
    let mut i = 0usize;
    for (p, _) in a.iter_ordered() {
        i = i.checked_add(1).stack()?;
        ensure_eq!(PtrInx::try_into_usize(p.inx()).stack()?.get(), i);
    }
    ensure_eq!(i, a.len());
    match a.find_last_inx_ptr() {
        Some(last) => ensure_eq!(PtrInx::try_into_usize(last.inx()).stack()?.get(), a.len()),
        None => ensure!(a.is_empty()),
    }
    Ok(())
}

/// Checks the `find_*` functions against the model with a random key
fn check_finds<P: Ptr, B: ArenaBacking>(
    rng: &mut StarRng,
    a: &SimpleOrdArena<P, TItem<()>, B>,
    b: &Model<P>,
) -> Result<(), StackedError> {
    let k = rng.index(KEY_LIMIT as usize).unwrap() as u8;
    let (lo, hi) = b.bounds(k);
    // an equal key exists iff the range of equal keys is nonempty
    let exists = lo < hi;

    // `find_key` finds one of the equal keys if there are any
    match a.find_key(&k) {
        Some(p) => {
            ensure!(exists);
            ensure_eq!(*a.get(p).stack()?.k(), k);
            let i = b.pos_of_inx(p.inx()).stack()?;
            ensure!((lo <= i) && (i < hi));
        }
        None => ensure!(!exists),
    }

    // `find_similar_key` returns `Equal` iff an equal key exists, and otherwise
    // returns the unique legal insertion point
    match a.find_similar_key(&k) {
        Some((p, Ordering::Equal)) => {
            ensure!(exists);
            ensure_eq!(*a.get(p).stack()?.k(), k);
        }
        Some((p, Ordering::Less)) => {
            ensure!(!exists);
            // `k` would be inserted immediately before `p`
            ensure_eq!(b.pos_of_inx(p.inx()).stack()?, lo);
        }
        Some((p, Ordering::Greater)) => {
            ensure!(!exists);
            // `k` would be inserted immediately after `p`
            ensure_eq!(b.pos_of_inx(p.inx()).stack()?.checked_add(1).stack()?, lo);
        }
        None => ensure!(b.is_empty()),
    }

    // the linear versions have to agree on everything except which of a group of
    // equal keys they land on
    let num = rng.index_inclusive(4);
    let p_init = if let Some((_, e)) = b.get_rand(rng)
        && rng.next_bool()
    {
        e.p
    } else {
        gen_invalid(rng, a)
    };
    match a.find_key_linear(p_init, num, &k) {
        Some(p) => {
            ensure!(exists);
            ensure_eq!(*a.get(p).stack()?.k(), k);
            let i = b.pos_of_inx(p.inx()).stack()?;
            ensure!((lo <= i) && (i < hi));
        }
        None => ensure!(!exists),
    }
    match a.find_similar_key_linear(p_init.inx(), num, &k) {
        Some((p, Ordering::Equal)) => {
            ensure!(exists);
            ensure_eq!(*a.get(p).stack()?.k(), k);
        }
        Some((p, Ordering::Less)) => {
            ensure!(!exists);
            ensure_eq!(b.pos_of_inx(p.inx()).stack()?, lo);
        }
        Some((p, Ordering::Greater)) => {
            ensure!(!exists);
            ensure_eq!(b.pos_of_inx(p.inx()).stack()?.checked_add(1).stack()?, lo);
        }
        None => ensure!(b.is_empty()),
    }
    Ok(())
}

/// Checks `find_with` and `find_similar_with`
fn check_find_withs<P: Ptr, B: ArenaBacking>(
    rng: &mut StarRng,
    a: &SimpleOrdArena<P, TItem<()>, B>,
    b: &Model<P>,
) -> Result<(), StackedError> {
    match rng.index_inclusive(2) {
        0 => {
            // replicate the `find_key` behavior
            let k = rng.index(KEY_LIMIT as usize).unwrap() as u8;
            let (lo, hi) = b.bounds(k);
            let mut visited = 0usize;
            let res = a.find_with(|_, t| {
                visited = visited.wrapping_add(1);
                k.cmp(t.k())
            });
            match res {
                Some(p) => {
                    ensure!(lo < hi);
                    ensure_eq!(*a.get(p).stack()?.k(), k);
                }
                None => ensure_eq!(lo, hi),
            }
            // the binary search cannot take more steps than there are entries
            ensure!(visited <= b.len());
            let res = a.find_similar_with(|_, t| k.cmp(t.k()));
            match res {
                Some((p, Ordering::Equal)) => {
                    ensure!(lo < hi);
                    ensure_eq!(*a.get(p).stack()?.k(), k);
                }
                Some((p, Ordering::Less)) => {
                    ensure_eq!(lo, hi);
                    ensure_eq!(b.pos_of_inx(p.inx()).stack()?, lo);
                }
                Some((p, Ordering::Greater)) => {
                    ensure_eq!(lo, hi);
                    ensure_eq!(b.pos_of_inx(p.inx()).stack()?.checked_add(1).stack()?, lo);
                }
                None => ensure!(b.is_empty()),
            }
        }
        1 => {
            // always descending subtree 0 ends up at the least entry, which is
            // `first` because the in-order traversal is the key order
            ensure!(a.find_with(|_, _| Ordering::Less).is_none());
            ensure_eq!(
                a.find_similar_with(|_, _| Ordering::Less),
                a.first().map(|p| (p, Ordering::Less))
            );
        }
        2 => {
            ensure!(a.find_with(|_, _| Ordering::Greater).is_none());
            ensure_eq!(
                a.find_similar_with(|_, _| Ordering::Greater),
                a.last().map(|p| (p, Ordering::Greater))
            );
        }
        _ => unreachable!(),
    }
    Ok(())
}

/// What the model says an insertion should do
#[derive(Debug, Clone, Copy)]
enum Expect {
    /// The requirements of the kind are not met
    Fail,
    /// A new entry is inserted at some position in `lo..=hi`
    New { lo: usize, hi: usize },
    /// The entry at some position in `lo..hi` is replaced, and no capacity is
    /// used
    Replace { lo: usize, hi: usize },
}

/// An [OrdInsertKind] without the key borrow, which has to be rebuilt against a
/// local `u8`
#[derive(Debug, Clone, Copy)]
enum Kind<P: Ptr> {
    Empty,
    Normal,
    Nonhereditary,
    Linear {
        p_init: P::Inx,
        num: usize,
    },
    NonhereditaryLinear {
        p_init: P::Inx,
        num: usize,
    },
    Manual {
        p_target: P::Inx,
        direction: Ordering,
    },
}

impl<P: Ptr> Kind<P> {
    fn with_key(self, k: &u8) -> OrdInsertKind<P, &u8> {
        match self {
            Kind::Empty => OrdInsertKind::Empty,
            Kind::Normal => OrdInsertKind::Normal(k),
            Kind::Nonhereditary => OrdInsertKind::Nonhereditary(k),
            Kind::Linear { p_init, num } => OrdInsertKind::Linear { p_init, num, k },
            Kind::NonhereditaryLinear { p_init, num } => {
                OrdInsertKind::NonhereditaryLinear { p_init, num, k }
            }
            Kind::Manual {
                p_target,
                direction,
            } => OrdInsertKind::Manual {
                p_target,
                direction,
            },
        }
    }
}

/// Picks a random key and [Kind], biased towards ones that will succeed but
/// regularly producing unmet requirements and invalid `Ptr`s as well. The
/// `Manual` cases pick the key to fit the position they target so that the
/// ordering is not deliberately broken.
fn rand_kind<P: Ptr, B: ArenaBacking>(
    rng: &mut StarRng,
    a: &SimpleOrdArena<P, TItem<()>, B>,
    b: &Model<P>,
) -> (u8, Kind<P>, Expect) {
    // a random existing index, or an invalid one some of the time so that the
    // fallback and failure paths get reached
    let rand_inx = |rng: &mut StarRng| -> P::Inx {
        if let Some((_, e)) = b.get_rand(rng)
            && (rng.index_inclusive(7) != 0)
        {
            e.p.inx()
        } else {
            gen_invalid(rng, a).inx()
        }
    };
    let rand_key = |rng: &mut StarRng| -> u8 { rng.index(KEY_LIMIT as usize).unwrap() as u8 };
    // the ordinary key based kinds all reduce to one of these two expectations
    let hereditary = |b: &Model<P>, k: u8| -> Expect {
        let (lo, hi) = b.bounds(k);
        if lo < hi {
            Expect::Replace { lo, hi }
        } else {
            Expect::New { lo, hi }
        }
    };
    let nonhereditary = |b: &Model<P>, k: u8| -> Expect {
        let (lo, hi) = b.bounds(k);
        Expect::New { lo, hi }
    };
    match rng.index_inclusive(5) {
        0 => {
            let k = rand_key(rng);
            let expect = if b.is_empty() {
                Expect::New { lo: 0, hi: 0 }
            } else {
                Expect::Fail
            };
            (k, Kind::Empty, expect)
        }
        1 => {
            let k = rand_key(rng);
            (k, Kind::Normal, hereditary(b, k))
        }
        2 => {
            let k = rand_key(rng);
            (k, Kind::Nonhereditary, nonhereditary(b, k))
        }
        3 => {
            let k = rand_key(rng);
            let kind = Kind::Linear {
                p_init: rand_inx(rng),
                num: rng.index_inclusive(4),
            };
            (k, kind, hereditary(b, k))
        }
        4 => {
            let k = rand_key(rng);
            let kind = Kind::NonhereditaryLinear {
                p_init: rand_inx(rng),
                num: rng.index_inclusive(4),
            };
            (k, kind, nonhereditary(b, k))
        }
        5 => {
            let direction = rand_direction(rng);
            // a valid target most of the time so that the deterministic positions
            // get reached, and the empty arena always ends up failing. Note that
            // the manual kind resolves the target without a generation check, so
            // this has to go by whether the slot is allocated at all.
            let p_target = if let Some((_, e)) = b.get_rand(rng)
                && (rng.index_inclusive(7) != 0)
            {
                e.p.inx()
            } else {
                gen_invalid(rng, a).inx()
            };
            match b.pos_of_inx(p_target) {
                Some(i) => manual_at(rng, b, p_target, i, direction),
                None => (
                    rand_key(rng),
                    Kind::Manual {
                        p_target,
                        direction,
                    },
                    Expect::Fail,
                ),
            }
        }
        _ => unreachable!(),
    }
}

fn rand_direction(rng: &mut StarRng) -> Ordering {
    match rng.index_inclusive(2) {
        0 => Ordering::Less,
        1 => Ordering::Equal,
        2 => Ordering::Greater,
        _ => unreachable!(),
    }
}

/// The manual kind accepts whatever `direction` says without enforcing the
/// ordering, so this picks a key that fits the position that is being targeted.
/// `i` must be the position of the entry at the valid `p_target`.
fn manual_at<P: Ptr>(
    rng: &mut StarRng,
    b: &Model<P>,
    p_target: P::Inx,
    i: usize,
    direction: Ordering,
) -> (u8, Kind<P>, Expect) {
    // the position that the new entry ends up at, and the positions of the
    // neighbors that the key has to fit between
    let (pos, upper_pos) = match direction {
        // inserted immediately before `i`
        Ordering::Less => (i, i),
        // the entry at `i` is replaced
        Ordering::Equal => (i, i.wrapping_add(1)),
        // inserted immediately after `i`
        Ordering::Greater => (i.wrapping_add(1), i.wrapping_add(1)),
    };
    let lower = if pos == 0 {
        0
    } else {
        b.k_at(pos.wrapping_sub(1))
    };
    let upper = if upper_pos >= b.len() {
        KEY_LIMIT.wrapping_sub(1)
    } else {
        b.k_at(upper_pos)
    };
    let k = if lower >= upper {
        lower
    } else {
        lower.wrapping_add(rng.index_inclusive(usize::from(upper.wrapping_sub(lower))) as u8)
    };
    let expect = if direction.is_eq() {
        Expect::Replace {
            lo: pos,
            hi: pos.wrapping_add(1),
        }
    } else {
        Expect::New { lo: pos, hi: pos }
    };
    (
        k,
        Kind::Manual {
            p_target,
            direction,
        },
        expect,
    )
}

/// Which of the parallel insertion functions to use
#[derive(Clone, Copy, PartialEq, Eq)]
enum How {
    /// `insert_within_capacity`, which is always `Normal`
    WithinCapacity,
    /// `insert_reallocating`, which is always `Normal`
    Reallocating,
    /// `insert`, which is always `Normal`
    Panicking,
    EntryWithinCapacity,
    EntryReallocating,
    EntryPanicking,
    /// An entry that is dropped instead of inserted into
    Cancel,
    /// `insert_inx_manual_unwrap`, which is always a valid `Manual`
    ManualUnwrap,
}

impl How {
    fn is_panicking(self) -> bool {
        matches!(
            self,
            How::Panicking | How::EntryPanicking | How::ManualUnwrap
        )
    }

    fn is_reallocating(self) -> bool {
        matches!(
            self,
            How::Reallocating
                | How::EntryReallocating
                | How::Panicking
                | How::EntryPanicking
                | How::ManualUnwrap
        )
    }

    /// The functions that do not take a `OrdInsertKind`
    fn is_forced_normal(self) -> bool {
        matches!(
            self,
            How::WithinCapacity | How::Reallocating | How::Panicking
        )
    }
}

/// Attempts an insertion, determining the expected outcome from the model
/// beforehand and recording a successful insertion in `b`
fn try_ord_insert<P: Ptr, B: ArenaBacking>(
    a: &mut SimpleOrdArena<P, TItem<()>, B>,
    b: &mut Model<P>,
    cd_gen: &mut CdGen<()>,
    g: &TestGen<P>,
    key: u8,
    kind: Kind<P>,
    expect: Expect,
    how: How,
    test_limit: usize,
) -> Result<(), StackedError> {
    let len = a.len();
    let cap = a.capacity();
    let insert_kind = kind.with_key(&key);
    let max_reached = a
        .max_capacity()
        .is_some_and(|max_capacity| max_capacity == len);
    // replacements never need a slot
    let needs_capacity = matches!(expect, Expect::New { .. });
    let capacity_err = if !needs_capacity || (len < cap) {
        None
    } else if !how.is_reallocating() {
        Some(OrdInsertionError::NotWithinCapacity)
    } else if max_reached {
        Some(OrdInsertionError::BeyondMaxCapacity)
    } else {
        None
    };
    if how.is_panicking() && capacity_err.is_some() {
        // these would panic, and the parallel fallible functions already cover the
        // error paths
        return Ok(());
    }
    if matches!(expect, Expect::Fail) {
        if how.is_forced_normal() || (how == How::ManualUnwrap) {
            // these cannot reach a failed requirement
            return Ok(());
        }
        // the ordering requirement is checked before any capacity is used, so it
        // takes priority over what the capacity is doing
        let res = match how {
            How::EntryWithinCapacity | How::EntryPanicking | How::Cancel => {
                a.entry_insert_within_capacity(insert_kind).map(|_| ())
            }
            How::EntryReallocating => a.entry_insert_reallocating(insert_kind).map(|_| ()),
            _ => unreachable!(),
        };
        ensure_eq!(res, Err(OrdInsertionError::FailedOrdRequirement));
        ensure_eq!(a.len(), len);
        ensure_eq!(a.capacity(), cap);
        return Ok(());
    }
    if let Some(capacity_err) = capacity_err {
        let (_, t) = cd_gen.new_cd();
        let res = match how {
            How::WithinCapacity => a.insert_within_capacity(OrdPair::new(key, t)).map(|_| ()),
            How::Reallocating => a.insert_reallocating(OrdPair::new(key, t)).map(|_| ()),
            How::EntryWithinCapacity | How::Cancel => {
                a.entry_insert_within_capacity(insert_kind).map(|_| ())
            }
            How::EntryReallocating => a.entry_insert_reallocating(insert_kind).map(|_| ()),
            How::Panicking | How::EntryPanicking | How::ManualUnwrap => unreachable!(),
        };
        ensure_eq!(res, Err(capacity_err));
        ensure_eq!(a.len(), len);
        ensure_eq!(a.capacity(), cap);
        return Ok(());
    }
    if needs_capacity && (len == cap) && (len >= test_limit) {
        // stay around the limit instead of growing without bound
        return Ok(());
    }
    // the `Ptr` of the entry that a replacement is going to overwrite
    let replaced_range = match expect {
        Expect::Replace { lo, hi } => Some((lo, hi)),
        _ => None,
    };
    let (k, t) = cd_gen.new_cd();
    let item = OrdPair::new(key, t);
    let (p, old) = match how {
        How::WithinCapacity => a.insert_within_capacity(item).ok().stack()?,
        How::Reallocating => a.insert_reallocating(item).ok().stack()?,
        How::Panicking => a.insert(item),
        How::EntryWithinCapacity | How::EntryReallocating | How::EntryPanicking => {
            let entry = match how {
                How::EntryWithinCapacity => {
                    let Ok(entry) = a.entry_insert_within_capacity(insert_kind) else {
                        bail!("expected capacity to be available")
                    };
                    entry
                }
                How::EntryReallocating => {
                    let Ok(entry) = a.entry_insert_reallocating(insert_kind) else {
                        bail!("expected the capacity to be able to grow")
                    };
                    entry
                }
                _ => a.entry_insert(insert_kind),
            };
            // the elaborated `Ptr` says whether a replacement is going to happen.
            // Note that `entry` holds the arena, so this can only be checked
            // against the model.
            let elaborated = entry.ptr();
            match (elaborated, replaced_range) {
                (OrdEntryKind::Replacing(p), Some((lo, hi))) => {
                    // it has to be one of the entries that has the equal key
                    ensure!(b.order[lo..hi].iter().any(|e| e.p == p));
                }
                (OrdEntryKind::New(p), None) => {
                    // a fresh slot of the current generation
                    ensure!(b.pos_of_inx(p.inx()).is_none());
                    ensure_eq!(p.generation(), g.0);
                }
                _ => bail!("`ptr` disagreed with the expected replacement"),
            }
            let p = elaborated.any();
            (p, entry.insert(item))
        }
        How::Cancel => {
            let Ok(entry) = a.entry_insert_within_capacity(insert_kind) else {
                bail!("expected capacity to be available")
            };
            let p = entry.ptr();
            // REF(insertion_idempotency) note that there is nothing to undo, the
            // entry only carries the prepared insertion point
            let _ = entry;
            drop(item);
            match p {
                OrdEntryKind::New(p) => ensure!(!a.contains(p)),
                // the entry that would have been replaced is untouched
                OrdEntryKind::Replacing(p) => ensure!(a.contains(p)),
            }
            ensure_eq!(a.len(), len);
            ensure_eq!(a.capacity(), cap);
            // and nothing was moved around
            check_model(a, b).stack()?;
            return Ok(());
        }
        How::ManualUnwrap => {
            let Kind::Manual {
                p_target,
                direction,
            } = kind
            else {
                unreachable!()
            };
            let old = a.insert_inx_manual_unwrap(p_target, direction, item);
            // the new entry is the one that the model does not have yet
            let p = if old.is_some() {
                Ptr::_from_raw(p_target, a.get_inx(p_target).stack()?.0)
            } else {
                let mut found = None;
                for (p, t) in a.iter() {
                    if ck(t) == k {
                        found = Some(p);
                        break;
                    }
                }
                found.stack()?
            };
            (p, old)
        }
    };
    ensure_eq!(*a.get(p).stack()?.k(), key);
    ensure_eq!(ck(a.get(p).stack()?), k);
    if let Some((lo, hi)) = replaced_range {
        // a replacement keeps the same slot and generation, and does not change the
        // length or capacity
        let old = old.stack()?;
        let old_c = ck(&old);
        let i = b.pos_of_ck(old_c).stack()?;
        ensure!((lo <= i) && (i < hi));
        // a replacement keeps the same slot and generation
        ensure_eq!(b.p_at(i), p);
        ensure_eq!(a.len(), len);
        ensure_eq!(a.capacity(), cap);
        drop(old);
        b.remove_at(i);
        b.insert_at(i, k, p, key);
    } else {
        let Expect::New { lo, hi } = expect else {
            unreachable!()
        };
        ensure!(old.is_none());
        ensure_eq!(p.generation(), g.0);
        ensure_eq!(a.len(), len.checked_add(1).stack()?);
        if how.is_reallocating() && (len == cap) {
            ensure!(a.capacity() > cap);
        } else {
            ensure_eq!(a.capacity(), cap);
        }
        // find where it actually landed, and check that it is a legal position
        let i = match a.get_inx_link_no_gen(p.inx()).stack()?.1.prev() {
            Some(prev) => b.pos_of_inx(prev).stack()?.checked_add(1).stack()?,
            None => 0,
        };
        ensure!((lo <= i) && (i <= hi));
        b.insert_at(i, k, p, key);
    }
    Ok(())
}

/// Rebuilds the `p` fields of the model from `a`, which is what the operations
/// that move entries around without being able to report the new `Ptr`s need.
/// The ordering in the model is left alone so that `check_model` still verifies
/// it.
fn refresh_model_ptrs<P: Ptr, B: ArenaBacking>(
    a: &SimpleOrdArena<P, TItem<()>, B>,
    b: &mut Model<P>,
) -> Result<(), StackedError> {
    let mut i = 0usize;
    for (p, t) in a.iter_ordered() {
        let e = b.order.get_mut(i).stack()?;
        // going in order also checks that the ordering survived
        ensure_eq!(e.c, ck(t));
        e.p = p;
        i = i.checked_add(1).stack()?;
    }
    ensure_eq!(i, b.len());
    Ok(())
}

/// Rebuilds the whole model from `a`. This is only used where the ordering has
/// already been checked against what it was before the operation.
fn rebuild_model<P: Ptr, B: ArenaBacking>(a: &SimpleOrdArena<P, TItem<()>, B>, b: &mut Model<P>) {
    b.clear();
    for (p, t) in a.iter_ordered() {
        let i = b.len();
        b.insert_at(i, ck(t), p, *t.k());
    }
}

/// The key sequence of an ordered arena, which the interarena operations have
/// to preserve
fn key_sequence<P: Ptr, D: Copy + Default, B: ArenaBacking>(
    a: &SimpleOrdArena<P, TItem<D>, B>,
) -> Vec<u8> {
    a.iter_ordered().map(|(_, t)| *t.k()).collect()
}

/// Transfers everything from `a` into `a1` and then straight back, which
/// verifies both directions and that the ordering survives a round trip without
/// disturbing the length that the fuzz is sitting at
#[allow(clippy::too_many_arguments)]
fn transfer_round_trip<P: Ptr, B: ArenaBacking>(
    a: &mut SimpleOrdArena<P, TItem<()>, B>,
    a1: &mut A1<P>,
    b: &mut Model<P>,
    g: &mut TestGen<P>,
    g1: &mut TestGen<P>,
    cd_gen: &mut CdGen<()>,
    cd_gen1: &mut CdGen<D1>,
    recaster: &mut DirectArena<P, P, StackBacking<{ 2 * LIMIT }>>,
) -> Result<(), StackedError> {
    let len = a.len();
    let keys = key_sequence(a);
    let expected: Vec<TEntry<P>> = b.order.clone();

    // do something that is not setting to a low constant, so that generation
    // overflow is reached
    let next_gen = PtrGen::generational_inc(g1.0).0;
    let mut fwd: Vec<Ck<D1>> = vec![];
    recaster.clone_from_with(a, |_, _| P::invalid()).unwrap();
    a1.transfer_canonical_reallocating(next_gen, a, |q, o, p| {
        recaster[q] = p;
        let i = fwd.len();
        assert_eq!(o.is_overflow(), g.invalidate());
        let u = o.allow();
        // `map` is called in key order, and the destination indexes are assigned
        // in order
        assert_eq!(ck(&u), expected[i].c);
        assert_eq!(q, expected[i].p);
        assert_eq!(PtrInx::try_into_usize(p.inx()).unwrap().get(), i + 1);
        assert_eq!(p.generation(), next_gen);
        let (c1, t1) = cd_gen1.new_cd();
        fwd.push(c1);
        OrdPair::new(*u.k(), t1)
    })
    .stack()?;
    ensure!(a.is_empty());
    ensure_eq!(fwd.len(), len);
    ensure_eq!(a1.len(), len);
    g1.0 = next_gen;
    ensure_eq!(key_sequence(a1), keys);
    check_canonical_layout(a1).stack()?;
    // the recaster is the complete mapping of where everything went
    for (i, e) in expected.iter().enumerate() {
        let p = *recaster.get(e.p).stack()?;
        ensure_eq!(PtrInx::try_into_usize(p.inx()).stack()?.get(), i + 1);
    }
    // and the ordering is exactly the one that arrived
    for (i, (_, t)) in a1.iter_ordered().enumerate() {
        ensure_eq!(ck1(t), fwd[i]);
    }

    let next_gen = PtrGen::generational_inc(g.0).0;
    let mut back: Vec<Ck<()>> = vec![];
    a.transfer_canonical_reallocating(next_gen, a1, |_, o, p| {
        let i = back.len();
        assert_eq!(o.is_overflow(), g1.invalidate());
        let u = o.allow();
        assert_eq!(ck1(&u), fwd[i]);
        assert_eq!(PtrInx::try_into_usize(p.inx()).unwrap().get(), i + 1);
        let (c, t) = cd_gen.new_cd();
        back.push(c);
        OrdPair::new(*u.k(), t)
    })
    .stack()?;
    ensure!(a1.is_empty());
    ensure_eq!(back.len(), len);
    ensure_eq!(a.len(), len);
    g.0 = next_gen;
    ensure_eq!(key_sequence(a), keys);
    check_canonical_layout(a).stack()?;
    rebuild_model(a, b);
    // the round trip put every entry back at the position it started at
    for (i, c) in back.iter().enumerate() {
        ensure_eq!(b.at(i).c, *c);
    }
    Ok(())
}

pub fn fuzz<P: Ptr, B: ArenaBacking>(
    meta: &mut Meta<Stats>,
    a: &mut SimpleOrdArena<P, TItem<()>, B>,
    mut check_invariants: impl FnMut(&SimpleOrdArena<P, TItem<()>, B>) -> Result<(), StackedError>,
    // set iff `SetMaxCapacity` is implemented
    set_max_capacity: Option<
        fn(&mut SimpleOrdArena<P, TItem<()>, B>, usize) -> Result<(), MaxCapacityReductionError>,
    >,
) -> Result<(), StackedError> {
    let rng = &mut meta.rng;
    let stats = meta.stats.as_mut().stack()?;
    let cd_gen = &mut stats.cd_gen;
    let cd_gen1 = &mut stats.cd_gen1;

    let mut b = Model::<P>::new();
    let mut b_capacity = a.capacity();
    let mut g = TestGen::<P>(a.generation());

    // set and used by the interarena sections
    let mut a1 = A1::<P>::new();
    let mut g1 = TestGen::<P>(a1.generation());
    let mut recaster = DirectArena::<P, P, StackBacking<{ 2 * LIMIT }>>::new();
    let mut chain_arena = ChainArena::<P, Cd<D1>, StackBacking<{ 2 * LIMIT }>>::new();
    let mut arena = Arena::<P, Cd<D1>, StackBacking<{ 2 * LIMIT }>>::new();

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
        ensure_eq!(a.singular_generation().stack()?, g.0);
        ensure_eq!(a.generation(), g.0);
        check_invariants(a).stack()?;
        check_model(a, &b).stack()?;

        meta.i = i;
        meta.op_inx = rng.index_inclusive(1023);
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
                get_mut_rand,
                ck,
            )
            .stack()?,
            250..700 => {
                // all of the insertion functions with all of the kinds
                let (key, kind, expect) = rand_kind(rng, a, &b);
                let how = match rng.index_inclusive(5) {
                    0 => How::WithinCapacity,
                    1 => How::Reallocating,
                    2 => How::Panicking,
                    3 => How::EntryWithinCapacity,
                    4 => How::EntryReallocating,
                    5 => How::EntryPanicking,
                    _ => unreachable!(),
                };
                // the non-entry functions are always `Normal`
                let (kind, expect) = if how.is_forced_normal() {
                    let (lo, hi) = b.bounds(key);
                    let expect = if lo < hi {
                        Expect::Replace { lo, hi }
                    } else {
                        Expect::New { lo, hi }
                    };
                    (Kind::Normal, expect)
                } else {
                    (kind, expect)
                };
                try_ord_insert(
                    a,
                    &mut b,
                    cd_gen,
                    &g,
                    key,
                    kind,
                    expect,
                    how,
                    stats.test_limit,
                )
                .stack()?;
                b_capacity = a.capacity();
            }
            700..725 => {
                // insertion with cancellation
                let (key, kind, expect) = rand_kind(rng, a, &b);
                try_ord_insert(
                    a,
                    &mut b,
                    cd_gen,
                    &g,
                    key,
                    kind,
                    expect,
                    How::Cancel,
                    stats.test_limit,
                )
                .stack()?;
            }
            725..765 => {
                // `insert_inx_manual_unwrap`, which is only ever given a valid target
                let Some((i, e)) = b.get_rand(rng) else {
                    // nothing to target
                    continue;
                };
                let direction = rand_direction(rng);
                let (key, kind, expect) = manual_at(rng, &b, e.p.inx(), i, direction);
                try_ord_insert(
                    a,
                    &mut b,
                    cd_gen,
                    &g,
                    key,
                    kind,
                    expect,
                    How::ManualUnwrap,
                    stats.test_limit,
                )
                .stack()?;
                b_capacity = a.capacity();
            }
            765..865 => {
                // remove and remove_inx
                if let Some((i, e)) = b.get_rand(rng) {
                    let p = e.p;
                    if rng.next_bool() {
                        match a.remove(p) {
                            InvalidationResult::Success(u) => {
                                ensure_eq!(ck(&u), e.c);
                                ensure!(!g.invalidate());
                            }
                            InvalidationResult::GenerationOverflow(u) => {
                                ensure_eq!(ck(&u), e.c);
                                ensure!(g.invalidate());
                            }
                            InvalidationResult::InvalidPtr => bail!(),
                        }
                    } else {
                        match a.remove_inx(p.inx()) {
                            InvalidationResult::Success((generation, u)) => {
                                ensure_eq!(generation, p.generation());
                                ensure_eq!(ck(&u), e.c);
                                ensure!(!g.invalidate());
                            }
                            InvalidationResult::GenerationOverflow((generation, u)) => {
                                ensure_eq!(generation, p.generation());
                                ensure_eq!(ck(&u), e.c);
                                ensure!(g.invalidate());
                            }
                            InvalidationResult::InvalidPtr => bail!(),
                        }
                    }
                    b.remove_at(i);
                } else {
                    let invalid = gen_invalid(rng, a);
                    ensure!(matches!(a.remove(invalid), InvalidationResult::InvalidPtr));
                    ensure!(matches!(
                        a.remove_inx(invalid.inx()),
                        InvalidationResult::InvalidPtr
                    ));
                }
            }
            865..885 => {
                // removes with invalid `Ptr`s
                let invalid = gen_invalid(rng, a);
                ensure!(matches!(a.remove(invalid), InvalidationResult::InvalidPtr));
                if a.get_inx(invalid.inx()).is_none() {
                    ensure!(matches!(
                        a.remove_inx(invalid.inx()),
                        InvalidationResult::InvalidPtr
                    ));
                }
                // the index based lookups do not check the generation, so they
                // succeed iff the slot happens to be allocated
                ensure_eq!(
                    a.get_inx_link_no_gen(invalid.inx()).is_none(),
                    a.get_inx(invalid.inx()).is_none()
                );
                ensure_eq!(
                    a.get_inx_node(invalid.inx()).is_none(),
                    a.get_inx(invalid.inx()).is_none()
                );
            }
            885..925 => check_finds(rng, a, &b).stack()?,
            925..950 => check_find_withs(rng, a, &b).stack()?,
            950..975 => {
                // advancer_ordered and iter_ordered
                if let Some((mut i, e)) = b.get_rand(rng) {
                    let rev = rng.next_bool();
                    let mut adv = a.advancer_ordered(e.p, rev).stack()?;
                    loop {
                        let p = adv.advance(a).stack()?;
                        ensure_eq!(p, b.p_at(i));
                        if rev {
                            if i == 0 {
                                ensure!(adv.advance(a).is_none());
                                break;
                            }
                            i = i.wrapping_sub(1);
                        } else {
                            i = i.wrapping_add(1);
                            if i == b.len() {
                                ensure!(adv.advance(a).is_none());
                                break;
                            }
                        }
                    }
                } else {
                    let invalid = gen_invalid(rng, a);
                    ensure!(a.advancer_ordered(invalid, rng.next_bool()).is_none());
                }
                // the `IntoIterator` impl for a reference
                let mut i = 0usize;
                for (p, t) in &*a {
                    ensure_eq!(p, b.p_at(i));
                    ensure_eq!(ck(t), b.at(i).c);
                    i = i.wrapping_add(1);
                }
                ensure_eq!(i, b.len());
                // The unordered iteration covers exactly the same entries. This
                // is only checked here and not in `check_model`, because looking
                // an unordered entry up in the model is `O(n)`.
                let mut n = 0usize;
                for (p, t) in a.iter() {
                    let i = b.pos_of_ck(ck(t)).stack()?;
                    ensure_eq!(b.p_at(i), p);
                    ensure_eq!(b.k_at(i), *t.k());
                    n = n.wrapping_add(1);
                }
                ensure_eq!(n, b.len());
            }
            975..983 => {
                // `IndexMut` and the `Debug` impl
                if let Some((_, e)) = b.get_rand(rng) {
                    ensure_eq!(ck(&a[e.p]), e.c);
                    ensure_eq!(ck(&a[&e.p]), e.c);
                    let _ = a[e.p].v_mut();
                }
                // this is ordered, unlike the unordered arena `Debug` impls
                let s = format!("{a:?}");
                ensure_eq!(s.matches("Cd(").count(), b.len());
            }
            983..991 => {
                // set_generation and inc_generation, which only advance the
                // counter for future insertions and leave the existing entries
                // and their `Ptr`s alone
                if rng.next_bool() {
                    let new_gen = PtrGen::generational_inc(g.0).0;
                    a.set_generation(new_gen);
                    // this loses whether it overflowed
                    g.invalidate();
                    ensure_eq!(a.generation(), new_gen);
                } else {
                    ensure_eq!(a.inc_generation().is_overflow(), g.invalidate());
                }
            }
            991..1003 => {
                // compress and compress_with
                let reset = rng.next_bool();
                if rng.next_bool() {
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
                } else {
                    let mut new_map = vec![];
                    let mut res = Ok(());
                    let o = a
                        .compress_with(reset, |p_old, t, p_new| {
                            if b.pos_of_inx(p_old.inx()).map(|i| b.at(i))
                                != Some(TEntry {
                                    c: ck(t),
                                    p: p_old,
                                    k: *t.k(),
                                })
                            {
                                res = Err(());
                            }
                            new_map.push((p_new, ck(t)));
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
                    for (p, c) in new_map {
                        let i = b.pos_of_ck(c).stack()?;
                        b.order.get_mut(i).stack()?.p = p;
                    }
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
            1003..1011 => {
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
                let keys = key_sequence(a);
                refresh_model_ptrs(a, &mut b).stack()?;
                check_canonical_layout(a).stack()?;
                // the ordering is preserved, which combined with `check_model` at the
                // top of the loop means the entries did not get shuffled
                ensure_eq!(keys.len(), len);
            }
            1011..1017 => {
                // clone_to_chain_arena and clone_to_arena
                if rng.next_bool() {
                    let mut i = 0usize;
                    a.clone_to_chain_arena(&mut chain_arena, |p, t| {
                        assert_eq!(ck(a.get(p).unwrap()), ck(t));
                        i += 1;
                        cd_gen1.new_cd().1
                    })
                    .stack()?;
                    ensure_eq!(i, len);
                    ensure_eq!(chain_arena.len(), len);
                    // the `Ptr`s and the ordering became the chain
                    for i in 0..len {
                        let p = b.p_at(i);
                        let link = chain_arena.get_link_no_gen(p).stack()?;
                        let expected_prev = if i == 0 {
                            None
                        } else {
                            Some(b.p_at(i.wrapping_sub(1)).inx())
                        };
                        let expected_next = if i.wrapping_add(1) == len {
                            None
                        } else {
                            Some(b.p_at(i.wrapping_add(1)).inx())
                        };
                        ensure_eq!(link.prev_next(), (expected_prev, expected_next));
                    }
                    chain_arena.clear().allow();
                } else {
                    let mut i = 0usize;
                    a.clone_to_arena(&mut arena, |p, link| {
                        let t = &link.t.t;
                        assert_eq!(ck(a.get(p).unwrap()), ck(t));
                        i += 1;
                        cd_gen1.new_cd().1
                    })
                    .stack()?;
                    ensure_eq!(i, len);
                    ensure_eq!(arena.len(), len);
                    for i in 0..len {
                        ensure!(arena.contains(b.p_at(i)));
                    }
                    arena.clear().allow();
                }
            }
            1017..1023 => {
                // the transfers in both directions
                transfer_round_trip(
                    a,
                    &mut a1,
                    &mut b,
                    &mut g,
                    &mut g1,
                    cd_gen,
                    cd_gen1,
                    &mut recaster,
                )
                .stack()?;
                check_invariants(a).stack()?;
                b_capacity = a.capacity();
            }
            1023 => {
                // the rare operations that empty the arena, kept rare so that the
                // length has time to climb back to the limit
                match rng.index_inclusive(5) {
                    0 => {
                        // drain
                        for tmp in a.drain() {
                            ensure_eq!(tmp.is_overflow(), g.invalidate());
                            let (p, t) = tmp.allow();
                            ensure_eq!(b.pos_of_ck(ck(&t)).map(|i| b.p_at(i)), Some(p));
                        }
                        ensure!(a.is_empty());
                        b.clear();
                    }
                    1 => {
                        // drain_ordered, sometimes stopping early so that the `Drop`
                        // impl has to clear the rest
                        let stop_at = if rng.next_bool() {
                            rng.index_inclusive(len)
                        } else {
                            len
                        };
                        let expected = b.order.clone();
                        let mut i = 0usize;
                        {
                            let mut drain = a.drain_ordered();
                            while i < stop_at
                                && let Some((p, t)) = drain.next()
                            {
                                ensure_eq!(p, expected[i].p);
                                ensure_eq!(ck(&t), expected[i].c);
                                i = i.wrapping_add(1);
                            }
                        }
                        ensure!(a.is_empty());
                        b.clear();
                        // every removal advances the generation, and then the `Drop`
                        // impl clears whatever is left which advances it once more
                        for _ in 0..i {
                            g.invalidate();
                        }
                        if i < len {
                            g.invalidate();
                        }
                        ensure_eq!(a.singular_generation().stack()?, g.0);
                    }
                    2 => {
                        // clear
                        b.clear();
                        if a.is_empty() {
                            ensure_eq!(a.clear(), InvalidationOption::Success(()));
                        } else {
                            ensure_eq!(a.clear().is_overflow(), g.invalidate());
                        }
                    }
                    3 => {
                        // transferring in a bigger `a1` so that the max capacity
                        // limits get to reject, and so that the length changes
                        for _ in 0..stats.test_limit {
                            let key = rng.index(KEY_LIMIT as usize).unwrap() as u8;
                            if a1
                                .insert_reallocating(OrdPair::new(key, cd_gen1.new_cd().1))
                                .is_err()
                            {
                                break;
                            }
                        }
                        let before = a.capacity();
                        let max_before = a.max_capacity();
                        let a1_len = a1.len();
                        let keys = key_sequence(&a1);
                        let mut on_first_call = true;
                        let next_gen = PtrGen::generational_inc(g.0).0;
                        let res =
                            a.transfer_canonical_reallocating(next_gen, &mut a1, |_, o, _| {
                                if on_first_call {
                                    b.clear();
                                    on_first_call = false;
                                }
                                assert_eq!(o.is_overflow(), g1.invalidate());
                                let u = o.allow();
                                OrdPair::new(*u.k(), cd_gen.new_cd().1)
                            });
                        if let Some(max) = max_before
                            && a1_len > max
                        {
                            ensure!(on_first_call);
                            ensure_eq!(res, Err(ReallocationError::BeyondMaxCapacity));
                        } else {
                            if on_first_call {
                                // `a1` was empty
                                b.clear();
                            }
                            ensure_eq!(res, Ok(()));
                            ensure!(a1.is_empty());
                            ensure_eq!(a.len(), a1_len);
                            ensure_eq!(a.max_capacity(), max_before);
                            ensure!(a.capacity() >= before);
                            ensure_eq!(key_sequence(a), keys);
                            check_canonical_layout(a).stack()?;
                            g.0 = next_gen;
                            b_capacity = a.capacity();
                            rebuild_model(a, &mut b);
                        }
                    }
                    4 => {
                        // with_min_capacity and the `Drop` impl
                        b.clear();

                        // could succeed for ZSTs
                        ensure_eq!(
                            SimpleOrdArena::<P, TItem<()>, B>::with_min_capacity(usize::MAX)
                                .map(|_| ()),
                            Err(AllocError)
                        );

                        let min_capacity = rng.index_inclusive(stats.test_limit);
                        *a = SimpleOrdArena::with_min_capacity(min_capacity).stack()?;
                        ensure!(a.capacity() >= min_capacity);
                        if stats.fixed_cap.is_some() {
                            stats.fixed_cap = Some(a.capacity());
                        }
                        g.0 = a.singular_generation().stack()?;
                        b_capacity = a.capacity();
                        iters999 += 1;
                    }
                    5 => {
                        // reallocate_min_capacity failures do not lose anything
                        let cap = a.capacity();
                        if let Some(max_capacity) = a.max_capacity()
                            && max_capacity < usize::MAX
                        {
                            ensure_eq!(
                                a.reallocate_min_capacity(max_capacity.wrapping_add(1)),
                                Err(ReallocationError::BeyondMaxCapacity)
                            );
                        } else {
                            ensure_eq!(
                                a.reallocate_min_capacity(usize::MAX),
                                Err(ReallocationError::AllocError)
                            );
                        }
                        ensure_eq!(cap, a.capacity());
                    }
                    _ => unreachable!(),
                }
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
    chain_arena.clear().allow();
    arena.clear().allow();
    Ok(())
}
