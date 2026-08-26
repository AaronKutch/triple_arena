use core::{mem, num::NonZeroUsize, slice::GetDisjointMutError};

use crate::{
    Arena, ChainArena, InvalidationOption, InvalidationResult, LinkInsertInxKind, LinkInsertKind,
    LinkNoGen,
    arena::Canonicalize,
    chain_iterators,
    errors::{AllocError, ChainInsertionError, NotWithinCapacityError, ReallocationError},
    traits::{
        ArenaInsertEntryTrait, ArenaInsertTrait, ArenaTrait, ChainArenaTrait, CompactArenaTrait,
        DisjointableArenaTrait, Ptr,
    },
    utils::{
        ArenaSlot::*,
        from_checked_ptr, from_checked_raw,
        traits::{ArenaBacking, NonZeroInxGenericStack, PtrGen},
    },
};

impl<P: Ptr, T, B: ArenaBacking> ArenaTrait<P, T> for ChainArena<P, T, B> {
    type PtrAdvancer = chain_iterators::PtrAdvancer<P>;

    fn new() -> Self {
        Self { a: Arena::new() }
    }

    fn with_min_capacity(min_capacity: usize) -> Result<Self, AllocError> {
        Ok(Self {
            a: Arena::with_min_capacity(min_capacity)?,
        })
    }

    fn capacity(&self) -> usize {
        self.a.capacity()
    }

    fn max_capacity(&self) -> Option<usize> {
        self.a.max_capacity()
    }

    fn reallocate_min_capacity(&mut self, min_capacity: usize) -> Result<(), ReallocationError> {
        self.a.reallocate_min_capacity(min_capacity)
    }

    fn len(&self) -> usize {
        self.a.len()
    }

    fn singular_generation(&self) -> Option<<P as Ptr>::Gen> {
        Some(self.generation())
    }

    fn get_inx(&self, p: <P as Ptr>::Inx) -> Option<(<P as Ptr>::Gen, &T)> {
        self.a
            .get_inx(p)
            .map(|(generation, link)| (generation, &link.t))
    }

    fn get_inx_mut(&mut self, p: <P as Ptr>::Inx) -> Option<(<P as Ptr>::Gen, &mut T)> {
        self.a
            .get_inx_mut(p)
            .map(|(generation, link)| (generation, &mut link.t))
    }

    fn find_first_inx_ptr(&self) -> Option<P> {
        self.a.find_first_inx_ptr()
    }

    fn find_last_inx_ptr(&self) -> Option<P> {
        self.a.find_last_inx_ptr()
    }

    fn advancer_inx(&self, inx: <P as Ptr>::Inx, rev: bool) -> Self::PtrAdvancer {
        self.internal_advancer_inx(inx, rev)
    }

    fn invalidate(&mut self, p: P) -> InvalidationResult<P> {
        self.a.invalidate(p)
    }

    fn drain(&mut self) -> impl Iterator<Item = InvalidationOption<(P, T)>> {
        self.a.drain().map(|o| o.map(|(p, link)| (p, link.t)))
    }

    fn remove(&mut self, p: P) -> InvalidationResult<T> {
        self.remove_link_no_gen(p).map(|link| link.t)
    }

    fn remove_inx(&mut self, p: <P as Ptr>::Inx) -> InvalidationResult<(<P as Ptr>::Gen, T)> {
        self.remove_inx_link_no_gen(p)
            .map(|(generation, link)| (generation, link.t))
    }

    fn clear(&mut self) -> InvalidationOption<()> {
        self.a.clear()
    }

    fn compress_with<F: FnMut(P, &mut T, P)>(
        &mut self,
        reset_generation: bool,
        mut map: F,
    ) -> InvalidationOption<()> {
        // same as base arena except that interlinks are changed
        let res = if reset_generation {
            self.a.set_generation(P::Gen::two());
            InvalidationOption::Success(())
        } else {
            // follow what `clear` does, and let the rest of the function canonicalize
            if self.is_empty() {
                InvalidationOption::Success(())
            } else {
                self.inc_generation()
            }
        };
        let new_gen = self.a.generation();
        // REF(canonicalize_guard)
        let this = Canonicalize(&mut self.a);
        // we are moving from `j` to `i`
        let mut i = NonZeroUsize::new(1).unwrap();
        for j in this.0.nziter() {
            let p_inx_old = from_checked_raw::<P>(j);
            let p_inx_new = from_checked_raw::<P>(i);
            let Allocated(generation, link) = this.0.m.get_mut(j).unwrap() else {
                continue;
            };
            // REF(map_before_moving)
            let old_gen = *generation;
            map(
                Ptr::_from_raw(p_inx_old, old_gen),
                &mut link.t,
                Ptr::_from_raw(p_inx_new, new_gen),
            );
            *generation = new_gen;
            let prev_next = link.prev_next();
            // handle the SLCC case, the interlinks travel with it
            let slcc = prev_next.0 == Some(p_inx_old);
            if slcc {
                link.prev_next = (Some(p_inx_new), Some(p_inx_new));
            }
            if i != j {
                if !slcc {
                    // Update the interlinks pointing at us. The slot at `i` is always
                    // free here, so a neighbor can never be what the move overwrites.
                    if let Some(p) = prev_next.0 {
                        this.0.get_inx_mut_unwrap(p).prev_next.1 = Some(p_inx_new);
                    }
                    if let Some(p) = prev_next.1 {
                        this.0.get_inx_mut_unwrap(p).prev_next.0 = Some(p_inx_new);
                    }
                }
                // the entry already has the new generation and interlinks in it
                let entry = mem::replace(
                    this.0.m.get_mut(j).unwrap(),
                    // this will be overwritten or dropped
                    Free(P::invalid().inx()),
                );
                let _ = mem::replace(this.0.m.get_mut(i).unwrap(), entry);
            }
            i = i.checked_add(1).unwrap();
        }
        // avoid extra `O(n)` search in canonicalization since there are no free slots
        // in the middle
        this.cancel();
        self.a.remove_free_end_slots();
        // we were relying on the drop to fix this
        self.a.freelist_root = None;
        res
    }
}

impl<P: Ptr, T, B: ArenaBacking> DisjointableArenaTrait<P, T> for ChainArena<P, T, B> {
    fn get_disjoint_inx_mut<const N: usize>(
        &mut self,
        indices: [<P as Ptr>::Inx; N],
    ) -> Result<[(<P as Ptr>::Gen, &mut T); N], GetDisjointMutError> {
        self.a
            .get_disjoint_inx_mut(indices)
            .map(|a| a.map(|(generation, link)| (generation, &mut link.t)))
    }

    fn iter_mut<'a>(&'a mut self) -> impl Iterator<Item = (P, &'a mut T)>
    where
        T: 'a,
    {
        self.a.iter_mut().map(|(p, link)| (p, &mut link.t))
    }
}

impl<P: Ptr, T, B: ArenaBacking> CompactArenaTrait<P, T> for ChainArena<P, T, B> {}

pub struct ChainArenaInsertEntry<'a, P: Ptr, T, B: ArenaBacking> {
    // REF(insertion_idempotency) we drop the entry when constructing this and are relying on
    // idempotency
    a: &'a mut ChainArena<P, T, B>,
    // the `Ptr` of the new link when inserted
    p: P,
    // this must be checked to be valid
    kind: LinkInsertInxKind<P>,
}

impl<'a, P: Ptr, T, B: ArenaBacking> ArenaInsertEntryTrait<'a, P, T>
    for ChainArenaInsertEntry<'a, P, T, B>
{
    fn ptr(&self) -> P {
        self.p
    }

    fn insert(self, t: T) {
        let a = &mut self.a.a;
        let p = self.p;
        // REF(insertion_idempotency)
        let Ok(entry) = a.entry_insert_within_capacity() else {
            unreachable!()
        };
        if entry.ptr() != p {
            unreachable!()
        }
        match self.kind {
            LinkInsertInxKind::Disconnected => entry.insert(LinkNoGen::new((None, None), t)),
            LinkInsertInxKind::SingleLinkCyclic => {
                entry.insert(LinkNoGen::new((Some(p.inx()), Some(p.inx())), t))
            }
            LinkInsertInxKind::ChainStartInx(start) => {
                entry.insert(LinkNoGen::new((None, Some(start)), t));
                a.get_inx_mut_unwrap(start).prev_next.0 = Some(p.inx());
            }
            LinkInsertInxKind::ChainEndInx(end) => {
                entry.insert(LinkNoGen::new((Some(end), None), t));
                a.get_inx_mut_unwrap(end).prev_next.1 = Some(p.inx());
            }
            LinkInsertInxKind::PrevToInx(next) => {
                entry.insert(LinkNoGen::new((None, Some(next)), t));
                let link = a.get_inx_mut_unwrap(next);
                if let Some(old_prev) = link.prev() {
                    // middle of chain
                    link.prev_next.0 = Some(p.inx());
                    a.get_inx_mut_unwrap(p.inx()).prev_next.0 = Some(old_prev);
                    a.get_inx_mut_unwrap(old_prev).prev_next.1 = Some(p.inx());
                } else {
                    link.prev_next.0 = Some(p.inx());
                }
            }
            LinkInsertInxKind::NextToInx(prev) => {
                entry.insert(LinkNoGen::new((Some(prev), None), t));
                let link = a.get_inx_mut_unwrap(prev);
                if let Some(old_next) = link.next() {
                    // middle of chain
                    link.prev_next.1 = Some(p.inx());
                    a.get_inx_mut_unwrap(p.inx()).prev_next.1 = Some(old_next);
                    a.get_inx_mut_unwrap(old_next).prev_next.0 = Some(p.inx());
                } else {
                    link.prev_next.1 = Some(p.inx());
                }
            }
            LinkInsertInxKind::InternalConnect { next_to, prev_to } => {
                entry.insert(LinkNoGen::new((Some(next_to), Some(prev_to)), t));
                a.get_inx_mut_unwrap(next_to).prev_next.1 = Some(p.inx());
                a.get_inx_mut_unwrap(prev_to).prev_next.0 = Some(p.inx());
            }
        }
    }
}

fn check_link_insert_kind<P: Ptr, T, B: ArenaBacking>(
    this: &ChainArena<P, T, B>,
    kind: LinkInsertKind<P>,
) -> Option<LinkInsertInxKind<P>> {
    let a = &this.a;
    match kind {
        LinkInsertKind::Disconnected => Some(LinkInsertInxKind::Disconnected),
        LinkInsertKind::SingleLinkCyclic => Some(LinkInsertInxKind::SingleLinkCyclic),
        LinkInsertKind::ChainStart(start) => a
            .get(start)?
            .prev()
            .is_none()
            .then_some(LinkInsertInxKind::ChainStartInx(start.inx())),
        LinkInsertKind::ChainStartInx(start) => a
            .get_inx(start)?
            .1
            .prev()
            .is_none()
            .then_some(LinkInsertInxKind::ChainStartInx(start)),
        LinkInsertKind::ChainEnd(end) => a
            .get(end)?
            .next()
            .is_none()
            .then_some(LinkInsertInxKind::ChainEndInx(end.inx())),
        LinkInsertKind::ChainEndInx(end) => a
            .get_inx(end)?
            .1
            .next()
            .is_none()
            .then_some(LinkInsertInxKind::ChainEndInx(end)),
        LinkInsertKind::PrevTo(p) => a
            .get(p)
            .is_some()
            .then_some(LinkInsertInxKind::PrevToInx(p.inx())),
        LinkInsertKind::PrevToInx(p) => a
            .get_inx(p)
            .is_some()
            .then_some(LinkInsertInxKind::PrevToInx(p)),
        LinkInsertKind::NextTo(p) => a
            .get(p)
            .is_some()
            .then_some(LinkInsertInxKind::NextToInx(p.inx())),
        LinkInsertKind::NextToInx(p) => a
            .get_inx(p)
            .is_some()
            .then_some(LinkInsertInxKind::NextToInx(p)),
        LinkInsertKind::AtInterlink { next_to, prev_to } => this
            .are_neighbors(next_to, prev_to)
            .then_some(LinkInsertInxKind::InternalConnect {
                next_to: next_to.inx(),
                prev_to: prev_to.inx(),
            }),
        LinkInsertKind::AtInterlinkInx { next_to, prev_to } => this
            .are_neighbors_inx(next_to, prev_to)
            .then_some(LinkInsertInxKind::InternalConnect { next_to, prev_to }),
        LinkInsertKind::Bridge { end, start } => {
            let mut res = None;
            if let Some(link0) = a.get(end)
                && let Some(link1) = a.get(start)
                && link0.next().is_none()
                && link1.prev().is_none()
            {
                res = Some(LinkInsertInxKind::InternalConnect {
                    next_to: end.inx(),
                    prev_to: start.inx(),
                })
            }
            res
        }
        LinkInsertKind::BridgeInx { end, start } => {
            let mut res = None;
            if let Some((_, link0)) = a.get_inx(end)
                && let Some((_, link1)) = a.get_inx(start)
                && link0.next().is_none()
                && link1.prev().is_none()
            {
                res = Some(LinkInsertInxKind::InternalConnect {
                    next_to: end,
                    prev_to: start,
                })
            }
            res
        }
    }
}

impl<P: Ptr, T, B: ArenaBacking> ChainArenaTrait<P, T> for ChainArena<P, T, B> {
    type ChainPtrAdvancer = chain_iterators::ChainPtrAdvancer<P>;
    type InsertionEntry<'a>
        = ChainArenaInsertEntry<'a, P, T, B>
    where
        Self: 'a;

    fn get_inx_link_no_gen(&self, p: <P as Ptr>::Inx) -> Option<(P::Gen, &LinkNoGen<P, T>)> {
        self.a.get_inx(p)
    }

    fn advancer_chain(&self, p_init: P) -> Option<Self::ChainPtrAdvancer> {
        self.internal_advancer_chain(p_init)
    }

    fn entry_insert_within_capacity(
        &mut self,
        kind: LinkInsertKind<P>,
    ) -> Result<Self::InsertionEntry<'_>, ChainInsertionError> {
        let Some(kind) = check_link_insert_kind(self, kind) else {
            return Err(ChainInsertionError::FailedLinkRequirement);
        };
        match self.a.entry_insert_within_capacity() {
            Ok(entry) => {
                let p = entry.ptr();
                Ok(ChainArenaInsertEntry { a: self, p, kind })
            }
            Err(NotWithinCapacityError) => Err(ChainInsertionError::NotWithinCapacity),
        }
    }

    fn connect(&mut self, p_prev: P, p_next: P) -> Option<()> {
        if self.get_link_no_gen(p_prev)?.next().is_none()
            && self.get_link_no_gen(p_next)?.prev().is_none()
        {
            self.a.get_inx_mut_unwrap(p_prev.inx()).prev_next.1 = Some(p_next.inx());
            self.a.get_inx_mut_unwrap(p_next.inx()).prev_next.0 = Some(p_prev.inx());
            Some(())
        } else {
            None
        }
    }

    fn break_prev(&mut self, p: P) -> Option<()> {
        let prev = self.get_link_no_gen(p)?.prev()?;
        self.a.get_inx_mut_unwrap(prev).prev_next.1 = None;
        self.a.get_inx_mut_unwrap(p.inx()).prev_next.0 = None;
        Some(())
    }

    fn break_next(&mut self, p: P) -> Option<()> {
        let next = self.get_link_no_gen(p)?.next()?;
        self.a.get_inx_mut_unwrap(p.inx()).prev_next.1 = None;
        self.a.get_inx_mut_unwrap(next).prev_next.0 = None;
        Some(())
    }

    fn exchange_next(&mut self, p0: P, p1: P) -> Option<()> {
        if self.contains(p0) && self.contains(p1) {
            // get downstream links
            let d0 = self.a.get_inx_unwrap(p0.inx()).next()?;
            let d1 = self.a.get_inx_unwrap(p1.inx()).next()?;
            self.a.get_inx_mut_unwrap(p0.inx()).prev_next.1 = Some(d1);
            self.a.get_inx_mut_unwrap(p1.inx()).prev_next.1 = Some(d0);
            self.a.get_inx_mut_unwrap(d0).prev_next.0 = Some(p1.inx());
            self.a.get_inx_mut_unwrap(d1).prev_next.0 = Some(p0.inx());
            Some(())
        } else {
            None
        }
    }

    fn remove_inx_link_no_gen(
        &mut self,
        p: P::Inx,
    ) -> InvalidationResult<(P::Gen, LinkNoGen<P, T>)> {
        let (Some((generation, link)), o) = self.a.remove_inx(p).overflowing() else {
            return InvalidationResult::InvalidPtr;
        };
        match link.prev_next() {
            (None, None) => (),
            (None, Some(p1)) => {
                self.a.get_inx_mut_unwrap(p1).prev_next.0 = None;
            }
            (Some(p0), None) => {
                self.a.get_inx_mut_unwrap(p0).prev_next.1 = None;
            }
            (Some(p0), Some(p1)) => {
                if p != p0 {
                    self.a.get_inx_mut_unwrap(p0).prev_next.1 = Some(p1);
                    self.a.get_inx_mut_unwrap(p1).prev_next.0 = Some(p0);
                } // else it is a single link cyclic chain
            }
        }
        if o {
            InvalidationResult::GenerationOverflow((generation, link))
        } else {
            InvalidationResult::Success((generation, link))
        }
    }

    fn drain_chain(
        &mut self,
        p_init: P,
    ) -> Option<impl Iterator<Item = InvalidationOption<(P, LinkNoGen<P, T>)>>> {
        self.internal_drain_chain(p_init)
    }

    fn compress_canonical(&mut self, reset_generation: bool) -> InvalidationOption<()> {
        let res = if reset_generation {
            self.a.set_generation(<P::Gen as PtrGen>::two());
            InvalidationOption::Success(())
        } else {
            // follow what `clear` does
            if self.is_empty() {
                InvalidationOption::Success(())
            } else {
                self.inc_generation()
            }
        };
        let new_gen = self.a.generation();

        // with this method, we do the same thing as normal compression, except that
        // every time we encounter a new chain, we iterate to find the start of the
        // chain (or discover that it is cyclic), and then starting from the start
        // link (or from the earliest index link if cyclic), we move that entire chain
        // to be in order compressed at `i` incrementing, swapping entries (and
        // preserving interlinks) if there was an allocation at `i` that we can't deal
        // with yet.

        // we are moving from `j` to `i`
        let mut i = NonZeroUsize::new(1).unwrap();
        let mut j = NonZeroUsize::new(1);
        while let Some(init_j) = j {
            if init_j.get() > self.a.m.len() {
                break;
            }
            if let Allocated(_, init_link) = self.a.m.get(init_j).unwrap() {
                // found lowest index link of a chain, time to find the start of the chain or
                // discover cyclicity
                let p_init = from_checked_raw::<P>(init_j);
                let mut target = p_init;
                let mut prev = init_link.prev();
                while let Some(p) = prev {
                    target = p;
                    if p == p_init {
                        // cyclic, and `target` is set to what we want
                        break;
                    }
                    prev = self.a.get_inx_unwrap(p).prev();
                }

                // start compressing the chain starting from `target` moving in the `Link::next`
                // direction, swapping to get other nodes out of the way when necessary.
                let i_first = from_checked_raw::<P>(i);
                loop {
                    if i == from_checked_ptr::<P>(target) {
                        // optimize and avoid edge case
                        let Allocated(old_gen, _link) = self.a.m.get_mut(i).unwrap() else {
                            unreachable!()
                        };
                        *old_gen = new_gen;
                        i = i.checked_add(1).unwrap();
                        let Some(next) = self.a.get_inx_unwrap(target).next() else {
                            break;
                        };
                        target = next;
                        // the sentinel for a cyclic chain having come all the way around has to be
                        // where the first link of the chain is moved to and not where it started
                        if target == i_first {
                            break;
                        }
                    }
                    // we need to handle the SLCC case, also it is possible for the replaced node to
                    // be the next node on the same chain, update the interlinks pointing to the
                    // current link and replaced link before doing any replacement
                    let p_inx_new = from_checked_raw::<P>(i);
                    let raw_target = from_checked_ptr::<P>(target);
                    let Allocated(_, link) = self.a.m.get(raw_target).unwrap() else {
                        unreachable!()
                    };
                    let prev0 = link.prev();
                    let next0 = link.next();
                    // get both before mutating
                    let mut prev1 = None;
                    let mut next1 = None;
                    if let Some(Allocated(_, link)) = self.a.m.get(i) {
                        prev1 = link.prev();
                        next1 = link.next()
                    }
                    if let Some(prev) = prev0 {
                        self.a.get_inx_mut_unwrap(prev).prev_next.1 = Some(p_inx_new);
                    }
                    if let Some(next) = next0 {
                        self.a.get_inx_mut_unwrap(next).prev_next.0 = Some(p_inx_new);
                    }
                    if let Some(prev) = prev1 {
                        self.a.get_inx_mut_unwrap(prev).prev_next.1 = Some(target);
                    }
                    if let Some(next) = next1 {
                        self.a.get_inx_mut_unwrap(next).prev_next.0 = Some(target);
                    }

                    let Allocated(_old_gen, link) = mem::replace(
                        self.a.m.get_mut(raw_target).unwrap(),
                        Free(P::invalid().inx()),
                    ) else {
                        unreachable!()
                    };
                    let next = link.next();

                    let replaced =
                        mem::replace(self.a.m.get_mut(i).unwrap(), Allocated(new_gen, link));
                    if let Allocated(..) = replaced {
                        // finish 3 replacements to do the swap
                        let _ = mem::replace(self.a.m.get_mut(raw_target).unwrap(), replaced);
                    }

                    i = i.checked_add(1).unwrap();
                    let Some(next) = next else { break };
                    target = next;
                    if target == i_first {
                        break;
                    }
                }

                j = Some(i);
            } else {
                j = init_j.checked_add(1);
            }
        }
        self.a.remove_free_end_slots();
        self.a.freelist_root = None;
        res
    }
}
