use core::iter::from_fn;

use crate::{
    InvalidationOption, InvalidationResult, Link, LinkNoGen,
    arena::handle_reallocation,
    errors::{ChainInsertionError, ReallocationError},
    traits::{Advancer, ArenaInsertEntryTrait, ArenaTrait, Ptr},
};

// The comments for this are in arena_traits.rs

/// Describes multiple ways to insert a link. All the "*Inx" variants disregard
/// generation counters.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LinkInsertKind<P: Ptr> {
    /// Insert a single link by itself, in a single link chain that is
    /// disconnected from anything else
    Disconnected,
    /// Insert a single link by itself but connected to itself, that is, a
    /// single link cyclic chain
    SingleLinkCyclic,
    /// Insert a link at the end of a chain. The `P` must point to the current
    /// end link of a noncyclic chain, and the inserted node will become the new
    /// end of the chain
    ChainEnd(P),
    ChainEndInx(P::Inx),
    /// Insert a link at the start of a chain. The `P` must point to the current
    /// start link of a noncyclic chain, and the inserted node will become the
    /// new start of the chain
    ChainStart(P),
    ChainStartInx(P::Inx),
    /// Insert a link as the next link from the existing link at `P`, which
    /// could be anywhere on any chain, maintaining continuity of the chain
    NextTo(P),
    NextToInx(P::Inx),
    /// Insert a link as the previous link from the existing link at `P`, which
    /// could be anywhere on any chain, maintaining continuity of the chain
    PrevTo(P),
    PrevToInx(P::Inx),
    /// Insert a link in between two `P` that have an interlink between them,
    /// maintaining continuity of the chain. The insertion will fail if the two
    /// links are not neighbors. Note that the arguments are directionally
    /// sensitive: calling [Link::next] on the link at `next_to` must
    /// result in `prev_to` and not the other way around. Note that this can
    /// act on a single link cyclic chain with `next_to == prev_to`, but
    /// `next_to == prev_to` is allowed only in that case as the "in between"
    /// acts upon the interlink of a link with itself. Single link chains
    /// without a cycle can never succeed with this operation, because there
    /// is no interlink.
    AtInterlink {
        next_to: P,
        prev_to: P,
    },
    AtInterlinkInx {
        next_to: P::Inx,
        prev_to: P::Inx,
    },
    // (named bridge because 3 links are involved, "connect" only involves interlinks)
    /// Insert a link as a bridge in between the end and start of chains. If
    /// this is the end and start of the same chain, this creates a unified
    /// cyclic chain. If this is the end and start of different chains, this
    /// makes a unified linear chain.
    Bridge {
        end: P,
        start: P,
    },
    BridgeInx {
        end: P::Inx,
        start: P::Inx,
    },
}

// for internal convenience
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LinkInsertInxKind<P: Ptr> {
    Disconnected,
    SingleLinkCyclic,
    ChainEndInx(P::Inx),
    ChainStartInx(P::Inx),
    NextToInx(P::Inx),
    PrevToInx(P::Inx),
    // `AtInterlinkInx` and `BridgeInx` unify for the purposes of a verified entry insertion
    InternalConnect { next_to: P::Inx, prev_to: P::Inx },
}

/// A trait for storing an idealized doubly-linked-list on arenas. Multiple
/// separate chains and cyclic chains are supported. This inherits all the
/// methods of [ArenaTrait] but adds on some [Link]-aware
/// ones. See [ChainArena](crate::ChainArena) for the standard implementor.
///
/// # Note
///
/// `P` `Ptr`s to links in a chain arena follow the same validity rules as
/// described on the [ArenaTrait] documentation, except that chain arenas
/// automatically update internal interlinks to maintain the linked-list nature
/// of the chains. The public interface has been designed such that it is not
/// possible to break the doubly linked invariant, which says that each
/// interlink `Ptr` from one link to its neighbor has exactly one corresponding
/// interlink `Ptr` pointing from that neighbor back to itself. However, note
/// that copies of interlinks made external to the arena or put in the custom
/// `T` may be indirectly invalidated by operations on a neighboring link.
///
/// Note that [ArenaTrait::remove] is modified for chain arenas to follow the
/// interlink semantics of [ChainArenaTrait::remove_link_no_gen].
pub trait ChainArenaTrait<P: Ptr, T>: ArenaTrait<P, T> {
    /// An advancer over the valid `Ptr`s of a chain
    type ChainPtrAdvancer: Advancer<Self, Item = P>;
    /// The entry type returned by the `entry_insert*` functions, dropping it
    /// cancels the insertion
    type InsertionEntry<'a>: ArenaInsertEntryTrait<'a, P, T>
    where
        Self: 'a;

    /// Inserts `t` into the arena and returns a `Ptr` to it. Returns an error
    /// if there was no available capacity or if the requirements of `kind` are
    /// not met.
    fn insert_within_capacity(
        &mut self,
        kind: LinkInsertKind<P>,
        t: T,
    ) -> Result<P, ChainInsertionError> {
        let entry = self.entry_insert_within_capacity(kind)?;
        let p = entry.ptr();
        entry.insert(t);
        Ok(p)
    }

    /// Inserts `t` into the arena and returns a `Ptr` to it. Automatically
    /// reallocates if needing more capacity. Returns the `t`
    /// if an allocation error occurs, if [ArenaTrait::max_capacity] is used
    /// up, or if the requirements of `kind` are not met.
    fn insert_reallocating(
        &mut self,
        kind: LinkInsertKind<P>,
        t: T,
    ) -> Result<P, ChainInsertionError> {
        let entry = self.entry_insert_reallocating(kind)?;
        let p = entry.ptr();
        entry.insert(t);
        Ok(p)
    }

    /// Inserts `t` into the arena and returns a `Ptr` to it. Panics if an
    /// allocation error occurs, if [ArenaTrait::max_capacity] is used up, or if
    /// the requirements of `kind` are not met.
    ///
    /// # Panics
    ///
    /// This function can panic on allocation failure when needing to extend
    /// capacity, or if `self.len()` is at the maximum capacity, or if the
    /// requirements of `kind` are not met.
    #[track_caller]
    fn insert(&mut self, kind: LinkInsertKind<P>, t: T) -> P {
        self.insert_reallocating(kind, t)
            .expect("`ChainArenaTrait::insert_reallocating` failed")
    }

    /// If capacity is available and the requirements for the `kind` are met, an
    /// insertion entry for inserting a new link into the arena is returned.
    /// Returns an error if there was no available capacity, or some
    /// requirement was not met.
    fn entry_insert_within_capacity(
        &mut self,
        kind: LinkInsertKind<P>,
    ) -> Result<Self::InsertionEntry<'_>, ChainInsertionError>;

    /// The same as [ChainArenaTrait::entry_insert_within_capacity] but
    /// automatically reallocating if necessary with the same semantics as other
    /// `*_reallocating` functions. Note that
    /// [FailedLinkRequirement](ChainInsertionError::FailedLinkRequirement)
    /// takes priority over the capacity related errors, so that which error is
    /// returned does not depend on how full the arena happens to be.
    fn entry_insert_reallocating(
        &mut self,
        kind: LinkInsertKind<P>,
    ) -> Result<Self::InsertionEntry<'_>, ChainInsertionError> {
        if self.len() == self.capacity() {
            // REF(insertion_idempotency) check the link requirement before growing
            // anything, dropping the entry if there turned out to be capacity anyways
            match self.entry_insert_within_capacity(kind) {
                Ok(_) | Err(ChainInsertionError::NotWithinCapacity) => (),
                Err(e) => return Err(e),
            }
            match handle_reallocation(self) {
                Ok(()) => (),
                Err(ReallocationError::AllocError) => return Err(ChainInsertionError::AllocError),
                Err(ReallocationError::BeyondMaxCapacity) => {
                    return Err(ChainInsertionError::BeyondMaxCapacity);
                }
            }
        }
        self.entry_insert_within_capacity(kind)
    }

    /// The same as [ChainArenaTrait::entry_insert_reallocating], but panics
    /// if an error occurs
    ///
    /// # Panics
    ///
    /// This function can panic on failures of
    /// [ChainArenaTrait::entry_insert_reallocating]
    #[track_caller]
    fn entry_insert(&mut self, kind: LinkInsertKind<P>) -> Self::InsertionEntry<'_> {
        self.entry_insert_reallocating(kind)
            .expect("`ChainArenaTrait::entry_insert_reallocating` failed")
    }

    /// Returns a reference to the link pointed to by `p`. Returns `None` if `p`
    /// is invalid.
    ///
    /// Be aware that unlike the functions returning `LinkNoGen<P, T>`, this has
    /// to look up neighboring links to find their generation counters and may
    /// be less performant.
    fn get_link(&self, p: P) -> Option<Link<P, &T>> {
        let link = self.get_link_no_gen(p)?;
        let mut prev_next = (None, None);
        if let Some(p) = link.prev() {
            let Some((generation, _)) = self.get_inx(p) else {
                // better assembly
                unreachable!()
            };
            prev_next.0 = Some(P::_from_raw(p, generation))
        }
        if let Some(p) = link.next() {
            let Some((generation, _)) = self.get_inx(p) else {
                unreachable!()
            };
            prev_next.1 = Some(P::_from_raw(p, generation))
        }
        Some(Link::new(prev_next, &link.t))
    }

    // no `get_inx_link`, there are a bunch of lookups it has to do anyways

    /// Returns a reference to the link pointed to by `p`. Returns `None` if `p`
    /// is invalid.
    fn get_link_no_gen(&self, p: P) -> Option<&LinkNoGen<P, T>> {
        self.get_inx_link_no_gen(p.inx())
            .and_then(|(generation, link)| (generation == p.generation()).then_some(link))
    }

    /// Like [ChainArenaTrait::get_link_no_gen], except generation counters are
    /// ignored and the existing generation is returned.
    fn get_inx_link_no_gen(&self, p: P::Inx) -> Option<(P::Gen, &LinkNoGen<P, T>)>;

    /// Returns if `p_prev` and `p_next` are neighbors on the same chain, such
    /// that `self.get_link(p_prev).unwrap().next() == Some(p_next)` or
    /// `self.get_link(p_next).unwrap().prev() == Some(p_prev)`. Note that
    /// `self.are_neighbors(p0, p1)` is not necessarily equal to
    /// `self.are_neighbors(p1, p0)` because of the directionality. This
    /// function returns true for the single link cyclic chain case with
    /// `p0 == p1`. Additionally returns `false` if `p_prev` or `p_next` are
    /// invalid `Ptr`s.
    fn are_neighbors(&self, p_prev: P, p_next: P) -> bool {
        if let Some(link) = self.get_link_no_gen(p_prev) {
            if let Some(p) = link.next() {
                // if equal, the link at `p_next.inx()` must implicitly exist because of
                // invariants, but `p_next` can still have an invalid generation
                (p == p_next.inx()) && self.contains(p_next)
            } else {
                false
            }
        } else {
            false
        }
    }

    /// The same as [ChainArenaTrait::are_neighbors] but generation counters are
    /// ignored
    fn are_neighbors_inx(&self, p_prev: P::Inx, p_next: P::Inx) -> bool {
        if let Some((_, link)) = self.get_inx_link_no_gen(p_prev) {
            if let Some(p) = link.next() {
                //  if equal,`p_next` must implicitly exist because of invariants
                p == p_next
            } else {
                false
            }
        } else {
            false
        }
    }

    /// Iteration over all `(P, &LinkNoGen<P, T>)` in the arena
    fn iter_link_no_gen<'a>(&'a self) -> impl Iterator<Item = (P, &'a LinkNoGen<P, T>)>
    where
        T: 'a,
    {
        let mut adv = self.advancer();
        from_fn(move || {
            let p = adv.advance(self)?;
            Some((p, self.get_link_no_gen(p)?))
        })
    }

    // TODO solve the advancer guarding problem

    /// Advances over every valid `Ptr` in the chain that contains `p_init`.
    /// This does _not_ support invalidating `Ptr`s or changing the interlinks
    /// of the chain of `p_init` during the loop.
    ///
    /// # Note
    ///
    /// This handles cyclic chains, however if links or interlinks of the
    /// chain that contains `p_init` are invalidated during the loop, or if the
    /// chain starts as noncyclic and is reconnected to become cyclic during
    /// the loop, it can lead to a loop where the same `Ptr` can be returned
    /// multiple times. There is an internal fail safe that prevents
    /// non-termination.
    fn advancer_chain(&self, p_init: P) -> Option<Self::ChainPtrAdvancer>;

    /// Iteration over `(P, &LinkNoGen<P, T>)` tuples corresponding to all
    /// links in the chain that `p_init` is connected to, according to the order
    /// of [ChainArenaTrait::advancer_chain]
    fn iter_chain<'a>(&'a self, p_init: P) -> Option<impl Iterator<Item = (P, &'a LinkNoGen<P, T>)>>
    where
        T: 'a,
    {
        let mut adv = self.advancer_chain(p_init)?;
        Some(from_fn(move || {
            let p = adv.advance(self)?;
            Some((p, self.get_link_no_gen(p)?))
        }))
    }

    /// Connects the interlinks of `p_prev` and `p_next` such that `p_prev` will
    /// be previous to `p_next`. Returns `None` if `p_prev` has an existing next
    /// interlink, `p_next` has an existing previous interlink, or the pointers
    /// are invalid.
    #[must_use]
    fn connect(&mut self, p_prev: P, p_next: P) -> Option<()>;

    /// Breaks the previous interlink of `p`. Returns `None` if `p` is invalid
    /// or does not have an existing prev link.
    #[must_use]
    fn break_prev(&mut self, p: P) -> Option<()>;

    /// Breaks the next interlink of `p`. Returns `None` if `p` is invalid or
    /// does not have an existing next link.
    #[must_use]
    fn break_next(&mut self, p: P) -> Option<()>;

    /// Exchanges the endpoints of the interlinks right after `p0` and `p1`.
    /// Returns `None` if the links do not have next interlinks or if the
    /// pointers are invalid.
    ///
    /// An interesting property of this function when applied to cyclic chains,
    /// is that `exchange_next` on two `Ptr`s of the same cyclic chain always
    /// results in two cyclic chains (except for if `p0 == p1`), and
    /// `exchange_next` on two `Ptr`s of two separate cyclic chains always
    /// results in a single cyclic chain. This is used by
    /// [SurjectArena](crate::SurjectArena)
    /// to efficiently track and merge sets of nodes.
    #[must_use]
    fn exchange_next(&mut self, p0: P, p1: P) -> Option<()>;

    /// Removes the link at `p`. If the link is in the middle of a chain, the
    /// neighbors of `p` are rerouted to be neighbors of each other so that the
    /// chain remains continuous. Returns `InvalidationResult::Invalid` if `p`
    /// is not valid and `InvalidationResult::GenerationOverflow` if a
    /// generation counter overflowed.
    fn remove_link_no_gen(&mut self, p: P) -> InvalidationResult<LinkNoGen<P, T>> {
        if !self.contains(p) {
            return InvalidationResult::InvalidPtr;
        }
        self.remove_inx_link_no_gen(p.inx()).map(|(_, link)| link)
    }

    /// Same as [ChainArenaTrait::remove_link_no_gen] but without generation
    /// counters
    fn remove_inx_link_no_gen(
        &mut self,
        p: P::Inx,
    ) -> InvalidationResult<(P::Gen, LinkNoGen<P, T>)>;

    /// Efficiently removes the entire chain that `p_init` is connected to
    /// (which might only include itself), yielding the links in the same
    /// order that [advancer_chain](ChainArenaTrait::advancer_chain) would
    /// advance over them. If the iterator is dropped, the rest of the chain
    /// is removed. Returns `None` if `p` is not valid.
    ///
    /// # Unwind Safety
    ///
    /// If a `T::drop` panics while the iterator is being dropped, the links
    /// that have yet to be removed are left in the arena as a valid chain.
    fn drain_chain(
        &mut self,
        p_init: P,
    ) -> Option<impl Iterator<Item = InvalidationOption<(P, LinkNoGen<P, T>)>>>;

    /// This is a more advanced version of [ArenaTrait::compress] that lays out
    /// links within the same chain to be continuous with one another, improving
    /// cache locality. Each chain occupies one contiguous run of indexes in
    /// [Link::next](crate::Link::next) order. Acyclic chains begin at their
    /// start link, and cyclic chains begin at their lowest index link.
    ///
    /// Because an element can be internally swapped multiple times to achieve
    /// this in-place in the allocation, this cannot have a map. Use
    /// [transfer_canonical_reallocating](crate::ChainArena::transfer_canonical_reallocating)
    /// if you need a recaster.
    fn compress_canonical(&mut self, reset_generation: bool) -> InvalidationOption<()>;
}
