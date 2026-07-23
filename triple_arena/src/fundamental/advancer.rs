/// A different kind of iterator that does not borrow the collection.
///
/// When using `Arena`s for their full flexibility, we run into the problem that
/// Rust's external iterators aren't "external" enough. Often in algorithms
/// being applied to the whole `Arena`, the user will need to call
/// `.ptrs().collect()` and allocate just to avoid borrowing conflicts
/// between the iteration and arbitrary mutations on the arena. In a collection
/// such as a `Vec`, you can do
///
/// ```text
/// let mut i = 0;
/// loop {
///     if i >= vec.len() {
///         break
///     }
///     ... vec.get(i) ...
///     ... vec.get_mut(i) ...
///     ... vec.get(any_i) ...
///     ... vec.get_mut(any_i) ...
///     ... vec.remove(any_i) ...
///
///     i += 1;
/// }
/// ```
///
/// This trait allows an analogous loop strategy:
///
/// ```text
/// let mut adv = arena.advancer();
/// while let Some(p) = adv.advance(&arena) {
///     ... arena.get(p) ...
///     ... arena.get_mut(p) ...
///     ... arena.get(any_ptr) ...
///     ... arena.get_mut(any_ptr) ...
///     // any kind of invalidation operation is ok (including the current `p`,
///     // it will not break `advance` or prevent the loop from witnessing a
///     // continuously valid element inserted from before the loop began),
///     ... arena.remove(p) ...
///     // but note that new elements from insertions done during the loop, can
///     // both be encountered or not encountered before the loop terminates.
///     ... let p_inserted = arena.insert(node) ...
///     // capacity shrinking operations and edge cases where a small `PtrInx`
///     // type is used to fill all possible entries with valid entries are
///     // also correctly handled to break the loop when advancement is done
/// }
/// ```
///
/// # Note
///
/// Not all collection types and advancers have the same properties like the
/// above example, be sure to check the documentation in each case.
///
/// `Advancers` should guarantee that any `Some(..)` will always be a valid
/// `Item` for the start of the loop, and it should never return the same `Item`
/// more than once. `Advancers` should also always fuse to always return `None`
/// after the first time `None` is returned.
///
/// `Collection` would have been an associated type (as an extra guard against
/// using the advancer on the wrong structure) instead of a trait parameter. But
/// an unavoidable consequence is that the Advancer structs would have to
/// include `PhantomData`s of the other generic parameters of the collection,
/// and when using them in generics it would require `'static` bounds on those
/// parameters. But, if arenas were already sharing the same `P` parameter then
/// it was easy to cross validity domains anyway. `Advancer`s are by their
/// purpose detached and extremely flexible, and the `'static` bound has been
/// added as well to the advancer type, which is not possible in almost any
/// other kind of iterator.
pub trait Advancer<Collection: ?Sized>: Sized + 'static {
    /// The item that this advancer returns
    type Item;

    /// Advance over the collection and return a single item
    fn advance(&mut self, collection: &Collection) -> Option<Self::Item>;

    /// Returns an empty advancer
    fn empty() -> Self;
}
