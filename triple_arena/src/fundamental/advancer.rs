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
/// more than once.
///
/// It is _not_ guaranteed that `advance` will continue returning `None`s after
/// the first time a `None` is returned (but this shouldn't be a concern unless
/// you are not using the standard `while let` loop)
pub trait Advancer {
    type Collection;
    type Item;

    fn advance(&mut self, collection: &Self::Collection) -> Option<Self::Item>;
}
