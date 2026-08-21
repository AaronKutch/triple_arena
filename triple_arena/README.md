# Triple Arena

Provides multiple very flexible and ideal arena types.
All support non-Clone entry insertion and deletion.
All are indexable with a `P: Ptr` generic, which contains an optional
generation counter to check for invalidity (zero cost when omitted).
`no_std` compatible.

- `Arena<P, T>` is the basic unassociated and nonhereditary arena type
- `ChainArena<P, T>` allows associating entries together into multiple linear or cyclic chains,
  representing an idealized doubly linked list stored on an arena
- `SurjectArena<P, K, V>` is a special kind of union-find data structure that can associate key
  entries into nonhereditary sets with a common value entry
- `OrdArena<P, T>` is a fusion between an ordered balanced tree and an arena. Entries can be a
  uniform combined value and key to be ordered by. Hereditary and nonhereditary insertion is
  supported. Unlike most `BTreeMap`s and `HashMap`s, the `P: Ptr` references to entries are stable,
  and can be trivially reused for `O(1)` operations.
- `DirectArena<P, T>` is a freelist-less arena with alternate "direct insertion" methods

Note: there are "alloc" (enabled by default), "std", and "serde_support" feature flags.
When the default "alloc" feature is enabled, the arenas have a defaulted `B: ArenaBacking = triple_arena::utils::HeapBacking` parameter, but when disabled the parameter must be specified.

<!-- base_arena_example -->
```rust
use triple_arena::{Arena, ptr_struct, traits::*};

// In implementations that always use valid indexes and only want the
// generation counter in debug mode, we can use `cfg`s like this:
/* // commented out because of doc tests
#[cfg(Debug)]
ptr_struct!(P0);
#[cfg(Debug)]
ptr_struct!(Q2);
#[cfg(not(Debug))]
ptr_struct!(P0());
#[cfg(not(Debug))]
ptr_struct!(Q2());
*/
ptr_struct!(P0);
ptr_struct!(Q2);

// By convention we use short names for `Ptr` structs beginning with `P`,
// `Q`, or `R`. In simple contexts we add a single digit to differentiate
// the generic `P: Ptr` from a instantiated `P0`. If the number of arenas
// exceeds a small number or the types will be public, you should use more
// descriptive names like `PNode`, `PComponent`, `PNameOfEntryKind`, etc.

// Note: if the crate was compiled with the "alloc" flag, the third
// `B: ArenaBacking` generic argument is defaulted to `crate::HeapBacking`.
// Otherwise, this would need to be something like
// `Arena<P0, String, StackBacking<...>>`.

let mut arena: Arena<P0, String> = Arena::new();

let test_ptr: P0 = arena.insert("test".to_string());
let hello_ptr: P0 = arena.insert("hello".to_string());

// Nice debug representations. See also the `triple_arena_render` crate for
// trait-based rendering of graphs. Note that the internal indexes are
// starting at 1 because `NonZero` types are used. This allows for memory
// niche optimizations of `Option<P>` and other such things.
assert_eq!(
    &format!("{:?}", arena),
    "{P0[1](2): \"test\", P0[2](2): \"hello\"}"
);

// use the `Ptr`s we got from insertion to reference the stored data
assert_eq!(arena[hello_ptr], "hello");

// Remove objects. The `Arena` uses internal freelists to keep the capacity
// for future inserts to reuse. Invalidation functions like
// `ArenaTrait::remove` return an `InvalidationResult` or
// `InvalidationOption` that allow checking for generation overflow. For
// most use cases with the default generation counter size, however, you
// should just use `.allow()` to allow generation overflow because it is
// practically impossible to reach.
let removed = arena.remove(test_ptr).allow().unwrap();
assert_eq!(removed, "test");

// When using generation counters, invalidated pointers are guaranteed to
// never work again.
assert!(arena.get(test_ptr).is_none());

// Using different `Ptr` generics is extremely useful in complicated
// multiple arena code with self pointers and inter-arena pointers. This is
// an arena storing a tuple of pointers that work on the first arena and
// itself.
let mut arena2: Arena<Q2, (P0, Q2)> = Arena::new();

let p2_ptr: Q2 = arena2.insert((hello_ptr, Ptr::invalid()));
let another: Q2 = arena2.insert((hello_ptr, p2_ptr));
assert_eq!(arena2[another].1, p2_ptr);

// With many arena crates, no compile time or runtime checks would prevent
// you from using the wrong pointers. Here, the compiler protects us.
// error: expected struct `P0`, found struct `Q2`
//let _ = arena.get(p2_ptr);

assert_eq!(arena[arena2[p2_ptr].0], "hello");

// In cases where we are forced to have the same `Ptr` struct, we can still
// have type guards against semantically different `Ptr`s by using generics:
fn example<P0: Ptr, P1: Ptr, T>(a0: &mut Arena<P0, T>, a1: &mut Arena<P1, T>, p1: P1) {
    // error: expected type parameter `P0`, found type parameter `P1`
    //let _ = a0.remove(p1);

    a0.insert(a1.remove(p1).allow().unwrap());
}

let mut arena3: Arena<Q2, String> = Arena::new();
example(&mut arena3, &mut arena, hello_ptr);
assert_eq!(arena3.iter().next().unwrap().1, "hello");
```

#### License

<sup>
Licensed under either of <a href="LICENSE-APACHE">Apache License, Version
2.0</a> or <a href="LICENSE-MIT">MIT license</a> at your option.
</sup>

<br>

<sub>
Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in this crate by you, as defined in the Apache-2.0 license, shall
be dual licensed as above, without any additional terms or conditions.
</sub>
