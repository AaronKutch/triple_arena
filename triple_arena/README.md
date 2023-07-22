# Triple Arena

Provides very flexible arena types. All support non-Clone entry insertion and deletion and
are `no_std` compatible. All are indexable with a `P` `Ptr` generic, which contains an optional
generation counter (zero cost when omitted) to check for invalidity. 

- `Arena<P, T>` is the basic unassociated and nonhereditary arena type
- `ChainArena<P, T>` allows associating entries together into multiple linear or cyclic chains,
  representing an idealized doubly linked list stored on an arena
- `SurjectArena<P, K, V>` is a special kind of union-find data structure that can associate key
  entries into nonhereditary sets, and set with a value entry
- `OrdArena<P, K, V>` is a fusion between an ordered balanced tree and an arena. All entries are
  key and value pairs that are all ordered by the key. Hereditary and nonhereditary insertion is
  supported. Unlike most `BTreeMap`s and `HashMap`s, the `P` `Ptr` references to entries are stable
  and can be reused for `O(1)` operations and only incur `O(n log n)` operations on initial
  insertion and deletion
