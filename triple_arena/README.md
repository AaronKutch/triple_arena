# Triple Arena

Provides 4 very flexible arena types. All support non-Clone entry insertion and deletion.
All are indexable with a `P: Ptr` generic, which contains an optional
generation counter to check for invalidity (zero cost when omitted). `no_std` compatible.

- `Arena<P, T>` is the basic unassociated and nonhereditary arena type
- `ChainArena<P, T>` allows associating entries together into multiple linear or cyclic chains,
  representing an idealized doubly linked list stored on an arena
- `SurjectArena<P, K, V>` is a special kind of union-find data structure that can associate key
  entries into nonhereditary sets with a common value entry
- `OrdArena<P, K, V>` is a fusion between an ordered balanced tree and an arena. All entries are
  key and value pairs that are all ordered by the key. Hereditary and nonhereditary insertion is
  supported. Unlike most `BTreeMap`s and `HashMap`s, the `P: Ptr` references to entries are stable,
  and can be trivially reused for `O(1)` operations.
