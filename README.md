# Triple Arena

Provides very flexible arena type `Arena<T>` and pointer type `TriPtr`. The arena supports non-Clone
`T` and deletion. `TriPtr`s can point to different arenas of different `T`.

No `unsafe` is used. `no_std` compatible.

This crate was inspired by the `generational-arena` crate.
