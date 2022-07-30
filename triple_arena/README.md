# Triple Arena

Provides very flexible arena type `Arena<T, P>` and pointer type `Ptr`. The arena supports
non-Clone `T`, optional generation counters (zero-cost when omitted), and zero-cost arena
differentiation. The generic `P` in `P` is a marker that can be used to guard against using the
wrong `Ptr` in the wrong `Arena` when multiple `Arena`s are in use. The `P` can optionally include a
generation number, in which the arena will use a generation counter to prevent invalidated pointers
from working.

No `unsafe` is used. `no_std` compatible.
