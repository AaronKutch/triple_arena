# Changelog

## [0.12.0] - TODO
### Additions
- Added `LinkNoGen` and `ChainNoGenArena` and made various performance improvements

## [0.11.0] - 2023-08-20
### Fixes
- Fixed that the `Clone::clone_from` specialization on `OrdArena` was broken
- Fixed that the `Debug` impl of `PtrNoGen` was messed up

### Changes
- Undid the tuple grouping of key value pairs in `OrdArena`, because it wasn't worth it and will not
  be compatible with the future cache local version anyway.
- Added a `num` argument to the `OrdArena::*_linear` functions and changed their signatures
- Added some raw functions
- Renamed the `iterators` module to `arena_iterators`

### Additions
- Added `compress_and_shrink` and `compress_and_shrink_with` functions to all arenas
- Added `<_ as Ptr>::name()`
- Added the `recasting` crate and various impls for it
- Added `Recast<Self>` bound to `Ptr`
- Added `PartialEq` and `Eq` impls to the arenas
- Added `SurjectArena::clone_keys_to_arena`

## [0.10.0] - 2023-08-05
### Fixes
- Changed the `Index` and `IndexMut` impls of `ChainArena` to return `&T` and `&mut T` respectively,
  this removes an unintentional place where chains could be broken.

### Changes
- Replaced all `first_ptr`, `next_ptr`, and similar functions with the `Advance` paradigm
- Changed `Link::prev` and others to take `&self`, moved `ChainArena::get` and mutable versions to
  `ChainArena::get_link`, made `ChainArena::get` return just the `&T`.
- Changed order of returned parameters of the `replace_and_update_gen` functions
- Fixed `ChainArena::insert_start` and `ChainArena::insert_end` to return `Result` and actually
  return ownership on failure like the documentation says
- Some iterator structs have more parameters
- The pointer traits are now `unsafe` and should only be implemented through `ptr_struct`
- Slightly optimized `SurjectArena`
- Refactored iterator struct organization
- Added `Unpin + RefUnwindSafe + UnwindSafe` to the pointer traits

### Additions
- Added `OrdArena`
- Added `Advance`
- Added `ArenaTrait`
- Added several Arena cloning functions
- Added `PtrNoGen<P>`
- Added `ChainArena::replace_and_keep_gen` and `ChainArena::replace_and_update_gen`
- Added missing `IntoIterator` and `FromIterator` impls
- Added several hidden functions for getting entries while ignoring generation counters

## [0.9.0] - 2023-06-04
### Changes
- Completely overhauled `SurjectArena` to have three generic parameters

### Additions
- Added `ChainArena::insert_with`
- Added `ChainArena::next_chain_ptr`
- Added `ChainArena::iter_chain`

## [0.8.0] - 2023-05-09
### Fixes
- Fixed subtle blind spot in `ChainArena::_assert_invariants` involving single link cyclical chains
- Fixed that `ChainArena::invalidate` would break chain invariants, now it can update interlinks

### Changes
- Changed `&mut Link<PLink, T>` to `Link<PLink, &mut T>` in some `ChainArena` signatures, because
  even if the interlinks were not directly available the whole struct could be `mem::replaced` and
  the chain invariants broken

### Additions
- Added `SurjectArena`
- Added `ChainArena::remove_chain`
- Added some `_with` variation functions to `ChainArena`
- Added `Link::new`

## [0.7.0] - 2022-12-07
### Additions
- added `first_ptr` and `next_ptr` functions
- added `must_use` attributes where applicable

## [0.6.0] - 2022-08-02
### Changes
- Major overhaul of `Ptr`s that reduces `Ptr<P0>` down to just `P0` and allows for different index
  and generation number sizes. There is now just one `ptr_struct` macro for all use cases.
- Moved the iterator structs into their own module
- The `PartialOrd` on `Ptr`s now sorts first by the internal raw index followed by generation value

### Additions
- Added `swap` and `get2_mut` to `Arena`
- Added `ChainArena`

## [0.5.0] - 2022-05-31
### Additions
- Added `Default` bounds and impls for `Ptr` and `P`

## [0.4.1] - 2022-04-09
### Fixes
- Fixed that the `clear` function resulted in a broken freelist and could cause exponential capacity
  growth. I had a test to prevent cases like this but accidentally did not include the `clear`
  function. I have rechecked all functions to make sure none have been missed.

## [0.4.0] - 2022-01-17
### Changes
- Added `Send` and `Sync` bounds to `Ptr`
- Added an argument to `create` in `Arena::try_insert_with`
- The iteration structs are now public

### Additions
- Added Changelog
- Added `insert_with` to `Arena`
- New iterators for `Arena` were added
