# Changelog

## [0.10.0] - TODO
### Changes
- Slightly optimized `SurjectArena`
- Some iterator structs have more parameters

### Additions
- Added `PtrNoGen<P>`

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
