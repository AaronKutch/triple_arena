# Changelog

## [0.6.0] - TODO
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
