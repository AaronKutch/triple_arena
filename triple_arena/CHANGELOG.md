# Changelog

## [0.4.1] - 2022-04-09
### Fixes
- Fixed that the `clear` function resulted in a broken freelist and could cause exponential capacity
  growth. I had a test to prevent cases like this but accidentally did not include the `clear`
  function. I have rechecked all functions to make sure none have been missed.


## [0.4.0] - 2022-01-17
### Changes
- Added `Send` and `Sync` bounds to `PtrTrait`
- Added an argument to `create` in `Arena::try_insert_with`
- The iteration structs are now public

### Additions
- Added Changelog
- Added `insert_with` to `Arena`
- New iterators for `Arena` were added
