# Changelog

## [0.11.0] - 2023-08-29
### Crate
- `triple_arena` 0.12.0

## [0.11.0] - 2023-08-20
### Crate
- `triple_arena` 0.11.0

## [0.10.0] - 2023-08-05
### Crate
- `triple_arena` 0.10.0

### Changes
- The impl of `DebugNodeTrait` for `Link` is now predicated on `T: DebugNodeTrait` and forwards the
  call to the `T`

## [0.9.0] - 2023-06-04
### Crate
- `triple_arena` 0.9.0

## [0.8.0] - 2023-05-09
### Crate
- `triple_arena` 0.8.0

## [0.7.0] - 2022-12-07
### Crate
- `triple_arena` 0.7.0

### Changes
- Added a `p_this` argument to `DebugNodeTrait::debug_node`

## [0.6.0] - 2022-08-02
### Crate
- `triple_arena` 0.6.0

### Changes
- Improved graph arrangement algorithm

## [0.5.0] - 2022-05-31
### Crate
- `triple_arena` 0.5.0

## [0.4.0] - 2022-01-17
### Changes
- `DebugNode` itself now implements `DebugNodeTrait`

## [0.3.2] - 2022-01-05
### Changes
- Reduced line crossings in renderings
- The version number for `triple_arena_render` will now diverge from `triple_arena` because of how
  many more changes it undergoes

### Additions
- Added Changelog
