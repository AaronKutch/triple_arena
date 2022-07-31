use core::{
    fmt::Debug,
    hash::Hash,
    num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8},
};

/// This should only be implemented on Rust's `NonZeroU...` types, because of
/// their memory saving properties. This is also implemented for `()` for the
/// generationless case.
#[doc(hidden)]
pub trait PtrGen:
    Debug + Hash + Clone + Copy + PartialEq + Eq + PartialOrd + Ord + Send + Sync
{
    /// Returns the first element after 0, which is special because Arenas with
    /// generation counters always start at generation 2, which means invalid
    /// pointers can use generation 1 and be guaranteed to always be invalid.
    fn one() -> Self;
    /// The value of 2
    fn two() -> Self;
    /// Returns `this` incremented by one. This should detect overflow and
    /// should panic if overflow happens.
    fn increment(this: Self) -> Self;
}

// I am using aggressive inlining even on trivial functions because there may
// otherwise be problems if the inlining is happening across compilation units.

macro_rules! impl_gen {
    ($($x: ident)*) => {
        $(
            impl PtrGen for $x {
                #[inline]
                fn one() -> Self {
                    Self::new(1).unwrap()
                }

                #[inline]
                fn two() -> Self {
                    Self::new(2).unwrap()
                }

                #[inline]
                fn increment(this: Self) -> Self {
                    match Self::new(this.get().wrapping_add(1)) {
                        Some(x) => x,
                        None => panic!("generation overflow"),
                    }
                }
            }
        )*
    };
}

impl_gen!(NonZeroU8 NonZeroU16 NonZeroU32 NonZeroU64 NonZeroU128);

impl PtrGen for () {
    #[inline]
    fn one() -> Self {}

    #[inline]
    fn two() -> Self {}

    #[inline]
    fn increment(_this: Self) -> Self {}
}

/// This is a trait for the index type used by the arena.
///
/// This should only be implemented for Rust's unsigned integers.
#[doc(hidden)]
pub trait PtrInx:
    Default + Debug + Hash + Clone + Copy + PartialEq + Eq + PartialOrd + Ord + Send + Sync
{
    /// Note: this should be truncating or zero extending cast, higher level
    /// functions should handle fallible cases
    fn new(inx: usize) -> Self;
    /// Note: this should be truncating or zero extending cast, higher level
    /// functions should handle fallible cases
    fn get(this: Self) -> usize;
    /// The maximum representable value, which should be truncated down to
    /// `usize::MAX` if necessary
    fn max() -> usize;
}

macro_rules! impl_ptr_inx {
    ($($x: ident)*) => {
        $(
            impl PtrInx for $x {
                #[inline]
                fn new(inx: usize) -> Self {
                    inx as $x
                }

                #[inline]
                fn get(this: Self) -> usize {
                    this as usize
                }

                #[inline]
                fn max() -> usize {
                    $x::MAX as usize
                }
            }
        )*
    };
}

impl_ptr_inx!(usize u8 u16 u32 u64 u128);

/// A trait containing index and generation information for the `Arena` type.
/// This crate supplies macros for automatically implementing types implementing
/// this trait efficiently.
///
/// Notes: This trait also has many bounds on it, so that users do not regularly
/// encounter friction with using `Ptr`s in data structures. The
/// `PartialEq`/`Eq` implementation is used for generation value comparison.
/// `Default` should use the `invalid` function.
pub trait Ptr:
    Default + Debug + Hash + Clone + Copy + PartialEq + Eq + PartialOrd + Ord + Send + Sync
{
    /// The recommended general purpose type for this is `usize`
    type Inx: PtrInx;

    /// The recommended general purpose type for this is `NonZeroU64` if
    /// generation tracking is wanted, otherwise `()`.
    type Gen: PtrGen;

    /// Returns a new `Ptr` with a generation value `PtrGen::one()`. Because the
    /// arena starts with generation 2, this is guaranteed invalid when
    /// generation counters are used. The raw index is also set to `Inx::max()`
    /// which should also cause failures with the generationless case, but be
    /// aware this can be reached practically with small `Inx` types.
    fn invalid() -> Self;

    /// Returns a raw `Inx`. This can be useful when getting a unique id for
    /// every entry. Do not rely on this if the `Ptr` is invalidated after
    /// `get_raw` is used.
    fn inx(self) -> Self::Inx;

    /// Returns the generation of this `Ptr`.
    fn gen(self) -> Self::Gen;

    /// Do not use this. This is only exposed because trait methods cannot be
    /// made private.
    #[doc(hidden)]
    fn _from_raw(inx: Self::Inx, gen: Self::Gen) -> Self;
}

/// Convenience macro for quickly making new unit structs that implement
/// `Ptr`. By default, `usize` is used for the index type and `NonZeroU64` is
/// used for the generation type. The struct name can be followed by square
/// brackets containing the type used for the index which can include `u8`
/// through `u128`. After the optional square brackets, optional parenthesis can
/// be added which contain the the generation type which can be `NonZeroU8`
/// through `NonZeroU128`. The parenthesis can also be empty in which case the
/// Arena will not use generation counters. This all can be followed by a comma
/// separated list of attributes.
///
/// ```
/// use triple_arena::prelude::*;
///
/// // Note that in most use cases the default types or default index with no
/// // generation counter are what should be used
///
/// // create struct `P0` implementing a default `Ptr` and having a doc comment
/// ptr_struct!(P0 doc="An example struct `P0` that implements `Ptr`");
/// let _: Arena<P0, String>;
///
/// // `P1` will have a smaller `u16` index type
/// ptr_struct!(P1[u16]);
///
/// use core::num::NonZeroU16;
///
/// // `P2` will have a smaller `NonZeroU16` generation type
/// ptr_struct!(P2(NonZeroU16));
///
/// // both the index and generation type are custom
/// ptr_struct!(P3[u16](NonZeroU16));
///
/// // no generation counter
/// ptr_struct!(P4());
///
/// // byte index with no generation counter
/// ptr_struct!(P5[u8]());
/// ```
#[macro_export]
macro_rules! ptr_struct {
    ($struct_name:ident[$inx_type:path]($gen_type:path) $($attributes:meta),*) => {
        $(#[$attributes])*
        #[derive(
            core::hash::Hash,
            core::clone::Clone,
            core::marker::Copy,
            core::cmp::PartialEq,
            core::cmp::Eq,
            core::cmp::PartialOrd,
            core::cmp::Ord
        )]
        pub struct $struct_name {
            // note: in this order `PartialOrd` will order primarily off of `_internal_inx`
            #[doc(hidden)]
            _internal_inx: $inx_type,
            #[doc(hidden)]
            _internal_gen: $gen_type,
        }

        impl $crate::Ptr for $struct_name {
            type Inx = $inx_type;
            type Gen = $gen_type;

            #[inline]
            fn invalid() -> Self {
                Self {
                    _internal_inx: $crate::PtrInx::new(core::primitive::usize::MAX),
                    _internal_gen: $crate::PtrGen::one()
                }
            }

            #[inline]
            fn inx(self) -> Self::Inx {
                self._internal_inx
            }

            #[inline]
            fn gen(self) -> Self::Gen {
                self._internal_gen
            }

            #[inline]
            #[doc(hidden)]
            fn _from_raw(_internal_inx: Self::Inx, _internal_gen: Self::Gen) -> Self {
                Self {
                    _internal_inx,
                    _internal_gen,
                }
            }
        }

        impl core::default::Default for $struct_name {
            #[inline]
            fn default() -> Self {
                Self::invalid()
            }
        }

        // This is manually implemented so that it is inline and has no newlines, which
        // makes the `Debug` implementation on `Arena` look much nicer.
        impl core::fmt::Debug for $struct_name {
            fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                f.write_fmt(format_args!(
                    "{}[{:?}]({:?})",
                    stringify!($struct_name),
                    self.inx(),
                    self.gen(),
                ))
            }
        }

        impl core::fmt::Display for $struct_name {
            fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                core::fmt::Debug::fmt(self, f)
            }
        }
    };
    ($struct_name:ident[$inx_type:path]() $($attributes:meta),*) => {
        $(#[$attributes])*
        #[derive(
            core::hash::Hash,
            core::clone::Clone,
            core::marker::Copy,
            core::cmp::PartialEq,
            core::cmp::Eq,
            core::cmp::PartialOrd,
            core::cmp::Ord
        )]
        pub struct $struct_name {
            // note: in this order `PartialOrd` will order primarily off of `_internal_inx`
            #[doc(hidden)]
            _internal_inx: $inx_type,
            #[doc(hidden)]
            _internal_gen: (),
        }

        impl $crate::Ptr for $struct_name {
            type Inx = $inx_type;
            type Gen = ();

            #[inline]
            fn invalid() -> Self {
                Self {
                    _internal_inx: $crate::PtrInx::new(core::primitive::usize::MAX),
                    _internal_gen: $crate::PtrGen::one()
                }
            }

            #[inline]
            fn inx(self) -> Self::Inx {
                self._internal_inx
            }

            #[inline]
            fn gen(self) -> Self::Gen {
                self._internal_gen
            }

            #[inline]
            #[doc(hidden)]
            fn _from_raw(_internal_inx: Self::Inx, _internal_gen: Self::Gen) -> Self {
                Self {
                    _internal_inx,
                    _internal_gen,
                }
            }
        }

        impl core::default::Default for $struct_name {
            #[inline]
            fn default() -> Self {
                Self::invalid()
            }
        }

        // This is manually implemented so that it is inline and has no newlines, which
        // makes the `Debug` implementation on `Arena` look much nicer.
        impl core::fmt::Debug for $struct_name {
            fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                f.write_fmt(format_args!(
                    "{}[{:?}]",
                    stringify!($struct_name),
                    self.inx(),
                ))
            }
        }

        impl core::fmt::Display for $struct_name {
            fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                core::fmt::Debug::fmt(self, f)
            }
        }
    };
    ($struct_name:ident[$inx_type:path] $($attributes:meta),*) => {
        $crate::ptr_struct!(
            $struct_name[$inx_type](core::num::NonZeroU64)
            $($attributes),*
        );
    };
    ($struct_name:ident($gen_type:path) $($attributes:meta),*) => {
        $crate::ptr_struct!(
            $struct_name[core::primitive::usize]($gen_type)
            $($attributes),*
        );
    };
    ($struct_name:ident() $($attributes:meta),*) => {
        $crate::ptr_struct!(
            $struct_name[core::primitive::usize]()
            $($attributes),*
        );
    };
    ($struct_name:ident $($attributes:meta),*) => {
        $crate::ptr_struct!(
            $struct_name[core::primitive::usize](core::num::NonZeroU64)
            $($attributes),*
        );
    };
}
