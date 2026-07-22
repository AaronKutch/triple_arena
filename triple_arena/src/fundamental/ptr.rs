/*

NOTE: do not forget to update `ptr_serde.rs` when updating this file

*/
use core::{
    fmt::Debug,
    hash::Hash,
    num::{NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize},
    panic::{RefUnwindSafe, UnwindSafe},
};

use recasting::{Recast, Recaster};

/// The trait for Arena Pointer generation types. Users should never have to
/// implement this for simple arenas, it is implemented for the `NonZeroU...`
/// types and for `()`.
pub trait PtrGen:
    Debug
    + Hash
    + Clone
    + Copy
    + PartialEq
    + Eq
    + PartialOrd
    + Ord
    + Send
    + Sync
    + Unpin
    + RefUnwindSafe
    + UnwindSafe
    + Recast<Self>
    + 'static
{
    /// Returns generation 1, which we designate as a representable invalid
    /// generation value, because Arenas with generation counters always
    /// start at generation 2, and [PtrGen::generational_inc] skips generation
    /// 2, which means invalid pointers can be constructed with this
    /// generation and be guaranteed to always be invalid.
    fn one() -> Self;
    /// The first valid generation value
    fn two() -> Self;
    /// A special overflowing increment function. For all values (including
    /// [PtrGen::one], but this shouldn't normally be done) except for the
    /// maximum value, this simply returns the incremented integer value and
    /// `false`. Upon being called on the maximum value, this overflows by
    /// skipping both the unrepresentable generation 0 and invalid generation 1
    /// values, resulting in [PtrGen::two] and a `true` value for overflow.
    fn generational_inc(this: Self) -> (Self, bool);
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
                fn generational_inc(this: Self) -> (Self, bool) {
                    match Self::new(this.get().wrapping_add(1)) {
                        Some(x) => (x, false),
                        None => (Self::new(2).unwrap(), true),
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
    fn generational_inc(_this: Self) -> (Self, bool) {
        ((), false)
    }
}

/// The trait for Arena index types. Users should never have to implement this
/// for simple arenas, it is implemented for the primitive unsigned integers.
#[allow(clippy::missing_safety_doc)]
pub trait PtrInx:
    Debug
    + Hash
    + Clone
    + Copy
    + PartialEq
    + Eq
    + PartialOrd
    + Ord
    + Send
    + Sync
    + Unpin
    + RefUnwindSafe
    + UnwindSafe
    + Recast<Self>
    + 'static
{
    /// This is used by "simple" arenas that expect a simple integer index that
    /// can be cast to and from `NonZeroUsize` losslessly. `NonZeroUsize` is
    /// used because any in-memory arena cannot ever take advantage of more
    /// elements using a larger type. If `inx` would be truncated when casting
    /// from `NonZeroUsize`, this must return `None` (this would only normally
    /// happen from a manually constructed `Ptr`, but we prefer to be strict,
    /// and it optimizes to nothing with the default). If this is not a simple
    /// `PtrInx` (such as one intended for a complex arena that takes the index
    /// modulo something and dispatches to different substructures), then it
    /// should always return `None`, so that any of the simple arenas will
    /// report the inability to allocate if given a `Ptr` with a complex index.
    fn try_from_usize(inx: NonZeroUsize) -> Option<Self>;
    /// See [PtrInx::try_from_usize], this is the same except for converting to
    /// `NonZeroUsize`
    fn try_into_usize(this: Self) -> Option<NonZeroUsize>;
    /// Returns the invalid index most likely to be unvalid if given to an
    /// arena, which is usually the max value
    fn best_effort_invalid() -> Self;
}

macro_rules! impl_ptr_inx {
    ($($nz:ident $x:ident);*;) => {
        $(
            impl PtrInx for $nz {
                #[inline]
                fn try_from_usize(inx: NonZeroUsize) -> Option<Self> {
                    // the zero check will optimize away, and the `try_into` will optimize away in the standard case
                    $nz::new(inx.get().try_into().ok()?)
                }

                #[inline]
                fn try_into_usize(this: Self) -> Option<NonZeroUsize> {
                    // the zero check will optimize away
                    NonZeroUsize::new(this.get().try_into().ok()?)
                }

                fn best_effort_invalid() -> Self {
                    $nz::MAX
                }
            }
        )*
    };
}

impl_ptr_inx!(
    NonZeroUsize usize;
    NonZeroU8 u8;
    NonZeroU16 u16;
    NonZeroU32 u32;
    NonZeroU64 u64;
    NonZeroU128 u128;
);

/// A trait containing index and generation information for the `Arena` type.
///
/// Users should never have to manually implement this, use the `ptr_trait`
/// macro for automatically implementing types implementing this trait safely
/// and efficiently.
///
/// This trait also has many bounds on it, so that users do not regularly
/// encounter friction with using `Ptr`s in data structures.
///
/// The `Inx` and `Gen` types should only be the types implemented by this
/// crate, the function descriptions should be followed. The `PartialEq`/`Eq`
/// implementation should differentiate between pointers at the same index but
/// different generation. `Default` should use the `invalid` function.
#[allow(clippy::missing_safety_doc)]
pub unsafe trait Ptr:
    Debug
    + Hash
    + Clone
    + Copy
    + PartialEq
    + Eq
    + PartialOrd
    + Ord
    + Send
    + Sync
    + Unpin
    + RefUnwindSafe
    + UnwindSafe
    + Recast<Self>
    + 'static
{
    /// The recommended general purpose type for this is `usize`
    type Inx: PtrInx;

    /// The recommended general purpose type for this is `NonZeroU64` if
    /// generation tracking is wanted, otherwise `()`.
    type Gen: PtrGen;

    /// The struct name used in debugging (needed by `PtrNoGen` for example)
    fn name() -> &'static str;

    /// Returns a new `Ptr` with a generation value `PtrGen::one()`. Because the
    /// arena starts with generation 2 and skips generation 1 on overflow, this
    /// is guaranteed invalid if generation counters are used. The raw index
    /// is also set to `Inx::best_effort_invalid()` which should also cause
    /// failures with the generationless case, but be aware this can be
    /// reached practically with small `Inx` types.
    fn invalid() -> Self;

    /// Returns a raw `Inx`. This can be useful when getting a unique id for
    /// every entry, but be aware of generational invalidation.
    fn inx(self) -> Self::Inx;

    /// Returns the generation of this `Ptr`.
    fn generation(self) -> Self::Gen;

    /// Do not use this unless you are manually managing internal details
    fn _from_raw(inx: Self::Inx, generation: Self::Gen) -> Self;
}

/// Convenience macro for quickly making new structs that implement `Ptr`. The
/// index and generation types can be changed to be smaller for less memory
/// footprint in exchange for smaller maximum arena capacity and generations.
///
/// By default, `NonZeroUsize` is used for the index type and `NonZeroU64` is
/// used for the generation type. The struct name can be followed by square
/// brackets containing the type used for the index which can include
/// `NonZeroU8` through `NonZeroU128`. After the optional square brackets,
/// optional parenthesis can be added which contain the the generation type
/// which can be `NonZeroU8` through `NonZeroU128`. The parenthesis can also be
/// empty in which case the Arena will not use generation counters. This all can
/// be followed by a comma separated list of attributes.
///
/// ```
/// use core::num::{NonZeroU16, NonZeroU8};
/// use triple_arena::{ptr_struct, Arena, traits::Ptr};
///
/// // Note that in most use cases the default types or default index with no
/// // generation counter are what should be used
///
/// // create struct `P0` implementing a default `Ptr` and having a doc comment
/// ptr_struct!(P0 doc="An example struct `P0` that implements `Ptr`");
/// let _: Arena<P0, String>;
///
/// // `P1` will have a smaller `NonZeroU16` index type
/// ptr_struct!(P1[NonZeroU16]);
///
/// // `P2` will have a smaller `NonZeroU16` generation type
/// ptr_struct!(P2(NonZeroU16));
///
/// // both the index and generation type are custom
/// ptr_struct!(P3[NonZeroU16](NonZeroU16));
///
/// // no generation counter
/// ptr_struct!(P4());
///
/// // byte index with no generation counter
/// ptr_struct!(P5[NonZeroU8]());
///
/// // a single macro can have multiple structs of the same matching kind with
/// // semicolon separators
/// ptr_struct!(Q0(); Q1(); R0());
/// ```
#[macro_export]
macro_rules! ptr_struct {
    ($($struct_name:ident[$inx_type:path]($gen_type:path) $($attributes:meta),*);*) => {
        $(
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

            unsafe impl $crate::traits::Ptr for $struct_name {
                type Inx = $inx_type;
                type Gen = $gen_type;

                fn name() -> &'static str {
                    stringify!($struct_name)
                }

                #[inline]
                fn invalid() -> Self {
                    Self {
                        _internal_inx: $crate::utils::traits::PtrInx::best_effort_invalid(),
                        _internal_gen: $crate::utils::traits::PtrGen::one()
                    }
                }

                #[inline]
                fn inx(self) -> Self::Inx {
                    self._internal_inx
                }

                #[inline]
                fn generation(self) -> Self::Gen {
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
                    $crate::traits::Ptr::invalid()
                }
            }

            // This is manually implemented so that it is inline and has no newlines, which
            // makes the `Debug` implementation on `Arena` look much nicer.
            impl core::fmt::Debug for $struct_name {
                fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                    f.write_fmt(format_args!(
                        "{}[{:x?}]({:x?})",
                        <Self as $crate::traits::Ptr>::name(),
                        $crate::traits::Ptr::inx(*self),
                        $crate::traits::Ptr::generation(*self),
                    ))
                }
            }

            impl core::fmt::Display for $struct_name {
                fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                    core::fmt::Debug::fmt(self, f)
                }
            }

            impl $crate::traits::Recast<Self> for $struct_name {
                fn recast<R: $crate::traits::Recaster<Item = Self>>(&mut self, recaster: &R)
                    -> core::result::Result<(), <R as $crate::traits::Recaster>::Item> {
                    recaster.recast_item(self)
                }
            }
        )*
    };
    ($($struct_name:ident[$inx_type:path]() $($attributes:meta),*);*) => {
        $(
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

            unsafe impl $crate::traits::Ptr for $struct_name {
                type Inx = $inx_type;
                type Gen = ();

                fn name() -> &'static str {
                    stringify!($struct_name)
                }

                #[inline]
                fn invalid() -> Self {
                    Self {
                        _internal_inx: $crate::utils::traits::PtrInx::best_effort_invalid(),
                        _internal_gen: $crate::utils::traits::PtrGen::one()
                    }
                }

                #[inline]
                fn inx(self) -> Self::Inx {
                    self._internal_inx
                }

                #[inline]
                fn generation(self) -> Self::Gen {
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
                    $crate::traits::Ptr::invalid()
                }
            }

            // This is manually implemented so that it is inline and has no newlines, which
            // makes the `Debug` implementation on `Arena` look much nicer.
            impl core::fmt::Debug for $struct_name {
                fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                    f.write_fmt(format_args!(
                        "{}[{:x?}]",
                        <Self as $crate::traits::Ptr>::name(),
                        $crate::traits::Ptr::inx(*self),
                    ))
                }
            }

            impl core::fmt::Display for $struct_name {
                fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                    core::fmt::Debug::fmt(self, f)
                }
            }

            impl $crate::traits::Recast<Self> for $struct_name {
                fn recast<R: $crate::traits::Recaster<Item = Self>>(&mut self, recaster: &R)
                    -> core::result::Result<(), <R as $crate::traits::Recaster>::Item> {
                    recaster.recast_item(self)
                }
            }
        )*
    };
    ($($struct_name:ident[$inx_type:path] $($attributes:meta),*);*) => {
        $(
            $crate::ptr_struct!(
                $struct_name[$inx_type](core::num::NonZeroU64)
                $($attributes),*
            );
        )*
    };
    ($($struct_name:ident($gen_type:path) $($attributes:meta),*);*) => {
        $(
            $crate::ptr_struct!(
                $struct_name[core::num::NonZeroUsize]($gen_type)
                $($attributes),*
            );
        )*
    };
    ($($struct_name:ident() $($attributes:meta),*);*) => {
        $(
            $crate::ptr_struct!(
                $struct_name[core::num::NonZeroUsize]()
                $($attributes),*
            );
        )*
    };
    ($($struct_name:ident $($attributes:meta),*);*) => {
        $(
            $crate::ptr_struct!(
                $struct_name[core::num::NonZeroUsize](core::num::NonZeroU64)
                $($attributes),*
            );
        )*
    };
}

/// This wraps around any `P: Ptr` and acts like a `ptr_struct` implemented `P`
/// but with the generation counter removed. Most cases should use `P::Inx`
/// directly instead, this is used in case `Ptr` needs to be implemented.
#[derive(
    core::hash::Hash,
    core::clone::Clone,
    core::marker::Copy,
    core::cmp::PartialEq,
    core::cmp::Eq,
    core::cmp::PartialOrd,
    core::cmp::Ord,
)]
pub struct PtrNoGen<P: Ptr> {
    #[doc(hidden)]
    _internal_inx: P::Inx,
    #[doc(hidden)]
    _internal_gen: (),
}

unsafe impl<P: Ptr> Ptr for PtrNoGen<P> {
    type Gen = ();
    type Inx = P::Inx;

    fn name() -> &'static str {
        P::name()
    }

    #[inline]
    fn invalid() -> Self {
        Self {
            _internal_inx: PtrInx::best_effort_invalid(),
            _internal_gen: PtrGen::one(),
        }
    }

    #[inline]
    fn inx(self) -> Self::Inx {
        self._internal_inx
    }

    #[inline]
    fn generation(self) -> Self::Gen {
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

impl<P: Ptr> core::default::Default for PtrNoGen<P> {
    #[inline]
    fn default() -> Self {
        Ptr::invalid()
    }
}

impl<P: Ptr> core::fmt::Debug for PtrNoGen<P> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.write_fmt(format_args!("{}[{:x?}]", Self::name(), Ptr::inx(*self),))
    }
}

impl<P: Ptr> core::fmt::Display for PtrNoGen<P> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        core::fmt::Debug::fmt(self, f)
    }
}

impl<P: Ptr> Recast<Self> for PtrNoGen<P> {
    fn recast<R: Recaster<Item = Self>>(
        &mut self,
        recaster: &R,
    ) -> Result<(), <R as Recaster>::Item> {
        recaster.recast_item(self)
    }
}
