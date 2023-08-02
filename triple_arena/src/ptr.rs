use core::{
    fmt::Debug,
    hash::Hash,
    num::{NonZeroU128, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize},
    panic::{RefUnwindSafe, UnwindSafe},
};

use crate::utils::nzusize_unchecked;

/// Pointer generation information type
///
/// Users should never have to implement this, it is implemented only for the
/// `NonZeroU...` types and for `()`.
#[allow(clippy::missing_safety_doc)]
pub unsafe trait PtrGen:
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
            unsafe impl PtrGen for $x {
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

unsafe impl PtrGen for () {
    #[inline]
    fn one() -> Self {}

    #[inline]
    fn two() -> Self {}

    #[inline]
    fn increment(_this: Self) -> Self {}
}

/// This is a trait for the index type used by the arena.
///
/// Users should never have to implement this, it is implemented only for Rust's
/// unsigned integers.
#[allow(clippy::missing_safety_doc)]
pub unsafe trait PtrInx:
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
{
    /// Note: this should be truncating or zero extending cast, higher level
    /// functions should handle fallible cases
    fn new(inx: NonZeroUsize) -> Self;
    /// Note: this should be truncating or zero extending cast, higher level
    /// functions should handle fallible cases
    fn get(this: Self) -> NonZeroUsize;
    /// The maximum representable value, which should be truncated down to
    /// `usize::MAX` if necessary
    fn max() -> NonZeroUsize;
}

macro_rules! impl_ptr_inx {
    ($($nz:ident $x:ident);*;) => {
        $(
            unsafe impl PtrInx for $nz {
                #[inline]
                fn new(inx: NonZeroUsize) -> Self {
                    $nz::new(inx.get() as $x).unwrap()
                }

                #[inline]
                fn get(this: Self) -> NonZeroUsize {
                    NonZeroUsize::new(this.get() as usize).unwrap()
                }

                #[inline]
                fn max() -> NonZeroUsize {
                    NonZeroUsize::new($x::MAX as usize).unwrap()
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

/// Shorthand for `PtrInx::new(nzusize_unchecked(x))`.
///
/// # Safety
///
/// `x` must not be 0 and must be within the `PtrInx` limits
pub unsafe fn ptrinx_unchecked<P: PtrInx>(x: usize) -> P {
    PtrInx::new(nzusize_unchecked(x))
}

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

    /// Do not use this unless you are manually managing internal details
    fn _from_raw(inx: Self::Inx, gen: Self::Gen) -> Self;
}

/// Convenience macro for quickly making new structs that implement `Ptr`. By
/// default, `usize` is used for the index type and `NonZeroU64` is used for the
/// generation type. The struct name can be followed by square brackets
/// containing the type used for the index which can include `u8` through
/// `u128`. After the optional square brackets, optional parenthesis can be
/// added which contain the the generation type which can be `NonZeroU8` through
/// `NonZeroU128`. The parenthesis can also be empty in which case the Arena
/// will not use generation counters. This all can be followed by a comma
/// separated list of attributes.
///
/// ```
/// use core::num::{NonZeroU16, NonZeroU8};
/// use triple_arena::{ptr_struct, Arena, Ptr};
///
/// // Note that in most use cases the default types or default index with no
/// // generation counter are what should be used
///
/// // create struct `P0` implementing a default `Ptr` and having a doc comment
/// ptr_struct!(P0 doc="An example struct `P0` that implements `Ptr`");
/// let _: Arena<P0, String>;
///
///
/// // `P1` will have a smaller `u16` index type
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

            unsafe impl $crate::Ptr for $struct_name {
                type Inx = $inx_type;
                type Gen = $gen_type;

                #[inline]
                fn invalid() -> Self {
                    Self {
                        _internal_inx: $crate::utils::PtrInx::new(
                            <Self::Inx as $crate::utils::PtrInx>::max()
                        ),
                        _internal_gen: $crate::utils::PtrGen::one()
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
                    $crate::Ptr::invalid()
                }
            }

            // This is manually implemented so that it is inline and has no newlines, which
            // makes the `Debug` implementation on `Arena` look much nicer.
            impl core::fmt::Debug for $struct_name {
                fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                    f.write_fmt(format_args!(
                        "{}[{:?}]({:?})",
                        stringify!($struct_name),
                        $crate::Ptr::inx(*self),
                        $crate::Ptr::gen(*self),
                    ))
                }
            }

            impl core::fmt::Display for $struct_name {
                fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                    core::fmt::Debug::fmt(self, f)
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

            unsafe impl $crate::Ptr for $struct_name {
                type Inx = $inx_type;
                type Gen = ();

                #[inline]
                fn invalid() -> Self {
                    Self {
                        _internal_inx: $crate::utils::PtrInx::new(
                            <Self::Inx as $crate::utils::PtrInx>::max()
                        ),
                        _internal_gen: $crate::utils::PtrGen::one()
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
                    $crate::Ptr::invalid()
                }
            }

            // This is manually implemented so that it is inline and has no newlines, which
            // makes the `Debug` implementation on `Arena` look much nicer.
            impl core::fmt::Debug for $struct_name {
                fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                    f.write_fmt(format_args!(
                        "{}[{:?}]",
                        stringify!($struct_name),
                        $crate::Ptr::inx(*self),
                    ))
                }
            }

            impl core::fmt::Display for $struct_name {
                fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                    core::fmt::Debug::fmt(self, f)
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

    #[inline]
    fn invalid() -> Self {
        Self {
            _internal_inx: PtrInx::new(
                core::num::NonZeroUsize::new(core::primitive::usize::MAX).unwrap(),
            ),
            _internal_gen: PtrGen::one(),
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

impl<P: Ptr> core::default::Default for PtrNoGen<P> {
    #[inline]
    fn default() -> Self {
        Ptr::invalid()
    }
}

impl<P: Ptr> core::fmt::Debug for PtrNoGen<P> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.write_fmt(format_args!(
            "{}[{:?}]",
            stringify!($struct_name),
            Ptr::inx(*self),
        ))
    }
}

impl<P: Ptr> core::fmt::Display for PtrNoGen<P> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        core::fmt::Debug::fmt(self, f)
    }
}
