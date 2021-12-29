use core::{fmt, hash::Hash, num::NonZeroU64};

/// Note: The `PartialEq` implementation is used for generation value
/// comparison. When implementing this trait manually, `#[inline]` should be
/// applied to all these functions.
pub trait PtrTrait: fmt::Debug + Hash + Clone + Copy + PartialEq + Eq + PartialOrd + Ord {
    /// Used by the Debug implementation of `Ptr<P>`
    fn ptr_debug_str() -> &'static str;

    /// If there is a generation value, this should assume `_gen.is_some()`
    /// and create `Self` with the given `NonZeroU64`. Otherwise, the
    /// argument can be ignored.
    fn new(_gen: Option<NonZeroU64>) -> Self;

    /// This should always return `None` if there is no generation value
    /// associated with the struct this trait is being implemented for.
    /// Otherwise, this should always return a mutable reference to a plain
    /// internal `NonZeroU64`.
    fn get_mut(this: &mut Self) -> Option<&mut NonZeroU64>;

    /// Same as `get_mut`, but with no reference
    fn get(this: &Self) -> Option<NonZeroU64>;
}

/// Convenience macro for quickly making new unit structs that implement
/// `PtrTrait` _without_ a generation value. Each struct name can be followed by
/// a comma separated list of attributes, and structs are separated by
/// semicolons.
///
/// ```
/// use triple_arena::prelude::*;
///
/// ptr_trait_struct!(
///     P0 doc="An example struct `P0` that implements `PtrTrait`";
///     Example2 doc="Another struct. ", doc="Another doc attribute."
/// );
///
/// let _: Arena<P0, String>;
/// ```
#[macro_export]
macro_rules! ptr_trait_struct {
    ($($struct_name:ident $($attributes:meta),*);*) => {
        $(
            $(#[$attributes])*
            #[derive(
                core::fmt::Debug,
                core::hash::Hash,
                core::clone::Clone,
                core::marker::Copy,
                core::cmp::PartialEq,
                core::cmp::Eq,
                core::cmp::PartialOrd,
                core::cmp::Ord
            )]
            pub struct $struct_name {}

            impl triple_arena::PtrTrait for $struct_name {
                #[inline]
                fn ptr_debug_str() -> &'static str {
                    stringify!($struct_name)
                }

                #[inline]
                fn new(_gen: Option<core::num::NonZeroU64>) -> Self {
                    Self {}
                }

                #[inline]
                fn get_mut(this: &mut Self) -> Option<&mut core::num::NonZeroU64> {
                    None
                }

                #[inline]
                fn get(this: &Self) -> Option<core::num::NonZeroU64> {
                    None
                }
            }
        )*
    };
}

/// Convenience macro for quickly making new unit structs that implement
/// `PtrTrait` with a generation value. Each struct name can be followed by a
/// comma separated list of attributes, and structs are separated by semicolons.
///
/// ```
/// use triple_arena::prelude::*;
///
/// ptr_trait_struct_with_gen!(
///     P0 doc="An example struct `P0` that implements `PtrTrait`";
///     Example2 doc="Another struct. ", doc="Another doc attribute."
/// );
///
/// let _: Arena<Example2, String>;
/// ```
#[macro_export]
macro_rules! ptr_trait_struct_with_gen {
    ($($struct_name:ident $($attributes:meta),*);*) => {
        $(
            $(#[$attributes])*
            #[derive(
                core::fmt::Debug,
                core::hash::Hash,
                core::clone::Clone,
                core::marker::Copy,
                core::cmp::PartialEq,
                core::cmp::Eq,
                core::cmp::PartialOrd,
                core::cmp::Ord
            )]
            pub struct $struct_name {
                _internal_value: core::num::NonZeroU64
            }

            impl triple_arena::PtrTrait for $struct_name {
                #[inline]
                fn ptr_debug_str() -> &'static str {
                    stringify!($struct_name)
                }

                #[inline]
                fn new(_gen: Option<core::num::NonZeroU64>) -> Self {
                    Self {
                        _internal_value: _gen.unwrap()
                    }
                }

                #[inline]
                fn get_mut(this: &mut Self) -> Option<&mut core::num::NonZeroU64> {
                    Some(&mut this._internal_value)
                }

                #[inline]
                fn get(this: &Self) -> Option<core::num::NonZeroU64> {
                    Some(this._internal_value)
                }
            }
        )*
    };
}

/// An arena pointer returned from an `Arena<T, P>`. Different `P` can be used
/// to leverage the type system to distinguish between `Ptr`s from different
/// arenas. If `P` has a generation value, a `Ptr<P>` will keep the generation
/// information for later arena accesses to determine if the pointer has been
/// invalidated.
#[derive(Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Ptr<P: PtrTrait> {
    gen: P,
    raw: usize,
}

impl<P: PtrTrait> Ptr<P> {
    #[inline]
    pub(crate) fn from_raw(p: usize, gen: Option<NonZeroU64>) -> Self {
        Ptr {
            gen: PtrTrait::new(gen),
            raw: p,
        }
    }

    #[inline]
    pub(crate) fn get_raw(self) -> usize {
        self.raw
    }

    /// Returns a new `Ptr<P>` with a generation value (if it exists) set to 1.
    /// Because the arena starts with generation 2, this is guaranteed invalid
    /// when generation counters are used. The raw index is also set to
    /// `usize::MAX`.
    #[inline]
    pub fn invalid() -> Self {
        Self::from_raw(usize::MAX, Some(NonZeroU64::new(1).unwrap()))
    }

    /// Return the generation of `self` as a `P`
    #[inline]
    pub fn gen_p(self) -> P {
        self.gen
    }

    /// Return the generation of `self` as a `Option<NonZeroU64>`
    #[inline]
    pub fn gen_nz(self) -> Option<NonZeroU64> {
        PtrTrait::get(&self.gen)
    }
}

// This is manually implemented so that it is inline and has no newlines, which
// makes the `Debug` implementation on `Arena` look much nicer.
impl<P: PtrTrait> fmt::Debug for Ptr<P> {
    /// Formats as `Ptr<{P::ptr_debug_str()}>({raw index})[{generation}]` (if
    /// generation number is included), or
    /// `Ptr<{P::ptr_debug_str()}>({raw index})`
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(gen) = self.gen_nz() {
            f.write_fmt(format_args!(
                "Ptr<{}>({})[{}]",
                P::ptr_debug_str(),
                self.get_raw(),
                gen
            ))
        } else {
            f.write_fmt(format_args!(
                "Ptr<{}>({})",
                P::ptr_debug_str(),
                self.get_raw(),
            ))
        }
    }
}

impl<P: PtrTrait> fmt::Display for Ptr<P> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}
