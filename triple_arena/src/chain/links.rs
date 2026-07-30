use core::{fmt, hash};

use crate::{fundamental::PtrInx, traits::Ptr};

/// The same as [crate::Link] except that the interlinks do not have a
/// generation counter
pub struct LinkNoGen<P: Ptr, T> {
    // I think the code generation should be overall better if this is done
    pub(crate) prev_next: (Option<P::Inx>, Option<P::Inx>),
    pub t: T,
}

impl<P: Ptr, T> LinkNoGen<P, T> {
    /// Get a `P::Inx` to the previous `LinkNoGen` in the chain before `self`.
    /// Returns `None` if `self` is at the start of the chain.
    pub fn prev(&self) -> Option<P::Inx> {
        self.prev_next.0
    }

    /// Get a `P::Inx` to the next `LinkNoGen` in the chain after `self`.
    /// Returns `None` if `self` is at the end of the chain.
    pub fn next(&self) -> Option<P::Inx> {
        self.prev_next.1
    }

    /// Shorthand for `(self.prev(), self.next())`
    pub fn prev_next(&self) -> (Option<P::Inx>, Option<P::Inx>) {
        self.prev_next
    }

    /// Construct a `LinkNoGen` from its components
    pub fn new(prev_next: (Option<P::Inx>, Option<P::Inx>), t: T) -> Self {
        Self { prev_next, t }
    }

    /// Used in the display and debug impls
    fn fmt_prelude(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("{")?;
        if let Some(p) = self.prev() {
            PtrInx::fmt_hex(p, f)?;
            f.write_str(", ")?;
        } else {
            f.write_str("(start), ")?;
        }
        if let Some(p) = self.next() {
            PtrInx::fmt_hex(p, f)?;
            f.write_str("} ")
        } else {
            f.write_str("(end)} ")
        }
    }
}

impl<P: Ptr, T: fmt::Debug> fmt::Debug for LinkNoGen<P, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_prelude(f)?;
        if f.alternate() {
            f.write_fmt(format_args!("{:#?}", self.t))
        } else {
            f.write_fmt(format_args!("{:?}", self.t))
        }
    }
}

impl<P: Ptr, T: fmt::Display> fmt::Display for LinkNoGen<P, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_prelude(f)?;
        if f.alternate() {
            f.write_fmt(format_args!("{:#}", self.t))
        } else {
            f.write_fmt(format_args!("{:}", self.t))
        }
    }
}

impl<P: Ptr, T: hash::Hash> hash::Hash for LinkNoGen<P, T> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.prev_next.hash(state);
        self.t.hash(state);
    }
}

impl<P: Ptr, T: Clone> Clone for LinkNoGen<P, T> {
    fn clone(&self) -> Self {
        Self {
            prev_next: self.prev_next,
            t: self.t.clone(),
        }
    }
}

impl<P: Ptr, T: Copy> Copy for LinkNoGen<P, T> {}

impl<P: Ptr, T: PartialEq> PartialEq for LinkNoGen<P, T> {
    fn eq(&self, other: &Self) -> bool {
        (self.prev_next == other.prev_next) && (self.t == other.t)
    }
}

impl<P: Ptr, T: Eq> Eq for LinkNoGen<P, T> {}

impl<P: Ptr, T: PartialOrd> PartialOrd for LinkNoGen<P, T> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        match self.prev_next.partial_cmp(&other.prev_next) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        self.t.partial_cmp(&other.t)
    }
}

impl<P: Ptr, T: Ord> Ord for LinkNoGen<P, T> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

/// This represents a link in a `ChainArena` that has a public `t: T` field and
/// `Option<Ptr<P>>` interlinks to the previous and next links.
pub struct Link<P: Ptr, T> {
    // I think the code gen should be overall better if this is done
    pub(crate) prev_next: (Option<P>, Option<P>),
    pub t: T,
}

impl<P: Ptr, T> Link<P, T> {
    /// Get a `Ptr` to the previous `Link` in the chain before `self`. Returns
    /// `None` if `self` is at the start of the chain.
    pub fn prev(&self) -> Option<P> {
        self.prev_next.0
    }

    /// Get a `Ptr` to the next `Link` in the chain after `self`. Returns
    /// `None` if `self` is at the end of the chain.
    pub fn next(&self) -> Option<P> {
        self.prev_next.1
    }

    /// Shorthand for `(self.prev(), self.next())`
    pub fn prev_next(&self) -> (Option<P>, Option<P>) {
        self.prev_next
    }

    /// Construct a `Link` from its components
    pub fn new(prev_next: (Option<P>, Option<P>), t: T) -> Self {
        Self { prev_next, t }
    }

    /// Convert `self` to a `LinkNoGen`
    pub fn no_gen(self) -> LinkNoGen<P, T> {
        LinkNoGen {
            prev_next: (
                self.prev_next.0.map(|p| p.inx()),
                self.prev_next.1.map(|p| p.inx()),
            ),
            t: self.t,
        }
    }

    /// Convert `&self` to a `LinkNoGen<P, &T>`
    pub fn no_gen_ref(&self) -> LinkNoGen<P, &T> {
        LinkNoGen {
            prev_next: (
                self.prev_next.0.map(|p| p.inx()),
                self.prev_next.1.map(|p| p.inx()),
            ),
            t: &self.t,
        }
    }
}

impl<P: Ptr, T: fmt::Debug> fmt::Debug for Link<P, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.no_gen_ref(), f)
    }
}

impl<P: Ptr, T: fmt::Display> fmt::Display for Link<P, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.no_gen_ref(), f)
    }
}

impl<P: Ptr, T: hash::Hash> hash::Hash for Link<P, T> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.prev_next.hash(state);
        self.t.hash(state);
    }
}

impl<P: Ptr, T: Clone> Clone for Link<P, T> {
    fn clone(&self) -> Self {
        Self {
            prev_next: self.prev_next,
            t: self.t.clone(),
        }
    }
}

impl<P: Ptr, T: Copy> Copy for Link<P, T> {}

impl<P: Ptr, T: PartialEq> PartialEq for Link<P, T> {
    fn eq(&self, other: &Self) -> bool {
        (self.prev_next == other.prev_next) && (self.t == other.t)
    }
}

impl<P: Ptr, T: Eq> Eq for Link<P, T> {}

impl<P: Ptr, T: PartialOrd> PartialOrd for Link<P, T> {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        match self.prev_next.partial_cmp(&other.prev_next) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        self.t.partial_cmp(&other.t)
    }
}

impl<P: Ptr, T: Ord> Ord for Link<P, T> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}
