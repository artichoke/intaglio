#![warn(clippy::all)]
#![warn(clippy::pedantic)]
#![warn(clippy::cargo)]
#![allow(clippy::cast_possible_truncation)]
#![warn(missing_docs, intra_doc_link_resolution_failure)]
#![warn(missing_debug_implementations)]
#![warn(missing_copy_implementations)]
#![warn(rust_2018_idioms)]
#![warn(trivial_casts, trivial_numeric_casts)]
#![warn(unused_qualifications)]
#![warn(variant_size_differences)]

//! This crate provides a library for interning strings.
//!
//! The primary API is a symbol table. Its API is similar to a
//! bimap in that symbols can resolve an underlying string and a string slice
//! can retrieve its associated symbol.
//!
//! For more specific details on the API for interning strings into a symbol
//! table, please see the documentation for the [`SymbolTable`] type.
//!
//! # Example
//!
//! ```
//! # use intaglio::SymbolTable;
//! # fn example() -> Result<(), Box<dyn std::error::Error>> {
//! let mut table = SymbolTable::new();
//! let sym_id = table.intern("abc")?;
//! assert_eq!(sym_id, table.intern("abc".to_string())?);
//! assert!(table.contains(sym_id));
//! assert!(table.is_interned("abc"));
//! # Ok(())
//! # }
//! ```
//!
//! # String interning
//!
//! Intaglio `SymbolTable`s store at most one copy of a string. All requests to
//! intern a string that is already present in the table, regardless of whether
//! the string is an owned `String` or borrowed `&'static str`, will return the
//! same immutable [`Symbol`].
//!
//! [`Symbol`]s are `u32` indexes into a `SymbolTable` that are cheap to
//! compare, copy, store, and send.
//!
//! # Allocations
//!
//! `SymbolTable` exposes several constructors for tuning the initial allocated
//! size of the table. It also exposes several APIs for tuning the table's
//! memory usage such as [`SymbolTable::reserve`] and
//! [`SymbolTable::shrink_to_fit`].
//!
//! [`SymbolTable::intern`] does not clone or copy interned strings. It takes
//! ownership of the string contents with no additional allocations. Owned
//! strings are leaked with [`Box::leak`] and recovered and deallocated when the
//! table is dropped.
//!
//! # Crate features
//!
//! All features are enabled by default.
//!
//! - **bytes** - Enables an additional symbol table implementation for
//!   interning bytestrings (`Vec<u8>` and `&'static [u8]`). Disabling this
//!   drops the `bstr` dependency.

#![doc(html_root_url = "https://docs.rs/intaglio/1.0.1")]

// Ensure code blocks in README.md compile
#[cfg(doctest)]
macro_rules! readme {
    ($x:expr) => {
        #[doc = $x]
        mod readme {}
    };
    () => {
        readme!(include_str!("../README.md"));
    };
}
#[cfg(all(doctest, feature = "bytes"))]
readme!();

use core::convert::TryFrom;
use core::fmt;
use core::mem::size_of;
use core::num::{NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize, TryFromIntError};
use std::error;

#[cfg(feature = "bytes")]
pub mod bytes;
mod str;

pub use crate::str::*;

// To prevent overflows when indexing into the backing `Vec`, `intaglio`
// requires `usize` to be at least as big as `u32`.
//
// This const-evaluated expression will fail to compile if this invariant does
// not hold.
const _: () = [()][!(size_of::<usize>() >= size_of::<u32>()) as usize];

/// Default capacity for new a [`SymbolTable`].
pub const DEFAULT_SYMBOL_TABLE_CAPACITY: usize = 4096;

/// Error returned when a [`SymbolTable`] or symbol identifier overflows.
///
/// `SymbolTable` uses `u32` identifiers for symbols to save space. If more than
/// `u32::MAX` symbols are stored in the table, no more identifiers can be
/// generated. Any subsequent inserts into the table will fail with this error.
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub struct SymbolOverflowError {
    source: Option<TryFromIntError>,
}

impl SymbolOverflowError {
    /// Construct a new `SymbolOverflowError` with no source.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Return the maximum capacity of the [`SymbolTable`] that returned this
    /// error.
    #[must_use]
    #[allow(clippy::unused_self)]
    pub fn max_capacity(self) -> usize {
        u32::MAX as usize
    }
}

impl From<TryFromIntError> for SymbolOverflowError {
    fn from(err: TryFromIntError) -> Self {
        Self { source: Some(err) }
    }
}

impl fmt::Display for SymbolOverflowError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Symbol overflow")
    }
}

impl error::Error for SymbolOverflowError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        if let Some(ref source) = self.source {
            Some(source)
        } else {
            None
        }
    }
}

/// Identifier bound to an interned string.
///
/// [`SymbolTable`] is guaranteed to return an equivalent `Symbol` each time
/// an equivalent string is interned.
///
/// A `Symbol` allows retrieving a reference to the original interned string.
///
/// `Symbol`s are based on a `u32` index.
///
/// `Symbol`s are not constrained to the `SymbolTable` which created them.  No
/// runtime checks ensure that [`SymbolTable::get`] is called with a `Symbol`
/// that the table itself issued.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Symbol(u32);

impl From<u8> for Symbol {
    fn from(sym: u8) -> Self {
        Self(sym.into())
    }
}

impl From<NonZeroU8> for Symbol {
    fn from(sym: NonZeroU8) -> Self {
        Self(sym.get().into())
    }
}

impl From<u16> for Symbol {
    fn from(sym: u16) -> Self {
        Self(sym.into())
    }
}

impl From<NonZeroU16> for Symbol {
    fn from(sym: NonZeroU16) -> Self {
        Self(sym.get().into())
    }
}

impl From<u32> for Symbol {
    fn from(sym: u32) -> Self {
        Self(sym)
    }
}

impl From<NonZeroU32> for Symbol {
    fn from(sym: NonZeroU32) -> Self {
        Self(sym.get())
    }
}

impl TryFrom<u64> for Symbol {
    type Error = SymbolOverflowError;

    fn try_from(value: u64) -> Result<Self, Self::Error> {
        let id = u32::try_from(value)?;
        Ok(id.into())
    }
}

impl TryFrom<NonZeroU64> for Symbol {
    type Error = SymbolOverflowError;

    fn try_from(value: NonZeroU64) -> Result<Self, Self::Error> {
        let id = u32::try_from(value.get())?;
        Ok(id.into())
    }
}

impl TryFrom<usize> for Symbol {
    type Error = SymbolOverflowError;

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        let id = u32::try_from(value)?;
        Ok(id.into())
    }
}

impl TryFrom<NonZeroUsize> for Symbol {
    type Error = SymbolOverflowError;

    fn try_from(value: NonZeroUsize) -> Result<Self, Self::Error> {
        let id = u32::try_from(value.get())?;
        Ok(id.into())
    }
}

impl From<Symbol> for u32 {
    fn from(sym: Symbol) -> Self {
        sym.0
    }
}

impl From<Symbol> for u64 {
    fn from(sym: Symbol) -> Self {
        sym.0.into()
    }
}

impl From<Symbol> for usize {
    fn from(sym: Symbol) -> Self {
        sym.0 as usize
    }
}

impl Symbol {
    /// Construct a new `Symbol` from the given `u32`.
    ///
    /// `Symbol`s constructed outside of a [`SymbolTable`] may fail to
    /// resolve to an underlying string using [`SymbolTable::get`].
    ///
    /// `Symbol`s are not constrained to the `SymbolTable` which created them.
    /// No runtime checks ensure that [`SymbolTable::get`] is called with a
    /// `Symbol` that the table itself issued.
    #[must_use]
    pub fn new(sym: u32) -> Self {
        Self::from(sym)
    }
}
