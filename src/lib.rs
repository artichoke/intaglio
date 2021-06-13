#![warn(clippy::all)]
#![warn(clippy::pedantic)]
#![warn(clippy::cargo)]
#![allow(clippy::cast_possible_truncation)]
#![allow(unknown_lints)]
#![warn(missing_copy_implementations)]
#![warn(missing_debug_implementations)]
#![warn(missing_docs)]
#![warn(rust_2018_idioms)]
#![warn(trivial_casts, trivial_numeric_casts)]
#![warn(unused_qualifications)]
#![warn(variant_size_differences)]
// Enable feature callouts in generated documentation:
// https://doc.rust-lang.org/beta/unstable-book/language-features/doc-cfg.html
//
// This approach is borrowed from tokio.
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, feature(doc_alias))]

//! This crate provides a library for interning strings.
//!
//! The primary API is a symbol table. Its API is similar to a
//! bimap in that symbols can resolve an underlying string and a string slice
//! can retrieve its associated symbol.
//!
//! For more specific details on the API for interning strings into a symbol
//! table, please see the documentation for the [`SymbolTable`] type.
//!
//! # Examples
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
//! # example().unwrap();
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
//! ownership of the string contents with no additional allocations.
//!
//! # Crate features
//!
//! All features are enabled by default.
//!
//! - **bytes** - Enables an additional symbol table implementation for
//!   interning bytestrings (`Vec<u8>` and `&'static [u8]`).

#![doc(html_root_url = "https://docs.rs/intaglio/1.2.1")]

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

use core::fmt;
use core::mem::size_of;
use core::num::TryFromIntError;
use std::error;

#[cfg(feature = "bytes")]
#[cfg_attr(docsrs, doc(cfg(feature = "bytes")))]
pub mod bytes;
mod convert;
mod eq;
mod internal;
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
#[derive(Default, Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct SymbolOverflowError {
    _private: (),
}

impl SymbolOverflowError {
    /// Construct a new `SymbolOverflowError` with no source.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self { _private: () }
    }

    /// Return the maximum capacity of the [`SymbolTable`] that returned this
    /// error.
    #[inline]
    #[must_use]
    #[allow(clippy::unused_self)]
    pub const fn max_capacity(self) -> usize {
        u32::MAX as usize
    }
}

impl From<TryFromIntError> for SymbolOverflowError {
    #[inline]
    fn from(err: TryFromIntError) -> Self {
        let _ = err;
        Self::new()
    }
}

impl fmt::Display for SymbolOverflowError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Symbol overflow")
    }
}

impl error::Error for SymbolOverflowError {}

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

impl Symbol {
    /// Construct a new `Symbol` from the given `u32`.
    ///
    /// `Symbol`s constructed outside of a [`SymbolTable`] may fail to
    /// resolve to an underlying string using [`SymbolTable::get`].
    ///
    /// `Symbol`s are not constrained to the `SymbolTable` which created them.
    /// No runtime checks ensure that [`SymbolTable::get`] is called with a
    /// `Symbol` that the table itself issued.
    ///
    /// # Examples
    ///
    /// ```
    /// # use intaglio::Symbol;
    /// let sym = Symbol::new(263);
    /// assert_eq!(263, sym.id());
    /// ```
    #[inline]
    #[must_use]
    pub const fn new(sym: u32) -> Self {
        Self(sym)
    }

    /// Return the `u32` identifier from this `Symbol`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use intaglio::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// let sym = table.intern("intaglio")?;
    /// assert_eq!(u32::from(sym), sym.id());
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    #[inline]
    #[must_use]
    pub const fn id(self) -> u32 {
        self.0
    }
}
