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
#![warn(unsafe_op_in_unsafe_fn)]
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
//! The primary API is a symbol table. Its API is similar to a bimap in that
//! symbols can resolve an underlying string and a string slice can retrieve
//! its associated symbol.
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
//! memory usage such as [`SymbolTable::reserve`] and [`SymbolTable::shrink_to_fit`].
//!
//! [`SymbolTable::intern`] does not clone or copy interned strings. It takes
//! ownership of the string contents with no additional allocations.
//!
//! # Types of Interners
//!
//! Intaglio includes multiple symbol tables which differ in the types of strings
//! they allow you to intern.
//!
//! - [`SymbolTable`] interns UTF-8 strings: [`String`] and [`&str`](prim@str).
//! - [`bytes::SymbolTable`] interns binary strings: [`Vec<u8>`] and `&[u8]`.
//! - [`cstr::SymbolTable`] interns C strings: [`CString`] and [`&CStr`].
//! - [`osstr::SymbolTable`] interns platform strings: [`OsString`] and [`&OsStr`].
//! - [`path::SymbolTable`] interns path strings: [`PathBuf`] and [`&Path`].
//!
//! # Crate features
//!
//! All features are enabled by default.
//!
//! - **bytes** - Enables an additional symbol table implementation for interning
//!   byte strings ([`Vec<u8>`] and `&'static [u8]`).
//! - **cstr** - Enables an additional symbol table implementation for interning
//!   C strings ([`CString`] and [`&'static CStr`]).
//! - **osstr** - Enables an additional symbol table implementation for interning
//!   platform strings ([`OsString`] and [`&'static OsStr`]).
//! - **path** - Enables an additional symbol table implementation for interning
//!   path strings ([`PathBuf`] and [`&'static Path`]).
//!
//! [`Vec<u8>`]: std::vec::Vec
//! [`CString`]: std::ffi::CString
//! [`&CStr`]: std::ffi::CStr
//! [`&'static CStr`]: std::ffi::CStr
//! [`OsString`]: std::ffi::OsString
//! [`&OsStr`]: std::ffi::OsStr
//! [`&'static OsStr`]: std::ffi::OsStr
//! [`PathBuf`]: std::path::PathBuf
//! [`&Path`]: std::path::Path
//! [`&'static Path`]: std::path::Path

#![doc(html_root_url = "https://docs.rs/intaglio/1.5.0")]

// Ensure code blocks in README.md compile
#[cfg(all(doctest, feature = "bytes", feature = "cstr", feature = "path"))]
#[doc = include_str!("../README.md")]
mod readme {}

use core::fmt;
use core::mem::size_of;
use core::num::TryFromIntError;
use std::error;

#[cfg(feature = "bytes")]
#[cfg_attr(docsrs, doc(cfg(feature = "bytes")))]
pub mod bytes;
mod convert;
#[cfg(feature = "cstr")]
#[cfg_attr(docsrs, doc(cfg(feature = "cstr")))]
pub mod cstr;
mod eq;
mod internal;
#[cfg(feature = "osstr")]
#[cfg_attr(docsrs, doc(cfg(feature = "osstr")))]
pub mod osstr;
#[cfg(feature = "path")]
#[cfg_attr(docsrs, doc(cfg(feature = "path")))]
pub mod path;
mod str;

pub use crate::str::*;

// To prevent overflows when indexing into the backing `Vec`, `intaglio`
// requires `usize` to be at least as big as `u32`.
//
// This const-evaluated expression will fail to compile if this invariant does
// not hold.
const _: () = [()][!(size_of::<usize>() >= size_of::<u32>()) as usize];

/// Default capacity for a new [`SymbolTable`] created with
/// [`SymbolTable::new`].
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
        // The valid representation of `Symbol` is:
        //
        // ```
        // Symbol(0_u32)..=Symbol(u32::MAX)
        // ```
        //
        // The length of a range from `0..uX::MAX` is `uX::MAX + 1`.
        u32::MAX as usize + 1
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
#[repr(transparent)]
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Symbol(u32);

impl Symbol {
    /// Construct a new `Symbol` from the given `u32`.
    ///
    /// `Symbol`s constructed outside a [`SymbolTable`] may fail to resolve to
    /// an underlying string using [`SymbolTable::get`].
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

#[cfg(test)]
mod tests {
    use super::SymbolOverflowError;

    #[test]
    #[cfg(not(miri))]
    fn max_capacity_is_length_of_symbol_range() {
        let symbol_range = 0_u32..=u32::MAX;
        let len = symbol_range.size_hint().0;
        assert_eq!(SymbolOverflowError::new().max_capacity(), len);
        let len = symbol_range.size_hint().1.unwrap();
        assert_eq!(SymbolOverflowError::new().max_capacity(), len);
    }
}
