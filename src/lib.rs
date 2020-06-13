#![warn(clippy::all)]
#![warn(clippy::pedantic)]
#![allow(clippy::cast_possible_truncation)] // see `_U32_FITS_IN_USIZE_ASSERTION`
#![warn(clippy::cargo)]
#![warn(missing_docs, intra_doc_link_resolution_failure)]
#![warn(missing_debug_implementations)]
#![warn(rust_2018_idioms)]

//! Intaglio
//!
//! This crate is a bytestring interner.
//!
//! > String interning is a method of storing only one copy of each distinct
//! > string value, which must be immutable.
//!
//! Intaglio exports [`SymbolTable`] which stores at most one copy of a
//! bytestring. All requests to intern an `Eq` bytestring, regardless of whether
//! the bytestring is an owned `Vec<u8>` or borrowed `&'static [u8]` will hand
//! back the same immutable [`SymbolId`].
//!
//! [`SymbolId`]s are u32 indexes into the [`SymbolTable`] that are cheap to
//! compare and copy.
//!
//! # Allocations
//!
//! Intaglio's [`SymbolTable`] is backed by a [`Vec`] and [`HashMap`] which grow
//! to accommodate growth in the number of stored bytestrings.
//!
//! [`SymbolTable::intern`] does not clone or copy interned bytes and takes
//! ownership of the bytestrings with no additional allocations.
//!
//! # Usage
//!
//! ```
//! # use intaglio::SymbolTable;
//! # fn example() -> Result<(), Box<dyn std::error::Error>> {
//! let mut table = SymbolTable::new();
//! let sym_id = table.intern(&b"abc"[..])?;
//! assert_eq!(sym_id, table.intern(b"abc".to_vec())?);
//! assert!(table.contains(sym_id));
//! assert!(table.is_interned(b"abc"));
//! # Ok(())
//! # }
//! ```

#![doc(html_root_url = "https://docs.rs/intaglio/0.1.0")]

#[cfg(doctest)]
doc_comment::doctest!("../README.md");

use bstr::{BStr, ByteSlice};
use std::borrow::{Borrow, Cow};
use std::cmp;
use std::collections::hash_map::RandomState;
use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use std::error;
use std::fmt;
use std::hash::{BuildHasher, Hash, Hasher};
use std::iter::{self, FusedIterator};
use std::marker::PhantomData;
use std::mem::{self, size_of};
use std::num::{NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize, TryFromIntError};
use std::ops::{Deref, Range, RangeInclusive};
use std::slice;

/// An intaglio interner for UTF-8 strings.
pub mod str;

// To prevent overflows when indexing into the backing `Vec`, `intaglio`
// requires `usize` to be at least as big as `u32`.
//
// This const-evaluated expression will fail to compile if this invariant does
// not hold.
const _U32_FITS_IN_USIZE_ASSERTION: &[()] = &[(); size_of::<usize>() - size_of::<u32>()];

/// Default capacity for new a [`SymbolTable`].
pub const DEFAULT_SYMBOL_TABLE_CAPACITY: usize = 4096;

/// Error returned when a [`SymbolTable`] or symbol identifier overflows.
///
/// `SymbolTable` uses `u32` identifiers for symbols to save space. If more than
/// `u32::MAX` symbols are stored in the table, no more identifiers can be
/// generated. Any subsequent inserts into the table will fail with this error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SymbolIdOverflowError {
    max_capacity: usize,
    source: TryFromIntError,
}

impl SymbolIdOverflowError {
    /// Return the maximum capacity of the [`SymbolTable`] that returned this
    /// error.
    #[must_use]
    pub fn max_capacity(self) -> usize {
        self.max_capacity
    }
}

impl From<TryFromIntError> for SymbolIdOverflowError {
    fn from(err: TryFromIntError) -> Self {
        Self {
            max_capacity: u32::MAX as usize,
            source: err,
        }
    }
}

impl fmt::Display for SymbolIdOverflowError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Symbol ID overflow")
    }
}

impl error::Error for SymbolIdOverflowError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        Some(&self.source)
    }
}

/// Identifier bound to an interned bytestring.
///
/// [`SymbolTable`] is guaranteed to return an equivalent `SymbolId` each time
/// an equivalent `&[u8]` is interned.
///
/// A `SymbolId` allows retrieving a reference to the original interned
/// bytestring.
///
/// `SymbolId`s are based on a `u32` index.
///
/// `SymbolId`s are not associated with the `SymbolTable` which created them. No
/// runtime checks ensure that [`SymbolTable::get`] is called with a `SymbolId`
/// that the table itself issued.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct SymbolId(u32);

impl From<u8> for SymbolId {
    fn from(sym: u8) -> Self {
        Self(sym.into())
    }
}

impl From<NonZeroU8> for SymbolId {
    fn from(sym: NonZeroU8) -> Self {
        Self(sym.get().into())
    }
}

impl From<u16> for SymbolId {
    fn from(sym: u16) -> Self {
        Self(sym.into())
    }
}

impl From<NonZeroU16> for SymbolId {
    fn from(sym: NonZeroU16) -> Self {
        Self(sym.get().into())
    }
}

impl From<u32> for SymbolId {
    fn from(sym: u32) -> Self {
        Self(sym)
    }
}

impl From<NonZeroU32> for SymbolId {
    fn from(sym: NonZeroU32) -> Self {
        Self(sym.get())
    }
}

impl TryFrom<u64> for SymbolId {
    type Error = SymbolIdOverflowError;

    fn try_from(value: u64) -> Result<Self, Self::Error> {
        let id = u32::try_from(value)?;
        Ok(id.into())
    }
}

impl TryFrom<NonZeroU64> for SymbolId {
    type Error = SymbolIdOverflowError;

    fn try_from(value: NonZeroU64) -> Result<Self, Self::Error> {
        let id = u32::try_from(value.get())?;
        Ok(id.into())
    }
}

impl TryFrom<usize> for SymbolId {
    type Error = SymbolIdOverflowError;

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        let id = u32::try_from(value)?;
        Ok(id.into())
    }
}

impl TryFrom<NonZeroUsize> for SymbolId {
    type Error = SymbolIdOverflowError;

    fn try_from(value: NonZeroUsize) -> Result<Self, Self::Error> {
        let id = u32::try_from(value.get())?;
        Ok(id.into())
    }
}

impl From<SymbolId> for u32 {
    fn from(sym: SymbolId) -> Self {
        sym.0
    }
}

impl From<SymbolId> for u64 {
    fn from(sym: SymbolId) -> Self {
        sym.0.into()
    }
}

impl From<SymbolId> for usize {
    fn from(sym: SymbolId) -> Self {
        sym.0 as usize
    }
}

impl SymbolId {
    /// Construct a new `SymbolId` from the given `u32`.
    ///
    /// `SymbolId`s constructed outside of a [`SymbolTable`] may fail to
    /// resolve to an underlying bytestring using [`SymbolTable::get`].
    ///
    /// `SymbolId`s are not associated with the `SymbolTable` which created
    /// them. No runtime checks ensure that [`SymbolTable::get`] is called with
    /// a `SymbolId` that the table itself issued.
    #[must_use]
    pub fn new(sym: u32) -> Self {
        Self::from(sym)
    }
}

/// Wrapper around `&'static [u8]` that supports deallocating references created
/// via [`Box::leak`].
///
/// # Safety
///
/// Must not be `Clone` or `Copy` because the Drop logic assumes this enum is the
/// unique owner of a leaked boxed slice. The lack of `Clone` and `Copy` impls is
/// necessary to prevent double frees.
#[derive(Debug)]
enum Slice {
    /// True 'static references.
    Static(&'static BStr),
    /// 'static references created by [`Box::leak`].
    ///
    /// These references can be deallocated by coercing the reference to a
    /// pointer and reconstituting the `Box` with [`Box::from_raw`] on drop.
    Leaked(&'static BStr),
}

impl Slice {
    /// Return a reference to the inner 'static byteslice.
    fn as_slice(&self) -> &'static [u8] {
        match self {
            Self::Static(global) => global,
            Self::Leaked(leaked) => leaked,
        }
    }
}

impl Default for Slice {
    fn default() -> Self {
        Self::Static(<_>::default())
    }
}

impl Drop for Slice {
    fn drop(&mut self) {
        // If the slice was created via `Box::leak`, turn it back into a boxed
        // slice and drop it to free the underlying bytes.
        //
        // Safety:
        //
        // Do not `mem::take(self)` to move out the leaked slice. This causes a
        // double free reported by miri.
        //
        // Instead, replace the contents of the `Leaked` variant with a truly
        // &'static [u8] that can be safely dropped when it goes out of scope.
        if let Slice::Leaked(mut slice) = self {
            // Move the leaked &'static mut [u8] out of the leaked variant and
            // replace with a truly static empty "".
            let slice = mem::take(&mut slice).as_ref();
            // Safety:
            //
            // `slice` contained in `Slice::Leaked(_)` was created by
            // `Box::leak` which returns `&'static mut [u8]` which is uniquely
            // owned by this enum.
            //
            // Copies of this reference are handed out by `SymbolTable::get`,
            // but they have lifetime bound to the `SymbolTable`. This drop can
            // only occur while the `SymbolTable` is being dropped which
            // requires unique access and thus no outstanding borrows of this
            // reference.
            let boxed = unsafe { Box::from_raw(slice as *const [u8] as *mut [u8]) };
            drop(boxed);
        }
    }
}

impl Deref for Slice {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl PartialEq<Slice> for Slice {
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl PartialEq<[u8]> for Slice {
    fn eq(&self, other: &[u8]) -> bool {
        self.as_slice() == other
    }
}

impl PartialEq<Slice> for [u8] {
    fn eq(&self, other: &Slice) -> bool {
        self == other.as_slice()
    }
}

impl PartialEq<Vec<u8>> for Slice {
    fn eq(&self, other: &Vec<u8>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl PartialEq<Slice> for Vec<u8> {
    fn eq(&self, other: &Slice) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl Eq for Slice {}

impl Hash for Slice {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

impl Borrow<[u8]> for Slice {
    fn borrow(&self) -> &[u8] {
        self.as_slice()
    }
}

impl Borrow<[u8]> for &Slice {
    fn borrow(&self) -> &[u8] {
        self.as_slice()
    }
}

impl Borrow<[u8]> for &mut Slice {
    fn borrow(&self) -> &[u8] {
        self.as_slice()
    }
}

/// An iterator over all [`SymbolId`]s in a [`SymbolTable`].
///
/// # Usage
///
/// ```
/// # use intaglio::SymbolTable;
/// # fn example() -> Result<(), Box<dyn std::error::Error>> {
/// let mut table = SymbolTable::new();
/// let sym_id = table.intern(&b"abc"[..])?;
/// let all_symbols = table.all_symbols();
/// assert_eq!(vec![sym_id], all_symbols.collect::<Vec<_>>());
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct AllSymbols<'a> {
    // this Result is being used as an Either type.
    range: Result<Range<u32>, RangeInclusive<u32>>,
    // Hold a shared reference to the underlying `SymbolTable` to ensure the
    // table is not modified while we are iterating which would make the results
    // not match the real state.
    phantom: PhantomData<&'a SymbolTable>,
}

impl<'a> Iterator for AllSymbols<'a> {
    type Item = SymbolId;

    fn next(&mut self) -> Option<Self::Item> {
        match self.range {
            Ok(ref mut range) => range.next().map(SymbolId::from),
            Err(ref mut range) => range.next().map(SymbolId::from),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self.range {
            Ok(ref range) => range.size_hint(),
            Err(ref range) => range.size_hint(),
        }
    }

    fn count(self) -> usize
    where
        Self: Sized,
    {
        match self.range {
            Ok(range) => range.count(),
            Err(range) => range.count(),
        }
    }

    fn last(self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        match self.range {
            Ok(range) => range.last().map(SymbolId::from),
            Err(range) => range.last().map(SymbolId::from),
        }
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        match self.range {
            Ok(ref mut range) => range.nth(n).map(SymbolId::from),
            Err(ref mut range) => range.nth(n).map(SymbolId::from),
        }
    }

    fn collect<B: iter::FromIterator<Self::Item>>(self) -> B
    where
        Self: Sized,
    {
        match self.range {
            Ok(range) => range.map(SymbolId::from).collect(),
            Err(range) => range.map(SymbolId::from).collect(),
        }
    }
}

impl<'a> DoubleEndedIterator for AllSymbols<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self.range {
            Ok(ref mut range) => range.next_back().map(SymbolId::from),
            Err(ref mut range) => range.next_back().map(SymbolId::from),
        }
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        match self.range {
            Ok(ref mut range) => range.nth_back(n).map(SymbolId::from),
            Err(ref mut range) => range.nth_back(n).map(SymbolId::from),
        }
    }
}

impl<'a> FusedIterator for AllSymbols<'a> {}

/// An iterator over all interned bytestrings in a [`SymbolTable`].
///
/// # Usage
///
/// ```
/// # use intaglio::SymbolTable;
/// # fn example() -> Result<(), Box<dyn std::error::Error>> {
/// let mut table = SymbolTable::new();
/// let sym_id = table.intern(b"abc".to_vec())?;
/// let bytestrings = table.bytestrings();
/// assert_eq!(vec![&b"abc"[..]], bytestrings.collect::<Vec<_>>());
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone)]
pub struct Bytestrings<'a>(slice::Iter<'a, Slice>);

impl<'a> Iterator for Bytestrings<'a> {
    type Item = &'a [u8];

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(Deref::deref)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }

    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.0.count()
    }

    fn last(self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.0.last().map(Deref::deref)
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.0.nth(n).map(Deref::deref)
    }

    fn collect<B: iter::FromIterator<Self::Item>>(self) -> B
    where
        Self: Sized,
    {
        self.0.map(Deref::deref).collect()
    }
}

impl<'a> DoubleEndedIterator for Bytestrings<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(Deref::deref)
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.0.nth_back(n).map(Deref::deref)
    }

    fn rfold<B, F>(self, accum: B, f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.0.map(Deref::deref).rfold(accum, f)
    }
}

impl<'a> ExactSizeIterator for Bytestrings<'a> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<'a> FusedIterator for Bytestrings<'a> {}

/// An iterator over all symbols and interned bytestrings in a [`SymbolTable`].
///
/// # Usage
///
/// ```
/// # use std::collections::HashMap;
/// # use intaglio::{SymbolId, SymbolTable};
/// # fn example() -> Result<(), Box<dyn std::error::Error>> {
/// let mut table = SymbolTable::new();
/// let sym_id = table.intern(b"abc".to_vec())?;
/// let iter = table.iter();
/// let mut map = HashMap::new();
/// map.insert(SymbolId::new(0), &b"abc"[..]);
/// assert_eq!(map, iter.collect::<HashMap<_, _>>());
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone)]
pub struct Iter<'a>(iter::Zip<AllSymbols<'a>, Bytestrings<'a>>);

impl<'a> Iterator for Iter<'a> {
    type Item = (SymbolId, &'a [u8]);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }

    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.0.count()
    }

    fn last(self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.0.last()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.0.nth(n)
    }

    fn collect<B: iter::FromIterator<Self::Item>>(self) -> B
    where
        Self: Sized,
    {
        self.0.collect()
    }
}

impl<'a> FusedIterator for Iter<'a> {}

impl<'a> IntoIterator for &'a SymbolTable {
    type Item = (SymbolId, &'a [u8]);
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Byte string interner.
///
/// This symbol table is implemented by leaking bytestrings with a fast path for
/// `&[u8]` that are already 'static.
///
/// # Usage
///
/// ```
/// # use intaglio::SymbolTable;
/// # fn example() -> Result<(), Box<dyn std::error::Error>> {
/// let mut table = SymbolTable::new();
/// let sym_id = table.intern(&b"abc"[..])?;
/// assert_eq!(sym_id, table.intern(b"abc".to_vec())?);
/// assert!(table.contains(sym_id));
/// assert!(table.is_interned(b"abc"));
/// # Ok(())
/// # }
/// ```
#[derive(Default, Debug)]
pub struct SymbolTable<S = RandomState> {
    map: HashMap<&'static BStr, SymbolId, S>,
    vec: Vec<Slice>,
}

impl SymbolTable<RandomState> {
    /// Constructs a new, empty `SymbolTable` with
    /// [default capacity](DEFAULT_SYMBOL_TABLE_CAPACITY).
    ///
    /// # Examples
    ///
    /// ```
    /// # use intaglio::SymbolTable;
    /// let table = SymbolTable::new();
    /// assert_eq!(0, table.len());
    /// assert!(table.capacity() >= 4096);
    /// ```
    #[must_use]
    pub fn new() -> Self {
        Self::with_capacity(DEFAULT_SYMBOL_TABLE_CAPACITY)
    }

    /// Constructs a new, empty `SymbolTable` with the specified capacity.
    ///
    /// The symbol table will be able to hold at least `capacity` bytestrings
    /// without reallocating. If `capacity` is 0, the symbol table will not
    /// allocate.
    ///
    /// # Examples
    ///
    /// ```
    /// # use intaglio::SymbolTable;
    /// let table = SymbolTable::with_capacity(10);
    /// assert_eq!(0, table.len());
    /// assert!(table.capacity() >= 10);
    /// ```
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        let capacity = capacity.next_power_of_two();
        Self {
            map: HashMap::with_capacity(capacity),
            vec: Vec::with_capacity(capacity),
        }
    }
}

impl<S> SymbolTable<S> {
    /// Constructs a new, empty `SymbolTable` with
    /// [default capacity](DEFAULT_SYMBOL_TABLE_CAPACITY) and the given hash
    /// builder.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::collections::hash_map::RandomState;
    /// # use intaglio::SymbolTable;
    /// let hash_builder = RandomState::new();
    /// let table = SymbolTable::with_hasher(hash_builder);
    /// assert_eq!(0, table.len());
    /// assert!(table.capacity() >= 4096);
    /// ```
    pub fn with_hasher(hash_builder: S) -> Self {
        Self::with_capacity_and_hasher(DEFAULT_SYMBOL_TABLE_CAPACITY, hash_builder)
    }

    /// Constructs a new, empty `SymbolTable` with the specified capacity and
    /// the given hash builder.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::collections::hash_map::RandomState;
    /// # use intaglio::SymbolTable;
    /// let hash_builder = RandomState::new();
    /// let table = SymbolTable::with_capacity_and_hasher(10, hash_builder);
    /// assert_eq!(0, table.len());
    /// assert!(table.capacity() >= 10);
    /// ```
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        Self {
            vec: Vec::with_capacity(capacity),
            map: HashMap::with_capacity_and_hasher(capacity, hash_builder),
        }
    }

    /// Returns the number of bytestrings the table can hold without
    /// reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// # use intaglio::SymbolTable;
    /// let table = SymbolTable::with_capacity(10);
    /// assert!(table.capacity() >= 10);
    /// ```
    pub fn capacity(&self) -> usize {
        cmp::min(self.vec.capacity(), self.map.capacity())
    }

    /// Returns the number of interned bytestrings in the table.
    ///
    /// # Examples
    ///
    /// ```
    /// # use intaglio::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// assert_eq!(0, table.len());
    ///
    /// table.intern(b"abc".to_vec())?;
    /// // only uniquely interned bytestrings grow the symbol table.
    /// table.intern(b"abc".to_vec())?;
    /// table.intern(b"xyz".to_vec())?;
    /// assert_eq!(2, table.len());
    /// # Ok(())
    /// # }
    /// ```
    pub fn len(&self) -> usize {
        self.vec.len()
    }

    /// Returns `true` if the symbol table contains no interned bytestrings.
    ///
    /// # Examples
    ///
    /// ```
    /// # use intaglio::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// assert!(table.is_empty());
    ///
    /// table.intern(b"abc".to_vec())?;
    /// assert!(!table.is_empty());
    /// # Ok(())
    /// # }
    /// ```
    pub fn is_empty(&self) -> bool {
        self.vec.is_empty()
    }

    /// Returns `true` if the symbol table contains the given symbol.
    ///
    /// # Examples
    ///
    /// ```
    /// # use intaglio::{SymbolId, SymbolTable};
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// assert!(!table.contains(SymbolId::new(0)));
    ///
    /// let sym = table.intern(b"abc".to_vec())?;
    /// assert!(table.contains(SymbolId::new(0)));
    /// assert!(table.contains(sym));
    /// # Ok(())
    /// # }
    /// ```
    #[must_use]
    pub fn contains(&self, id: SymbolId) -> bool {
        self.get(id).is_some()
    }

    /// Returns a reference to the byte string associated with the given symbol.
    ///
    /// If the given symbol does not exist in the underlying symbol table,
    /// `None` is returned.
    ///
    /// The lifetime of the returned reference is bound to the symbol table.
    ///
    /// # Examples
    ///
    /// ```
    /// # use intaglio::{SymbolId, SymbolTable};
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// assert!(!table.get(SymbolId::new(0)).is_none());
    ///
    /// let sym = table.intern(b"abc".to_vec())?;
    /// assert_eq!(Some(&b"abc"[..]), table.get(SymbolId::new(0)));
    /// assert_eq!(Some(&b"abc"[..]), table.get(sym));
    /// # Ok(())
    /// # }
    /// ```
    #[must_use]
    pub fn get(&self, id: SymbolId) -> Option<&[u8]> {
        let bytes = self.vec.get(usize::from(id))?;
        Some(bytes.as_slice())
    }

    /// Returns an iterator over all [`SymbolId`]s and bytestrings in the
    /// [`SymbolTable`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::collections::HashMap;
    /// # use intaglio::{SymbolId, SymbolTable};
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// table.intern(b"abc".to_vec())?;
    /// table.intern(b"xyz".to_vec())?;
    /// table.intern(b"123".to_vec())?;
    /// table.intern(b"789".to_vec())?;
    ///
    /// let iter = table.iter();
    /// let mut map = HashMap::new();
    /// map.insert(SymbolId::new(0), &b"abc"[..]);
    /// map.insert(SymbolId::new(1), &b"xyz"[..]);
    /// map.insert(SymbolId::new(2), &b"123"[..]);
    /// map.insert(SymbolId::new(3), &b"789"[..]);
    /// assert_eq!(map, iter.collect::<HashMap<_, _>>());
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// ```
    /// # use intaglio::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// table.intern(b"abc".to_vec())?;
    /// table.intern(b"xyz".to_vec())?;
    /// table.intern(b"123".to_vec())?;
    /// table.intern(b"789".to_vec())?;
    ///
    /// let iter = table.iter();
    /// assert_eq!(table.len(), iter.count());
    /// # Ok(())
    /// # }
    /// ```
    pub fn iter(&self) -> Iter<'_> {
        Iter(self.all_symbols().zip(self.bytestrings()))
    }

    /// Returns an iterator over all [`SymbolId`]s in the [`SymbolTable`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use intaglio::{SymbolId, SymbolTable};
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// table.intern(b"abc".to_vec())?;
    /// table.intern(b"xyz".to_vec())?;
    /// table.intern(b"123".to_vec())?;
    /// table.intern(b"789".to_vec())?;
    ///
    /// let mut all_symbols = table.all_symbols();
    /// assert_eq!(Some(SymbolId::new(0)), all_symbols.next());
    /// assert_eq!(Some(SymbolId::new(1)), all_symbols.nth_back(2));
    /// assert_eq!(None, all_symbols.next());
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// ```
    /// # use intaglio::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// table.intern(b"abc".to_vec())?;
    /// table.intern(b"xyz".to_vec())?;
    /// table.intern(b"123".to_vec())?;
    /// table.intern(b"789".to_vec())?;
    ///
    /// let all_symbols = table.all_symbols();
    /// assert_eq!(table.len(), all_symbols.count());
    /// # Ok(())
    /// # }
    /// ```
    pub fn all_symbols(&self) -> AllSymbols<'_> {
        if self.len() == u32::MAX as usize {
            AllSymbols {
                range: Err(0..=u32::MAX),
                phantom: PhantomData,
            }
        } else {
            let upper_bound = self.len() as u32;
            AllSymbols {
                range: Ok(0..upper_bound),
                phantom: PhantomData,
            }
        }
    }

    /// Returns an iterator over all bytestrings in the [`SymbolTable`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use intaglio::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// table.intern(b"abc".to_vec())?;
    /// table.intern(b"xyz".to_vec())?;
    /// table.intern(b"123".to_vec())?;
    /// table.intern(b"789".to_vec())?;
    ///
    /// let mut bytestrings = table.bytestrings();
    /// assert_eq!(Some(&b"abc"[..]), bytestrings.next());
    /// assert_eq!(Some(&b"xyz"[..]), bytestrings.nth_back(2));
    /// assert_eq!(None, bytestrings.next());
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// ```
    /// # use intaglio::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// table.intern(b"abc".to_vec())?;
    /// table.intern(b"xyz".to_vec())?;
    /// table.intern(b"123".to_vec())?;
    /// table.intern(b"789".to_vec())?;
    ///
    /// let  bytestrings = table.bytestrings();
    /// assert_eq!(table.len(), bytestrings.count());
    /// # Ok(())
    /// # }
    /// ```
    pub fn bytestrings(&self) -> Bytestrings<'_> {
        Bytestrings(self.vec.iter())
    }

    /// Transform owned bytes into a leaked boxed slice and return the resulting
    /// 'static reference which is suitable for storing in the list of symbols.
    ///
    /// The reference is wrapped in a `Slice::Leaked` which will convert the
    /// reference back into a `Box` to be deallocated on `drop`.
    ///
    /// # Safety
    ///
    /// This function is not marked unsafe because the only side effect is
    /// leaking memory. Memory leaks are not unsafe.
    #[must_use]
    fn alloc(contents: Vec<u8>) -> Slice {
        let boxed_slice = contents.into_boxed_slice();
        let slice = Box::leak(boxed_slice);
        Slice::Leaked(slice.as_bstr())
    }
}

impl<S> SymbolTable<S>
where
    S: BuildHasher,
{
    /// Intern a bytestring for the lifetime of the symbol table.
    ///
    /// The returned `SymbolId` allows retrieving of the underlying bytes.
    /// Equal bytestrings will be inserted into the symbol table exactly once.
    ///
    /// # Errors
    ///
    /// If the symbol table would grow larger than `u32::MAX` interned
    /// bytestrings, the [`SymbolId`] counter would overflow and a
    /// [`SymbolIdOverflowError`] is returned.
    pub fn intern<T>(&mut self, contents: T) -> Result<SymbolId, SymbolIdOverflowError>
    where
        T: Into<Cow<'static, [u8]>>,
    {
        let contents = contents.into();
        if let Some(&id) = self.map.get(contents.as_ref().as_bstr()) {
            return Ok(id);
        }
        let name = match contents {
            Cow::Borrowed(contents) => Slice::Static(contents.as_bstr()),
            Cow::Owned(contents) => Self::alloc(contents),
        };
        let id = self.map.len().try_into()?;
        let slice = name.as_slice();

        self.map.insert(slice.as_bstr(), id);
        self.vec.push(name);

        debug_assert!(self.get(id) == Some(slice));
        debug_assert!(self.intern(slice) == Ok(id));

        Ok(id)
    }

    /// Returns `true` if the given byte string has been interned before.
    ///
    /// This method does not modify the symbol table.
    ///
    /// ```
    /// # use intaglio::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// assert!(!table.is_interned(b"abc"));
    ///
    /// table.intern(b"abc".to_vec())?;
    /// assert!(table.is_interned(b"abc"));
    /// # Ok(())
    /// # }
    /// ```
    #[must_use]
    pub fn is_interned(&self, contents: &[u8]) -> bool {
        self.map.contains_key(contents.as_bstr())
    }

    /// Reserves capacity for at least additional more elements to be inserted
    /// in the given `SymbolTable`. The collection may reserve more space to
    /// avoid frequent reallocations. After calling reserve, capacity will be
    /// greater than or equal to `self.len() + additional`. Does nothing if
    /// capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use intaglio::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::with_capacity(1);
    /// table.intern(b"abc".to_vec())?;
    /// table.reserve(10);
    /// assert!(table.capacity() >= 11);
    /// # Ok(())
    /// # }
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.vec.reserve(additional);
        self.map.reserve(additional);
    }

    /// Shrinks the capacity of the symbol table as much as possible.
    ///
    /// It will drop down as close as possible to the length but the allocator
    /// may still inform the symbol table that there is space for a few more
    /// elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use intaglio::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::with_capacity(10);
    /// table.intern(b"abc".to_vec());
    /// table.intern(b"xyz".to_vec());
    /// table.intern(b"123".to_vec());
    /// table.shrink_to_fit();
    /// assert!(table.capacity() >= 3);
    /// # Ok(())
    /// # }
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.vec.shrink_to_fit();
        self.map.shrink_to_fit();
    }
}

#[cfg(test)]
#[allow(clippy::needless_pass_by_value)]
mod tests {
    use quickcheck_macros::quickcheck;

    use crate::SymbolTable;

    #[test]
    fn alloc_drop_new() {
        let table = SymbolTable::new();
        drop(table);
    }

    #[test]
    fn alloc_drop_with_capacity() {
        let table = SymbolTable::with_capacity(1 << 14);
        drop(table);
    }

    #[test]
    fn drop_with_true_static_data() {
        let mut table = SymbolTable::new();
        table.intern(&b"1"[..]).unwrap();
        table.intern(&b"2"[..]).unwrap();
        table.intern(&b"3"[..]).unwrap();
        table.intern(&b"4"[..]).unwrap();
        table.intern(&b"5"[..]).unwrap();
        drop(table);
    }

    #[test]
    fn drop_with_owned_data() {
        let mut table = SymbolTable::new();
        table.intern(b"1".to_vec()).unwrap();
        table.intern(b"2".to_vec()).unwrap();
        table.intern(b"3".to_vec()).unwrap();
        table.intern(b"4".to_vec()).unwrap();
        table.intern(b"5".to_vec()).unwrap();
        drop(table);
    }

    #[test]
    fn set_owned_value_and_get_with_owned_and_borrowed() {
        let mut table = SymbolTable::new();
        // intern an owned value
        let sym = table.intern(b"abc".to_vec()).unwrap();
        // retrieve bytes
        assert_eq!(&b"abc"[..], table.get(sym).unwrap());
        // intern owned value again
        assert_eq!(sym, table.intern(b"abc".to_vec()).unwrap());
        // intern borrowed value
        assert_eq!(sym, table.intern(&b"abc"[..]).unwrap());
    }

    #[test]
    fn set_borrowed_value_and_get_with_owned_and_borrowed() {
        let mut table = SymbolTable::new();
        // intern a borrowed value
        let sym = table.intern(&b"abc"[..]).unwrap();
        // retrieve bytes
        assert_eq!(&b"abc"[..], table.get(sym).unwrap());
        // intern owned value
        assert_eq!(sym, table.intern(b"abc".to_vec()).unwrap());
        // intern borrowed value again
        assert_eq!(sym, table.intern(&b"abc"[..]).unwrap());
    }

    #[quickcheck]
    fn intern_twice_symbol_equality(bytes: Vec<u8>) -> bool {
        let mut table = SymbolTable::new();
        let sym_id = table.intern(bytes.clone()).unwrap();
        let sym_again_id = table.intern(bytes).unwrap();
        sym_id == sym_again_id
    }

    #[quickcheck]
    fn intern_get_roundtrip(bytes: Vec<u8>) -> bool {
        let mut table = SymbolTable::new();
        let sym_id = table.intern(bytes.clone()).unwrap();
        let retrieved_bytes = table.get(sym_id).unwrap();
        bytes == retrieved_bytes
    }

    #[quickcheck]
    fn table_contains_sym(bytes: Vec<u8>) -> bool {
        let mut table = SymbolTable::new();
        let sym_id = table.intern(bytes).unwrap();
        table.contains(sym_id)
    }

    #[quickcheck]
    fn table_does_not_contain_missing_symbol_ids(sym_id: u32) -> bool {
        let table = SymbolTable::new();
        !table.contains(sym_id.into())
    }

    #[quickcheck]
    fn empty_table_does_not_report_any_interned_bytestrings(bytes: Vec<u8>) -> bool {
        let table = SymbolTable::new();
        !table.is_interned(bytes.as_slice())
    }

    #[quickcheck]
    fn table_reports_interned_bytestrings_as_interned(bytes: Vec<u8>) -> bool {
        let mut table = SymbolTable::new();
        table.intern(bytes.clone()).unwrap();
        table.is_interned(bytes.as_slice())
    }
}
