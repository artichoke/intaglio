//! Intern C strings.
//!
//! This module provides a nearly identical API to the one found in the
//! top-level of this crate. There is one important difference:
//!
//! 1. Interned contents are [`&CStr`] instead of `&str`. Additionally,
//!    [`CString`] is used where `String` would have been used.
//!
//! # Example: intern C string
//!
//! ```
//! # use std::ffi::{CStr, CString};
//! # use intaglio::cstr::SymbolTable;
//! # fn example() -> Result<(), Box<dyn std::error::Error>> {
//! let mut table = SymbolTable::new();
//! let sym = table.intern(CStr::from_bytes_with_nul(b"abc\0")?)?;
//! assert_eq!(sym, table.intern(CString::new(*b"abc")?)?);
//! assert_eq!(Some(&b"abc\0"[..]), table.get(sym).map(CStr::to_bytes_with_nul));
//! # Ok(())
//! # }
//! # example().unwrap();
//! ```
//!
//! # Example: symbol iterators
//!
//! ```
//! # use std::collections::HashMap;
//! # use std::ffi::CStr;
//! # use intaglio::cstr::SymbolTable;
//! # use intaglio::Symbol;
//! # fn example() -> Result<(), Box<dyn std::error::Error>> {
//! let mut table = SymbolTable::new();
//! let sym = table.intern(CStr::from_bytes_with_nul(b"abc\0")?)?;
//! // Retrieve set of `Symbol`s.
//! let all_symbols = table.all_symbols();
//! assert_eq!(vec![sym], all_symbols.collect::<Vec<_>>());
//!
//! table.intern(CStr::from_bytes_with_nul(b"xyz\0")?)?;
//! let mut map = HashMap::new();
//! map.insert(Symbol::new(0), CStr::from_bytes_with_nul(b"abc\0")?);
//! map.insert(Symbol::new(1), CStr::from_bytes_with_nul(b"xyz\0")?);
//! // Retrieve symbol to C string content mappings.
//! let iter = table.iter();
//! assert_eq!(map, iter.collect::<HashMap<_, _>>());
//! # Ok(())
//! # }
//! # example().unwrap();
//! ```
//!
//! # Performance
//!
//! In general, one should expect this crate's performance on `&CStr` to be
//! roughly similar to performance on `&str`.
//!
//! [`CString`]: std::ffi::CString
//! [`&CStr`]: std::ffi::CStr

use core::convert::TryInto;
use core::hash::BuildHasher;
use core::iter::{FromIterator, FusedIterator, Zip};
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ops::Range;
use core::slice;
use std::borrow::Cow;
use std::collections::hash_map::{HashMap, RandomState};
use std::ffi::CStr;

use crate::internal::Interned;
use crate::{Symbol, SymbolOverflowError, DEFAULT_SYMBOL_TABLE_CAPACITY};

/// An iterator over all [`Symbol`]s in a [`SymbolTable`].
///
/// See the [`all_symbols`](SymbolTable::all_symbols) method in [`SymbolTable`].
///
/// # Usage
///
/// ```
/// # use std::ffi::CStr;
/// # use intaglio::cstr::SymbolTable;
/// # fn example() -> Result<(), Box<dyn std::error::Error>> {
/// let mut table = SymbolTable::new();
/// let sym = table.intern(CStr::from_bytes_with_nul(b"abc\0")?)?;
/// let all_symbols = table.all_symbols();
/// assert_eq!(vec![sym], all_symbols.collect::<Vec<_>>());
/// # Ok(())
/// # }
/// # example().unwrap();
/// ```
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
#[cfg_attr(docsrs, doc(cfg(feature = "cstr")))]
pub struct AllSymbols<'a> {
    range: Range<u32>,
    // Hold a shared reference to the underlying `SymbolTable` to ensure the
    // table is not modified while we are iterating which would make the results
    // not match the real state.
    phantom: PhantomData<&'a SymbolTable>,
}

impl<'a> Iterator for AllSymbols<'a> {
    type Item = Symbol;

    fn next(&mut self) -> Option<Self::Item> {
        self.range.next().map(Symbol::from)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.range.size_hint()
    }

    fn count(self) -> usize {
        self.range.count()
    }

    fn last(self) -> Option<Self::Item> {
        self.range.last().map(Symbol::from)
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.range.nth(n).map(Symbol::from)
    }

    fn collect<B: FromIterator<Self::Item>>(self) -> B {
        self.range.map(Symbol::from).collect()
    }
}

impl<'a> DoubleEndedIterator for AllSymbols<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.range.next_back().map(Symbol::from)
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.range.nth_back(n).map(Symbol::from)
    }
}

impl<'a> FusedIterator for AllSymbols<'a> {}

/// An iterator over all interned C strings in a [`SymbolTable`].
///
/// See the [`c_strings`](SymbolTable::c_strings) method in [`SymbolTable`].
///
/// # Usage
///
/// ```
/// # use std::ffi::{CStr, CString};
/// # use intaglio::cstr::SymbolTable;
/// # fn example() -> Result<(), Box<dyn std::error::Error>> {
/// let mut table = SymbolTable::new();
/// let sym = table.intern(CString::new(*b"abc")?)?;
/// let c_strings = table.c_strings();
/// assert_eq!(vec![CStr::from_bytes_with_nul(b"abc\0")?], c_strings.collect::<Vec<_>>());
/// # Ok(())
/// # }
/// # example().unwrap();
/// ```
#[derive(Debug, Clone)]
#[cfg_attr(docsrs, doc(cfg(feature = "cstr")))]
pub struct CStrings<'a>(slice::Iter<'a, Interned<CStr>>);

impl<'a> Iterator for CStrings<'a> {
    type Item = &'a CStr;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(Interned::as_slice)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }

    fn count(self) -> usize {
        self.0.count()
    }

    fn last(self) -> Option<Self::Item> {
        self.0.last().map(Interned::as_slice)
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.0.nth(n).map(Interned::as_slice)
    }

    fn collect<B: FromIterator<Self::Item>>(self) -> B {
        self.0.map(Interned::as_slice).collect()
    }
}

impl<'a> DoubleEndedIterator for CStrings<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(Interned::as_slice)
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.0.nth_back(n).map(Interned::as_slice)
    }

    fn rfold<B, F>(self, accum: B, f: F) -> B
    where
        F: FnMut(B, Self::Item) -> B,
    {
        self.0.map(Interned::as_slice).rfold(accum, f)
    }
}

impl<'a> ExactSizeIterator for CStrings<'a> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<'a> FusedIterator for CStrings<'a> {}

/// An iterator over all symbols and interned C strings in a [`SymbolTable`].
///
/// See the [`iter`](SymbolTable::iter) method in [`SymbolTable`].
///
/// # Usage
///
/// ```
/// # use std::collections::HashMap;
/// # use std::ffi::{CStr, CString};
/// # use intaglio::cstr::SymbolTable;
/// # use intaglio::Symbol;
/// # fn example() -> Result<(), Box<dyn std::error::Error>> {
/// let mut table = SymbolTable::new();
/// let sym = table.intern(CStr::from_bytes_with_nul(b"abc\0")?)?;
/// let iter = table.iter();
/// let mut map = HashMap::new();
/// map.insert(Symbol::new(0), CStr::from_bytes_with_nul(b"abc\0")?);
/// assert_eq!(map, iter.collect::<HashMap<_, _>>());
/// # Ok(())
/// # }
/// # example().unwrap();
/// ```
#[derive(Debug, Clone)]
#[cfg_attr(docsrs, doc(cfg(feature = "cstr")))]
pub struct Iter<'a>(Zip<AllSymbols<'a>, CStrings<'a>>);

impl<'a> Iterator for Iter<'a> {
    type Item = (Symbol, &'a CStr);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }

    fn count(self) -> usize {
        self.0.count()
    }

    fn last(self) -> Option<Self::Item> {
        self.0.last()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.0.nth(n)
    }

    fn collect<B: FromIterator<Self::Item>>(self) -> B {
        self.0.collect()
    }
}

impl<'a> FusedIterator for Iter<'a> {}

impl<'a> IntoIterator for &'a SymbolTable {
    type Item = (Symbol, &'a CStr);
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// C string interner.
///
/// This symbol table is implemented by storing [`CString`]s with a fast path
/// for [`&CStr`] that are already `'static`.
///
/// See module documentation for more.
///
/// # Usage
///
/// ```
/// # use std::ffi::{CStr, CString};
/// # use intaglio::cstr::SymbolTable;
/// # fn example() -> Result<(), Box<dyn std::error::Error>> {
/// let mut table = SymbolTable::new();
/// let sym = table.intern(CStr::from_bytes_with_nul(b"abc\0")?)?;
/// assert_eq!(sym, table.intern(CString::new(*b"abc")?)?);
/// assert!(table.contains(sym));
/// assert!(table.is_interned(CStr::from_bytes_with_nul(b"abc\0")?));
/// # Ok(())
/// # }
/// # example().unwrap();
/// ```
///
/// [`CString`]: std::ffi::CString
/// [`&CStr`]: std::ffi::CStr
#[derive(Default, Debug)]
#[cfg_attr(docsrs, doc(cfg(feature = "cstr")))]
pub struct SymbolTable<S = RandomState> {
    map: ManuallyDrop<HashMap<&'static CStr, Symbol, S>>,
    vec: ManuallyDrop<Vec<Interned<CStr>>>,
}

impl<S> Drop for SymbolTable<S> {
    fn drop(&mut self) {
        // Safety:
        //
        // `Interned` requires that the `'static` references it gives out are
        // dropped before the owning buffer stored in the `Interned`.
        //
        // `ManuallyDrop::drop` is only invoked in this `Drop::drop` impl;
        // because mutable references to `map` and `vec` fields are not given
        // out by `SymbolTable`, `map` and `vec` are guaranteed to be
        // initialized.
        unsafe {
            ManuallyDrop::drop(&mut self.map);
            ManuallyDrop::drop(&mut self.vec);
        }
    }
}

impl SymbolTable<RandomState> {
    /// Constructs a new, empty `SymbolTable` with [default capacity].
    ///
    /// This function will always allocate. To construct a symbol table without
    /// allocating, call [`SymbolTable::with_capacity(0)`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use intaglio::cstr::SymbolTable;
    /// let table = SymbolTable::new();
    /// assert_eq!(0, table.len());
    /// assert!(table.capacity() >= 4096);
    /// ```
    ///
    /// [default capacity]: DEFAULT_SYMBOL_TABLE_CAPACITY
    /// [`SymbolTable::with_capacity(0)`]: Self::with_capacity
    #[must_use]
    pub fn new() -> Self {
        Self::with_capacity(DEFAULT_SYMBOL_TABLE_CAPACITY)
    }

    /// Constructs a new, empty `SymbolTable` with the specified capacity.
    ///
    /// The symbol table will be able to hold at least `capacity` C strings
    /// without reallocating. If `capacity` is 0, the symbol table will not
    /// allocate.
    ///
    /// # Examples
    ///
    /// ```
    /// # use intaglio::cstr::SymbolTable;
    /// let table = SymbolTable::with_capacity(10);
    /// assert_eq!(0, table.len());
    /// assert!(table.capacity() >= 10);
    /// ```
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        let capacity = capacity.next_power_of_two();
        Self {
            map: ManuallyDrop::new(HashMap::with_capacity(capacity)),
            vec: ManuallyDrop::new(Vec::with_capacity(capacity)),
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
    /// # use intaglio::cstr::SymbolTable;
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
    /// # use intaglio::cstr::SymbolTable;
    /// let hash_builder = RandomState::new();
    /// let table = SymbolTable::with_capacity_and_hasher(10, hash_builder);
    /// assert_eq!(0, table.len());
    /// assert!(table.capacity() >= 10);
    /// ```
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        Self {
            map: ManuallyDrop::new(HashMap::with_capacity_and_hasher(capacity, hash_builder)),
            vec: ManuallyDrop::new(Vec::with_capacity(capacity)),
        }
    }

    /// Returns the number of C strings the table can hold without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// # use intaglio::cstr::SymbolTable;
    /// let table = SymbolTable::with_capacity(10);
    /// assert!(table.capacity() >= 10);
    /// ```
    pub fn capacity(&self) -> usize {
        usize::min(self.vec.capacity(), self.map.capacity())
    }

    /// Returns the number of interned C strings in the table.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::ffi::CString;
    /// # use intaglio::cstr::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// assert_eq!(0, table.len());
    ///
    /// table.intern(CString::new(*b"abc")?)?;
    /// // only uniquely interned C strings grow the symbol table.
    /// table.intern(CString::new(*b"abc")?)?;
    /// table.intern(CString::new(*b"xyz")?)?;
    /// assert_eq!(2, table.len());
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    pub fn len(&self) -> usize {
        self.vec.len()
    }

    /// Returns `true` if the symbol table contains no interned C strings.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::ffi::CString;
    /// # use intaglio::cstr::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// assert!(table.is_empty());
    ///
    /// table.intern(CString::new(*b"abc")?)?;
    /// assert!(!table.is_empty());
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    pub fn is_empty(&self) -> bool {
        self.vec.is_empty()
    }

    /// Returns `true` if the symbol table contains the given symbol.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::ffi::CString;
    /// # use intaglio::cstr::SymbolTable;
    /// # use intaglio::Symbol;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// assert!(!table.contains(Symbol::new(0)));
    ///
    /// let sym = table.intern(CString::new(*b"abc")?)?;
    /// assert!(table.contains(Symbol::new(0)));
    /// assert!(table.contains(sym));
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    #[must_use]
    pub fn contains(&self, id: Symbol) -> bool {
        self.get(id).is_some()
    }

    /// Returns a reference to the C string associated with the given symbol.
    ///
    /// If the given symbol does not exist in the underlying symbol table,
    /// `None` is returned.
    ///
    /// The lifetime of the returned reference is bound to the symbol table.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::ffi::{CStr, CString};
    /// # use intaglio::cstr::SymbolTable;
    /// # use intaglio::Symbol;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// assert!(table.get(Symbol::new(0)).is_none());
    ///
    /// let sym = table.intern(CString::new(*b"abc")?)?;
    /// assert_eq!(Some(CStr::from_bytes_with_nul(b"abc\0")?), table.get(Symbol::new(0)));
    /// assert_eq!(Some(CStr::from_bytes_with_nul(b"abc\0")?), table.get(sym));
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    #[must_use]
    pub fn get(&self, id: Symbol) -> Option<&CStr> {
        let cstr = self.vec.get(usize::from(id))?;
        Some(cstr.as_slice())
    }

    /// Returns an iterator over all [`Symbol`]s and C strings in the
    /// [`SymbolTable`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::collections::HashMap;
    /// # use std::ffi::{CStr, CString};
    /// # use intaglio::cstr::SymbolTable;
    /// # use intaglio::Symbol;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// table.intern(CString::new(*b"abc")?)?;
    /// table.intern(CString::new(*b"xyz")?)?;
    /// table.intern(CString::new(*b"123")?)?;
    /// table.intern(CString::new(*b"789")?)?;
    ///
    /// let iter = table.iter();
    /// let mut map = HashMap::new();
    /// map.insert(Symbol::new(0), CStr::from_bytes_with_nul(b"abc\0")?);
    /// map.insert(Symbol::new(1), CStr::from_bytes_with_nul(b"xyz\0")?);
    /// map.insert(Symbol::new(2), CStr::from_bytes_with_nul(b"123\0")?);
    /// map.insert(Symbol::new(3), CStr::from_bytes_with_nul(b"789\0")?);
    /// assert_eq!(map, iter.collect::<HashMap<_, _>>());
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    ///
    /// ```
    /// # use std::ffi::CString;
    /// # use intaglio::cstr::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// table.intern(CString::new(*b"abc")?)?;
    /// table.intern(CString::new(*b"xyz")?)?;
    /// table.intern(CString::new(*b"123")?)?;
    /// table.intern(CString::new(*b"789")?)?;
    ///
    /// let iter = table.iter();
    /// assert_eq!(table.len(), iter.count());
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    pub fn iter(&self) -> Iter<'_> {
        Iter(self.all_symbols().zip(self.c_strings()))
    }

    /// Returns an iterator over all [`Symbol`]s in the [`SymbolTable`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::ffi::CString;
    /// # use intaglio::cstr::SymbolTable;
    /// # use intaglio::Symbol;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// table.intern(CString::new(*b"abc")?)?;
    /// table.intern(CString::new(*b"xyz")?)?;
    /// table.intern(CString::new(*b"123")?)?;
    /// table.intern(CString::new(*b"789")?)?;
    ///
    /// let mut all_symbols = table.all_symbols();
    /// assert_eq!(Some(Symbol::new(0)), all_symbols.next());
    /// assert_eq!(Some(Symbol::new(1)), all_symbols.nth_back(2));
    /// assert_eq!(None, all_symbols.next());
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    ///
    /// ```
    /// # use std::ffi::CString;
    /// # use intaglio::cstr::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// table.intern(CString::new(*b"abc")?)?;
    /// table.intern(CString::new(*b"xyz")?)?;
    /// table.intern(CString::new(*b"123")?)?;
    /// table.intern(CString::new(*b"789")?)?;
    ///
    /// let all_symbols = table.all_symbols();
    /// assert_eq!(table.len(), all_symbols.count());
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    pub fn all_symbols(&self) -> AllSymbols<'_> {
        let len = self.len();
        debug_assert!(
            u32::try_from(len).is_ok(),
            "Interner can hold at most u32::MAX symbols"
        );
        let len = len as u32;
        AllSymbols {
            range: 0_u32..len,
            phantom: PhantomData,
        }
    }

    /// Returns an iterator over all C strings in the [`SymbolTable`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::ffi::{CStr, CString};
    /// # use intaglio::cstr::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// table.intern(CString::new(*b"abc")?)?;
    /// table.intern(CString::new(*b"xyz")?)?;
    /// table.intern(CString::new(*b"123")?)?;
    /// table.intern(CString::new(*b"789")?)?;
    ///
    /// let mut c_strings = table.c_strings();
    /// assert_eq!(Some(CStr::from_bytes_with_nul(b"abc\0")?), c_strings.next());
    /// assert_eq!(Some(CStr::from_bytes_with_nul(b"xyz\0")?), c_strings.nth_back(2));
    /// assert_eq!(None, c_strings.next());
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    ///
    /// ```
    /// # use std::ffi::CString;
    /// # use intaglio::cstr::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// table.intern(CString::new(*b"abc")?)?;
    /// table.intern(CString::new(*b"xyz")?)?;
    /// table.intern(CString::new(*b"123")?)?;
    /// table.intern(CString::new(*b"789")?)?;
    ///
    /// let c_strings = table.c_strings();
    /// assert_eq!(table.len(), c_strings.count());
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    pub fn c_strings(&self) -> CStrings<'_> {
        CStrings(self.vec.iter())
    }
}

impl<S> SymbolTable<S>
where
    S: BuildHasher,
{
    /// Intern a C string for the lifetime of the symbol table.
    ///
    /// The returned `Symbol` allows retrieving of the underlying [`CStr`].
    /// Equal C strings will be inserted into the symbol table exactly once.
    ///
    /// This function only allocates if the underlying symbol table has no
    /// remaining capacity.
    ///
    /// # Errors
    ///
    /// If the symbol table would grow larger than `u32::MAX` interned C
    /// strings, the [`Symbol`] counter would overflow and a
    /// [`SymbolOverflowError`] is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::ffi::{CStr, CString};
    /// # use intaglio::cstr::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// let sym = table.intern(CString::new(*b"abc")?)?;
    /// table.intern(CString::new(*b"xyz")?)?;
    /// table.intern(CStr::from_bytes_with_nul(b"123\0")?)?;
    /// table.intern(CStr::from_bytes_with_nul(b"789\0")?)?;
    ///
    /// assert_eq!(4, table.len());
    /// assert_eq!(Some(&b"abc\0"[..]), table.get(sym).map(CStr::to_bytes_with_nul));
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    pub fn intern<T>(&mut self, contents: T) -> Result<Symbol, SymbolOverflowError>
    where
        T: Into<Cow<'static, CStr>>,
    {
        let contents = contents.into();
        if let Some(&id) = self.map.get(&*contents) {
            return Ok(id);
        }

        let id = self.map.len().try_into()?;
        // If the number of symbols stored in the table is `u32::MAX`, then the
        // last issued symbol was `u32::MAX - 1` because `(0..u32::MAX).count() == u32::MAX`.
        //
        // Creating a symbol with id `u32::MAX` means the range of ids in the
        // table would be `0..=u32::MAX`, which means the table would store
        // `u32::MAX + 1` symbols, which is beyond `SymbolTable`'s documented
        // capacity.
        if id == u32::MAX {
            return Err(SymbolOverflowError::new());
        }

        // If given `Cow::Owned(_)` this operation will potentially perform a
        // copy when converting the owned string into a boxed owned string.
        let name = Interned::from(contents);

        // Safety:
        //
        // This expression creates a reference with a `'static` lifetime
        // from an owned and interned buffer. This is permissible because:
        //
        // - `Interned` is an internal implementation detail of `SymbolTable`.
        // - `SymbolTable` never give out `'static` references to underlying
        //   C string byte contents.
        // - All slice references given out by the `SymbolTable` have the same
        //   lifetime as the `SymbolTable`.
        // - The `map` field of `SymbolTable`, which contains the `'static`
        //   references, is dropped before the owned buffers stored in this
        //   `Interned`.
        let slice = unsafe { name.as_static_slice() };

        self.map.insert(slice, id);
        self.vec.push(name);

        debug_assert_eq!(self.get(id), Some(slice));
        debug_assert_eq!(self.intern(slice), Ok(id));

        Ok(id)
    }

    /// Returns the `Symbol` identifier for `contents` if it has been interned
    /// before, `None` otherwise.
    ///
    /// This method does not modify the symbol table.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::ffi::{CStr, CString};
    /// # use intaglio::cstr::SymbolTable;
    /// # use intaglio::Symbol;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// assert!(!table.is_interned(CStr::from_bytes_with_nul(b"abc\0")?));
    /// assert_eq!(None, table.check_interned(CStr::from_bytes_with_nul(b"abc\0")?));
    ///
    /// table.intern(CString::new(*b"abc")?)?;
    /// assert!(table.is_interned(CStr::from_bytes_with_nul(b"abc\0")?));
    /// assert_eq!(Some(Symbol::new(0)), table.check_interned(CStr::from_bytes_with_nul(b"abc\0")?));
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    #[must_use]
    pub fn check_interned(&self, contents: &CStr) -> Option<Symbol> {
        self.map.get(contents).copied()
    }

    /// Returns `true` if the given C string has been interned before.
    ///
    /// This method does not modify the symbol table.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::ffi::{CStr, CString};
    /// # use intaglio::cstr::SymbolTable;
    /// # use intaglio::Symbol;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// assert!(!table.is_interned(CStr::from_bytes_with_nul(b"abc\0")?));
    /// assert_eq!(None, table.check_interned(CStr::from_bytes_with_nul(b"abc\0")?));
    ///
    /// table.intern(CString::new(*b"abc")?)?;
    /// assert!(table.is_interned(CStr::from_bytes_with_nul(b"abc\0")?));
    /// assert_eq!(Some(Symbol::new(0)), table.check_interned(CStr::from_bytes_with_nul(b"abc\0")?));
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    #[must_use]
    pub fn is_interned(&self, contents: &CStr) -> bool {
        self.map.contains_key(contents)
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
    /// # use std::ffi::CString;
    /// # use intaglio::cstr::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::with_capacity(1);
    /// table.intern(CString::new(*b"abc")?)?;
    /// table.reserve(10);
    /// assert!(table.capacity() >= 11);
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.map.reserve(additional);
        self.vec.reserve(additional);
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
    /// # use std::ffi::CString;
    /// # use intaglio::cstr::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::with_capacity(10);
    /// table.intern(CString::new(*b"abc")?);
    /// table.intern(CString::new(*b"xyz")?);
    /// table.intern(CString::new(*b"123")?);
    /// table.shrink_to_fit();
    /// assert!(table.capacity() >= 3);
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.map.shrink_to_fit();
        self.vec.shrink_to_fit();
    }

    /// Shrinks the capacity of the symbol table with a lower bound.
    ///
    /// The capacity will remain at least as large as both the length and the
    /// supplied value.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::ffi::CString;
    /// # use intaglio::cstr::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::with_capacity(10);
    /// table.intern(CString::new(*b"abc")?);
    /// table.intern(CString::new(*b"xyz")?);
    /// table.intern(CString::new(*b"123")?);
    /// table.shrink_to(5);
    /// assert!(table.capacity() >= 5);
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.map.shrink_to(min_capacity);
        self.vec.shrink_to(min_capacity);
    }
}

#[cfg(test)]
#[allow(clippy::needless_pass_by_value)]
mod tests {
    use std::ffi::{CStr, CString};

    use quickcheck_macros::quickcheck;

    use super::SymbolTable;

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
        table
            .intern(CStr::from_bytes_with_nul(b"1\0").unwrap())
            .unwrap();
        table
            .intern(CStr::from_bytes_with_nul(b"2\0").unwrap())
            .unwrap();
        table
            .intern(CStr::from_bytes_with_nul(b"3\0").unwrap())
            .unwrap();
        table
            .intern(CStr::from_bytes_with_nul(b"4\0").unwrap())
            .unwrap();
        table
            .intern(CStr::from_bytes_with_nul(b"5\0").unwrap())
            .unwrap();
        drop(table);
    }

    #[test]
    fn drop_with_owned_data() {
        let mut table = SymbolTable::new();
        table.intern(CString::new(*b"1").unwrap()).unwrap();
        table.intern(CString::new(*b"2").unwrap()).unwrap();
        table.intern(CString::new(*b"3").unwrap()).unwrap();
        table.intern(CString::new(*b"4").unwrap()).unwrap();
        table.intern(CString::new(*b"5").unwrap()).unwrap();
        drop(table);
    }

    #[test]
    fn set_owned_value_and_get_with_owned_and_borrowed() {
        let mut table = SymbolTable::new();
        // intern an owned value
        let sym = table.intern(CString::new(*b"abc").unwrap()).unwrap();
        // retrieve C string bytes
        assert_eq!(&b"abc\0"[..], table.get(sym).unwrap().to_bytes_with_nul());
        // intern owned value again
        assert_eq!(sym, table.intern(CString::new(*b"abc").unwrap()).unwrap());
        // intern borrowed value
        assert_eq!(
            sym,
            table
                .intern(CStr::from_bytes_with_nul(b"abc\0").unwrap())
                .unwrap()
        );
    }

    #[test]
    fn set_borrowed_value_and_get_with_owned_and_borrowed() {
        let mut table = SymbolTable::new();
        // intern a borrowed value
        let sym = table
            .intern(CStr::from_bytes_with_nul(b"abc\0").unwrap())
            .unwrap();
        // retrieve C string bytes
        assert_eq!(&b"abc\0"[..], table.get(sym).unwrap().to_bytes_with_nul());
        // intern owned value
        assert_eq!(sym, table.intern(CString::new(*b"abc").unwrap()).unwrap());
        // intern borrowed value again
        assert_eq!(
            sym,
            table
                .intern(CStr::from_bytes_with_nul(b"abc\0").unwrap())
                .unwrap()
        );
    }

    #[quickcheck]
    fn intern_twice_symbol_equality(cstring: CString) -> bool {
        let mut table = SymbolTable::new();
        let sym = table.intern(cstring.clone()).unwrap();
        let sym_again = table.intern(cstring).unwrap();
        sym == sym_again
    }

    #[quickcheck]
    fn intern_get_roundtrip(cstring: CString) -> bool {
        let mut table = SymbolTable::new();
        let sym = table.intern(cstring.clone()).unwrap();
        let retrieved_c_string = table.get(sym).unwrap();
        &*cstring == retrieved_c_string
    }

    #[quickcheck]
    fn table_contains_sym(cstring: CString) -> bool {
        let mut table = SymbolTable::new();
        let sym = table.intern(cstring).unwrap();
        table.contains(sym)
    }

    #[quickcheck]
    fn table_does_not_contain_missing_symbol_ids(sym: u32) -> bool {
        let table = SymbolTable::new();
        !table.contains(sym.into())
    }

    #[quickcheck]
    fn empty_table_does_not_report_any_interned_c_strings(cstring: CString) -> bool {
        let table = SymbolTable::new();
        !table.is_interned(cstring.as_c_str())
    }

    #[quickcheck]
    fn table_reports_interned_c_strings_as_interned(cstring: CString) -> bool {
        let mut table = SymbolTable::new();
        table.intern(cstring.clone()).unwrap();
        table.is_interned(cstring.as_c_str())
    }
}
