//! Intaglio interner for UTF-8 [`String`]s.

use core::borrow::Borrow;
use core::cmp;
use core::convert::TryInto;
use core::hash::{BuildHasher, Hash, Hasher};
use core::iter::{self, FusedIterator};
use core::marker::PhantomData;
use core::ops::{Deref, Range, RangeInclusive};
use core::slice;
use std::borrow::Cow;
use std::collections::hash_map::RandomState;
use std::collections::HashMap;

use crate::{Symbol, SymbolOverflowError, DEFAULT_SYMBOL_TABLE_CAPACITY};

/// Wrapper around `&'static str` that supports deallocating references created
/// via [`Box::leak`].
///
/// # Safety
///
/// Must not be `Clone` or `Copy` because the Drop logic assumes this enum is the
/// unique owner of a leaked boxed slice. The lack of `Clone` and `Copy` impls is
/// necessary to prevent double frees.
#[derive(Debug)]
enum Slice {
    /// True `'static` references.
    Static(&'static str),
    /// Owned `'static` references.
    Owned(Box<str>),
}

impl Slice {
    /// Return a reference to the inner slice.
    fn as_slice(&self) -> &str {
        match self {
            Self::Static(global) => global,
            Self::Owned(leaked) => &**leaked,
        }
    }

    /// Return a reference to the inner slice.
    ///
    /// # Safety
    ///
    /// This returns a reference with an unbounded lifetime.
    /// It is your responsibility to make sure it is not used
    /// after this `Slice` is dropped.
    unsafe fn as_static_slice(&self) -> &'static str {
        match self {
            Self::Static(global) => global,
            #[allow(trivial_casts)]
            Self::Owned(leaked) => &*(&**leaked as *const str),
        }
    }
}

impl Default for Slice {
    fn default() -> Self {
        Self::Static(<_>::default())
    }
}

impl Deref for Slice {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl PartialEq<Slice> for Slice {
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl PartialEq<str> for Slice {
    fn eq(&self, other: &str) -> bool {
        self.as_slice() == other
    }
}

impl PartialEq<Slice> for str {
    fn eq(&self, other: &Slice) -> bool {
        self == other.as_slice()
    }
}

impl PartialEq<String> for Slice {
    fn eq(&self, other: &String) -> bool {
        self.as_slice() == other
    }
}

impl PartialEq<Slice> for String {
    fn eq(&self, other: &Slice) -> bool {
        self == other.as_slice()
    }
}

impl Eq for Slice {}

impl Hash for Slice {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

impl Borrow<str> for Slice {
    fn borrow(&self) -> &str {
        self.as_slice()
    }
}

impl Borrow<str> for &Slice {
    fn borrow(&self) -> &str {
        self.as_slice()
    }
}

impl Borrow<str> for &mut Slice {
    fn borrow(&self) -> &str {
        self.as_slice()
    }
}

impl Borrow<[u8]> for Slice {
    fn borrow(&self) -> &[u8] {
        self.as_slice().as_bytes()
    }
}

impl Borrow<[u8]> for &Slice {
    fn borrow(&self) -> &[u8] {
        self.as_slice().as_bytes()
    }
}

impl Borrow<[u8]> for &mut Slice {
    fn borrow(&self) -> &[u8] {
        self.as_slice().as_bytes()
    }
}

/// An iterator over all [`Symbol`]s in a [`SymbolTable`].
///
/// # Usage
///
/// ```
/// # use intaglio::SymbolTable;
/// # fn example() -> Result<(), Box<dyn std::error::Error>> {
/// let mut table = SymbolTable::new();
/// let sym = table.intern("abc")?;
/// let all_symbols = table.all_symbols();
/// assert_eq!(vec![sym], all_symbols.collect::<Vec<_>>());
/// # Ok(())
/// # }
/// # example().unwrap();
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
    type Item = Symbol;

    fn next(&mut self) -> Option<Self::Item> {
        match self.range {
            Ok(ref mut range) => range.next().map(Symbol::from),
            Err(ref mut range) => range.next().map(Symbol::from),
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
            Ok(range) => range.last().map(Symbol::from),
            Err(range) => range.last().map(Symbol::from),
        }
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        match self.range {
            Ok(ref mut range) => range.nth(n).map(Symbol::from),
            Err(ref mut range) => range.nth(n).map(Symbol::from),
        }
    }

    fn collect<B: iter::FromIterator<Self::Item>>(self) -> B
    where
        Self: Sized,
    {
        match self.range {
            Ok(range) => range.map(Symbol::from).collect(),
            Err(range) => range.map(Symbol::from).collect(),
        }
    }
}

impl<'a> DoubleEndedIterator for AllSymbols<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self.range {
            Ok(ref mut range) => range.next_back().map(Symbol::from),
            Err(ref mut range) => range.next_back().map(Symbol::from),
        }
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        match self.range {
            Ok(ref mut range) => range.nth_back(n).map(Symbol::from),
            Err(ref mut range) => range.nth_back(n).map(Symbol::from),
        }
    }
}

impl<'a> FusedIterator for AllSymbols<'a> {}

/// An iterator over all interned strings in a [`SymbolTable`].
///
/// # Usage
///
/// ```
/// # use intaglio::SymbolTable;
/// # fn example() -> Result<(), Box<dyn std::error::Error>> {
/// let mut table = SymbolTable::new();
/// let sym = table.intern("abc")?;
/// let strings = table.strings();
/// assert_eq!(vec!["abc"], strings.collect::<Vec<_>>());
/// # Ok(())
/// # }
/// # example().unwrap();
/// ```
#[derive(Debug, Clone)]
pub struct Strings<'a>(slice::Iter<'a, Slice>);

impl<'a> Iterator for Strings<'a> {
    type Item = &'a str;

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

impl<'a> DoubleEndedIterator for Strings<'a> {
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

impl<'a> ExactSizeIterator for Strings<'a> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<'a> FusedIterator for Strings<'a> {}

/// An iterator over all symbols and interned strings in a [`SymbolTable`].
///
/// # Usage
///
/// ```
/// # use std::collections::HashMap;
/// # use intaglio::{Symbol, SymbolTable};
/// # fn example() -> Result<(), Box<dyn std::error::Error>> {
/// let mut table = SymbolTable::new();
/// let sym = table.intern("abc")?;
/// let iter = table.iter();
/// let mut map = HashMap::new();
/// map.insert(Symbol::new(0), "abc");
/// assert_eq!(map, iter.collect::<HashMap<_, _>>());
/// # Ok(())
/// # }
/// # example().unwrap();
/// ```
#[derive(Debug, Clone)]
pub struct Iter<'a>(iter::Zip<AllSymbols<'a>, Strings<'a>>);

impl<'a> Iterator for Iter<'a> {
    type Item = (Symbol, &'a str);

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
    type Item = (Symbol, &'a str);
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// UTF-8 string interner.
///
/// This symbol table is implemented by leaking UTF-8 strings with a fast path for
/// `&str` that are already `'static`.
///
/// # Usage
///
/// ```
/// # use intaglio::SymbolTable;
/// # fn example() -> Result<(), Box<dyn std::error::Error>> {
/// let mut table = SymbolTable::new();
/// let sym = table.intern("abc")?;
/// assert_eq!(sym, table.intern("abc".to_string())?);
/// assert!(table.contains(sym));
/// assert!(table.is_interned("abc"));
/// # Ok(())
/// # }
/// # example().unwrap();
/// ```
#[derive(Default, Debug)]
pub struct SymbolTable<S = RandomState> {
    map: HashMap<&'static str, Symbol, S>,
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
    /// table.intern("abc")?;
    /// // only uniquely interned bytestrings grow the symbol table.
    /// table.intern("abc")?;
    /// table.intern("xyz")?;
    /// assert_eq!(2, table.len());
    /// # Ok(())
    /// # }
    /// # example().unwrap();
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
    /// table.intern("abc")?;
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
    /// # use intaglio::{Symbol, SymbolTable};
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// assert!(!table.contains(Symbol::new(0)));
    ///
    /// let sym = table.intern("abc")?;
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
    /// # use intaglio::{Symbol, SymbolTable};
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// assert!(table.get(Symbol::new(0)).is_none());
    ///
    /// let sym = table.intern("abc".to_string())?;
    /// assert_eq!(Some("abc"), table.get(Symbol::new(0)));
    /// assert_eq!(Some("abc"), table.get(sym));
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    #[must_use]
    pub fn get(&self, id: Symbol) -> Option<&str> {
        let bytes = self.vec.get(usize::from(id))?;
        Some(bytes.as_slice())
    }

    /// Returns an iterator over all [`Symbol`]s and bytestrings in the
    /// [`SymbolTable`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use std::collections::HashMap;
    /// # use intaglio::{Symbol, SymbolTable};
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// table.intern("abc")?;
    /// table.intern("xyz")?;
    /// table.intern("123")?;
    /// table.intern("789")?;
    ///
    /// let iter = table.iter();
    /// let mut map = HashMap::new();
    /// map.insert(Symbol::new(0), "abc");
    /// map.insert(Symbol::new(1), "xyz");
    /// map.insert(Symbol::new(2), "123");
    /// map.insert(Symbol::new(3), "789");
    /// assert_eq!(map, iter.collect::<HashMap<_, _>>());
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    ///
    /// ```
    /// # use intaglio::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// table.intern("abc")?;
    /// table.intern("xyz")?;
    /// table.intern("123")?;
    /// table.intern("789")?;
    ///
    /// let iter = table.iter();
    /// assert_eq!(table.len(), iter.count());
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    pub fn iter(&self) -> Iter<'_> {
        Iter(self.all_symbols().zip(self.strings()))
    }

    /// Returns an iterator over all [`Symbol`]s in the [`SymbolTable`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use intaglio::{Symbol, SymbolTable};
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// table.intern("abc")?;
    /// table.intern("xyz")?;
    /// table.intern("123")?;
    /// table.intern("789")?;
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
    /// # use intaglio::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// table.intern("abc")?;
    /// table.intern("xyz")?;
    /// table.intern("123")?;
    /// table.intern("789")?;
    ///
    /// let all_symbols = table.all_symbols();
    /// assert_eq!(table.len(), all_symbols.count());
    /// # Ok(())
    /// # }
    /// # example().unwrap();
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

    /// Returns an iterator over all strings in the [`SymbolTable`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use intaglio::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// table.intern("abc")?;
    /// table.intern("xyz")?;
    /// table.intern("123")?;
    /// table.intern("789")?;
    ///
    /// let mut strings = table.strings();
    /// assert_eq!(Some("abc"), strings.next());
    /// assert_eq!(Some("xyz"), strings.nth_back(2));
    /// assert_eq!(None, strings.next());
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    ///
    /// ```
    /// # use intaglio::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// table.intern("abc")?;
    /// table.intern("xyz")?;
    /// table.intern("123")?;
    /// table.intern("789")?;
    ///
    /// let  strings = table.strings();
    /// assert_eq!(table.len(), strings.count());
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    pub fn strings(&self) -> Strings<'_> {
        Strings(self.vec.iter())
    }

    /// Transform owned String into a leaked boxed slice and return the
    /// resulting `'static` reference which is suitable for storing in the list
    /// of symbols.
    ///
    /// The reference is wrapped in a `Slice::Owned` which will convert the
    /// reference back into a `Box` to be deallocated on `drop`.
    ///
    /// # Safety
    ///
    /// This function is not marked unsafe because the only side effect is
    /// leaking memory. Memory leaks are not unsafe.
    #[must_use]
    fn alloc(contents: String) -> Slice {
        let boxed_slice = contents.into_boxed_str();
        Slice::Owned(boxed_slice)
    }
}

impl<S> SymbolTable<S>
where
    S: BuildHasher,
{
    /// Intern a bytestring for the lifetime of the symbol table.
    ///
    /// The returned `Symbol` allows retrieving of the underlying bytes.
    /// Equal bytestrings will be inserted into the symbol table exactly once.
    ///
    /// This function only allocates if the underlying symbol table has no
    /// remaining capacity.
    ///
    /// # Errors
    ///
    /// If the symbol table would grow larger than `u32::MAX` interned
    /// bytestrings, the [`Symbol`] counter would overflow and a
    /// [`SymbolOverflowError`] is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// # use intaglio::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// let sym = table.intern("abc".to_string())?;
    /// table.intern("xyz".to_string())?;
    /// table.intern("123")?;
    /// table.intern("789")?;
    ///
    /// assert_eq!(4, table.len());
    /// assert_eq!(Some("abc"), table.get(sym));
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    pub fn intern<T>(&mut self, contents: T) -> Result<Symbol, SymbolOverflowError>
    where
        T: Into<Cow<'static, str>>,
    {
        let contents = contents.into();
        if let Some(&id) = self.map.get(contents.as_ref()) {
            return Ok(id);
        }
        let name = match contents {
            Cow::Borrowed(contents) => Slice::Static(contents),
            Cow::Owned(contents) => Self::alloc(contents),
        };
        let id = self.map.len().try_into()?;
        let slice = unsafe { name.as_static_slice() };

        self.map.insert(slice, id);
        self.vec.push(name);

        debug_assert!(self.get(id) == Some(slice));
        debug_assert!(self.intern(slice) == Ok(id));

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
    /// # use intaglio::{SymbolTable, Symbol};
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// assert!(!table.is_interned("abc"));
    /// assert_eq!(None, table.check_interned("abc"));
    ///
    /// table.intern("abc".to_string())?;
    /// assert!(table.is_interned("abc"));
    /// assert_eq!(Some(Symbol::new(0)), table.check_interned("abc"));
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    #[must_use]
    pub fn check_interned(&self, contents: &str) -> Option<Symbol> {
        self.map.get(contents).copied()
    }

    /// Returns `true` if the given byte string has been interned before.
    ///
    /// This method does not modify the symbol table.
    ///
    /// # Examples
    ///
    /// ```
    /// # use intaglio::{SymbolTable, Symbol};
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::new();
    /// assert!(!table.is_interned("abc"));
    /// assert_eq!(None, table.check_interned("abc"));
    ///
    /// table.intern("abc".to_string())?;
    /// assert!(table.is_interned("abc"));
    /// assert_eq!(Some(Symbol::new(0)), table.check_interned("abc"));
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    #[must_use]
    pub fn is_interned(&self, contents: &str) -> bool {
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
    /// # use intaglio::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::with_capacity(1);
    /// table.intern("abc")?;
    /// table.reserve(10);
    /// assert!(table.capacity() >= 11);
    /// # Ok(())
    /// # }
    /// # example().unwrap();
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
    /// table.intern("abc")?;
    /// table.intern("xyz")?;
    /// table.intern("123")?;
    /// table.shrink_to_fit();
    /// assert!(table.capacity() >= 3);
    /// # Ok(())
    /// # }
    /// # example().unwrap();
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

    use crate::str::SymbolTable;

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
        table.intern("1").unwrap();
        table.intern("2").unwrap();
        table.intern("3").unwrap();
        table.intern("4").unwrap();
        table.intern("5").unwrap();
        drop(table);
    }

    #[test]
    fn drop_with_owned_data() {
        let mut table = SymbolTable::new();
        table.intern("1".to_string()).unwrap();
        table.intern("2".to_string()).unwrap();
        table.intern("3".to_string()).unwrap();
        table.intern("4".to_string()).unwrap();
        table.intern("5".to_string()).unwrap();
        drop(table);
    }

    #[test]
    fn set_owned_value_and_get_with_owned_and_borrowed() {
        let mut table = SymbolTable::new();
        // intern an owned value
        let sym = table.intern("abc".to_string()).unwrap();
        // retrieve bytes
        assert_eq!("abc", table.get(sym).unwrap());
        // intern owned value again
        assert_eq!(sym, table.intern("abc".to_string()).unwrap());
        // intern borrowed value
        assert_eq!(sym, table.intern("abc").unwrap());
    }

    #[test]
    fn set_borrowed_value_and_get_with_owned_and_borrowed() {
        let mut table = SymbolTable::new();
        // intern a borrowed value
        let sym = table.intern("abc").unwrap();
        // retrieve bytes
        assert_eq!("abc", table.get(sym).unwrap());
        // intern owned value
        assert_eq!(sym, table.intern("abc".to_string()).unwrap());
        // intern borrowed value again
        assert_eq!(sym, table.intern("abc").unwrap());
    }

    #[quickcheck]
    fn intern_twice_symbol_equality(string: String) -> bool {
        let mut table = SymbolTable::new();
        let sym = table.intern(string.clone()).unwrap();
        let sym_again = table.intern(string).unwrap();
        sym == sym_again
    }

    #[quickcheck]
    fn intern_get_roundtrip(string: String) -> bool {
        let mut table = SymbolTable::new();
        let sym = table.intern(string.clone()).unwrap();
        let retrieved_bytes = table.get(sym).unwrap();
        string == retrieved_bytes
    }

    #[quickcheck]
    fn table_contains_sym(string: String) -> bool {
        let mut table = SymbolTable::new();
        let sym = table.intern(string).unwrap();
        table.contains(sym)
    }

    #[quickcheck]
    fn table_does_not_contain_missing_symbol_ids(sym: u32) -> bool {
        let table = SymbolTable::new();
        !table.contains(sym.into())
    }

    #[quickcheck]
    fn empty_table_does_not_report_any_interned_bytestrings(string: String) -> bool {
        let table = SymbolTable::new();
        !table.is_interned(string.as_str())
    }

    #[quickcheck]
    fn table_reports_interned_bytestrings_as_interned(string: String) -> bool {
        let mut table = SymbolTable::new();
        table.intern(string.clone()).unwrap();
        table.is_interned(string.as_str())
    }
}
