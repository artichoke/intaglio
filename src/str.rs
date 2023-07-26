//! Intaglio interner for UTF-8 [`String`]s.

use core::hash::BuildHasher;
use core::iter::{FromIterator, FusedIterator, Zip};
use core::marker::PhantomData;
use core::mem::ManuallyDrop;
use core::ops::Range;
use core::slice;
use std::borrow::Cow;
use std::collections::hash_map::{HashMap, RandomState};

use crate::internal::Interned;
use crate::{Symbol, SymbolOverflowError, DEFAULT_SYMBOL_TABLE_CAPACITY};

/// An iterator over all [`Symbol`]s in a [`SymbolTable`].
///
/// See the [`all_symbols`](SymbolTable::all_symbols) method in [`SymbolTable`].
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
    range: Range<usize>,
    // Hold a shared reference to the underlying `SymbolTable` to ensure the
    // table is not modified while we are iterating which would make the results
    // not match the real state.
    phantom: PhantomData<&'a SymbolTable>,
}

impl<'a> Iterator for AllSymbols<'a> {
    type Item = Symbol;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.range.next()?;
        debug_assert!(u32::try_from(next).is_ok());
        Some((next as u32).into())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.range.size_hint()
    }

    fn count(self) -> usize {
        self.range.count()
    }

    fn last(self) -> Option<Self::Item> {
        let last = self.range.last()?;
        debug_assert!(u32::try_from(last).is_ok());
        Some((last as u32).into())
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        let nth = self.range.nth(n)?;
        debug_assert!(u32::try_from(nth).is_ok());
        Some((nth as u32).into())
    }

    fn collect<B: FromIterator<Self::Item>>(self) -> B {
        self.range.map(|sym| Symbol::from(sym as u32)).collect()
    }
}

impl<'a> DoubleEndedIterator for AllSymbols<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let next = self.range.next_back()?;
        debug_assert!(u32::try_from(next).is_ok());
        Some((next as u32).into())
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        let nth = self.range.nth_back(n)?;
        debug_assert!(u32::try_from(nth).is_ok());
        Some((nth as u32).into())
    }
}

impl<'a> FusedIterator for AllSymbols<'a> {}

/// An iterator over all interned strings in a [`SymbolTable`].
///
/// See the [`strings`](SymbolTable::strings) method in [`SymbolTable`].
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
pub struct Strings<'a>(slice::Iter<'a, Interned<str>>);

impl<'a> Iterator for Strings<'a> {
    type Item = &'a str;

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

impl<'a> DoubleEndedIterator for Strings<'a> {
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

impl<'a> ExactSizeIterator for Strings<'a> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<'a> FusedIterator for Strings<'a> {}

/// An iterator over all symbols and interned strings in a [`SymbolTable`].
///
/// See the [`iter`](SymbolTable::iter) method in [`SymbolTable`].
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
pub struct Iter<'a>(Zip<AllSymbols<'a>, Strings<'a>>);

impl<'a> Iterator for Iter<'a> {
    type Item = (Symbol, &'a str);

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
    type Item = (Symbol, &'a str);
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// UTF-8 string interner.
///
/// This symbol table is implemented by storing UTF-8 strings with a fast path
/// for `&str` that are already `'static`.
///
/// See crate documentation for more.
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
    map: ManuallyDrop<HashMap<&'static str, Symbol, S>>,
    vec: ManuallyDrop<Vec<Interned<str>>>,
}

impl<S> Drop for SymbolTable<S> {
    fn drop(&mut self) {
        // SAFETY: No mutable references to `SymbolTable` internal fields are
        // given out, which means `ManuallyDrop::drop` can only be invoked in
        // this `Drop::drop` impl. Interal fields are guaranteed to be
        // initialized by `SymbolTable` constructors.
        unsafe {
            // `Interned` requires that the `'static` references it gives out
            // are dropped before the owning buffer stored in the `Interned`.
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
    /// # use intaglio::SymbolTable;
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
    /// The symbol table will be able to hold at least `capacity` strings
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
            map: ManuallyDrop::new(HashMap::with_capacity_and_hasher(capacity, hash_builder)),
            vec: ManuallyDrop::new(Vec::with_capacity(capacity)),
        }
    }

    /// Returns the number of strings the table can hold without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// # use intaglio::SymbolTable;
    /// let table = SymbolTable::with_capacity(10);
    /// assert!(table.capacity() >= 10);
    /// ```
    pub fn capacity(&self) -> usize {
        usize::min(self.vec.capacity(), self.map.capacity())
    }

    /// Returns the number of interned strings in the table.
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
    /// // only uniquely interned strings grow the symbol table.
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

    /// Returns `true` if the symbol table contains no interned strings.
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

    /// Returns a reference to the string associated with the given symbol.
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

    /// Returns an iterator over all [`Symbol`]s and strings in the
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
        AllSymbols {
            range: 0..self.len(),
            phantom: PhantomData,
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
    /// let strings = table.strings();
    /// assert_eq!(table.len(), strings.count());
    /// # Ok(())
    /// # }
    /// # example().unwrap();
    /// ```
    pub fn strings(&self) -> Strings<'_> {
        Strings(self.vec.iter())
    }
}

impl<S> SymbolTable<S>
where
    S: BuildHasher,
{
    /// Intern a string for the lifetime of the symbol table.
    ///
    /// The returned `Symbol` allows retrieving of the underlying string.
    /// Equal strings will be inserted into the symbol table exactly once.
    ///
    /// This function only allocates if the underlying symbol table has no
    /// remaining capacity.
    ///
    /// # Errors
    ///
    /// If the symbol table would grow larger than `u32::MAX` interned
    /// strings, the [`Symbol`] counter would overflow and a
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
        if let Some(&id) = self.map.get(&*contents) {
            return Ok(id);
        }

        // The `Interned::Owned` variant is derived from a `Box<T>`. When such
        // a structure is moved or assigned, as it is below in the call to
        // `self.vec.push`, the allocation is "retagged" in Miri/stacked borrows.
        //
        // Retagging an allocation pops all of the borrows derived from it off
        // of the stack. This means we need to move the `Interned` into the
        // `Vec` before calling `Interned::as_static_slice` to ensure the
        // reference does not get invalidated by retagging.
        //
        // However, that alone may be insufficient as the `Interened` may be
        // moved when the symbol table grows.
        //
        // The `SymbolTable` API prevents shared references to the `Interned`
        // being invalidated by a retag by tying resolved symbol contents,
        // `&'a T`, to `&'a SymbolTable`, which means the `SymbolTable` cannot
        // grow, shrink, or otherwise reallocate/move contents while a reference
        // to the `Interned`'s inner `T` is alive.
        //
        // To protect against future updates to stacked borrows or the unsafe
        // code operational semantics, we can address this additional invariant
        // with updated `Interned` internals which store the `Box<T>` in a raw
        // pointer form, which allows moves to be treated as untyped copies.
        //
        // See:
        //
        // - <https://github.com/artichoke/intaglio/issues/235>
        // - <https://github.com/artichoke/intaglio/pull/236>
        let name = Interned::from(contents);
        let id = Symbol::try_from(self.map.len())?;

        // Move the `Interned` into the `Vec`, causing it to be retagged under
        // stacked borrows, before taking any references to its inner `T`.
        self.vec.push(name);
        // Ensure we grow the map before we take any shared references to the
        // inner `T`.
        self.map.reserve(1);

        // SAFETY: `self.vec` is non-empty because the preceding line of code
        // pushed an entry into it.
        let name = unsafe { self.vec.last().unwrap_unchecked() };

        // SAFETY: This expression creates a reference with a `'static` lifetime
        // from an owned and interned buffer, which is permissible because:
        //
        // - `Interned` is an internal implementation detail of `SymbolTable`.
        // - `SymbolTable` never gives out `'static` references to underlying
        //   contents.
        // - All slice references given out by the `SymbolTable` have the same
        //   lifetime as the `SymbolTable`.
        // - The `map` field of `SymbolTable`, which contains the `'static`
        //   references, is dropped before the owned buffers stored in this
        //   `Interned`.
        // - The shared reference may be derived from a `PinBox` which prevents
        //   moves from retagging the underlying boxed `T` under stacked borrows.
        // - The symbol table cannot grow, shrink, or otherwise move its contents
        //   while this reference is alive.
        let slice = unsafe { name.as_static_slice() };

        self.map.insert(slice, id);

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

    /// Returns `true` if the given string has been interned before.
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
    /// # use intaglio::SymbolTable;
    /// # fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut table = SymbolTable::with_capacity(10);
    /// table.intern("abc")?;
    /// table.intern("xyz")?;
    /// table.intern("123")?;
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
        // retrieve string
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
        // retrieve string
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
        let retrieved_str = table.get(sym).unwrap();
        string == retrieved_str
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
    fn empty_table_does_not_report_any_interned_strings(string: String) -> bool {
        let table = SymbolTable::new();
        !table.is_interned(string.as_str())
    }

    #[quickcheck]
    fn table_reports_interned_strings_as_interned(string: String) -> bool {
        let mut table = SymbolTable::new();
        table.intern(string.clone()).unwrap();
        table.is_interned(string.as_str())
    }
}
