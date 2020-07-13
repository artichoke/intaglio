//! A Wrapper around interned strings that maintains the safety invariants of
//! the `'static` slices handed out to the interner.

use core::borrow::Borrow;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::ops::Deref;
use std::borrow::Cow;

/// Wrapper around `&'static` slices that does not allow mutable access to the
/// inner slice.
pub struct Interned<T: 'static + ?Sized>(Slice<T>);

impl<T> From<&'static T> for Interned<T>
where
    T: ?Sized,
{
    #[inline]
    fn from(slice: &'static T) -> Self {
        Self(slice.into())
    }
}

impl From<String> for Interned<str> {
    #[inline]
    fn from(owned: String) -> Self {
        Self(owned.into())
    }
}

impl From<Cow<'static, str>> for Interned<str> {
    #[inline]
    fn from(string: Cow<'static, str>) -> Self {
        Self(string.into())
    }
}

#[cfg(feature = "bytes")]
impl From<Vec<u8>> for Interned<[u8]> {
    #[inline]
    fn from(owned: Vec<u8>) -> Self {
        Self(owned.into())
    }
}

#[cfg(feature = "bytes")]
impl From<Cow<'static, [u8]>> for Interned<[u8]> {
    #[inline]
    fn from(bytes: Cow<'static, [u8]>) -> Self {
        Self(bytes.into())
    }
}

impl<T> Interned<T>
where
    T: ?Sized,
{
    /// Return a reference to the inner slice.
    #[inline]
    pub fn as_slice(&self) -> &T {
        self.0.as_slice()
    }

    /// Return a `'static` reference to the inner slice.
    ///
    /// # Safety
    ///
    /// This returns a reference with an unbounded lifetime. It is the caller's
    /// responsibility to make sure it is not used after this `Interned` and its
    /// inner `Slice` is dropped.
    #[inline]
    pub unsafe fn as_static_slice(&self) -> &'static T {
        self.0.as_static_slice()
    }
}

impl<T> Default for Interned<T>
where
    T: ?Sized,
    &'static T: Default,
{
    #[inline]
    fn default() -> Self {
        Self(Slice::default())
    }
}

impl fmt::Debug for Interned<str> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "{:#?}", self.0)
        } else {
            write!(f, "{:?}", self.0)
        }
    }
}

#[cfg(feature = "bytes")]
impl fmt::Debug for Interned<[u8]> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "{:#?}", self.0)
        } else {
            write!(f, "{:?}", self.0)
        }
    }
}

impl<T> Deref for Interned<T>
where
    T: ?Sized,
{
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T> PartialEq<Interned<T>> for Interned<T>
where
    T: ?Sized + PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<T> PartialEq<T> for Interned<T>
where
    T: ?Sized + PartialEq,
{
    #[inline]
    fn eq(&self, other: &T) -> bool {
        self.as_slice() == other
    }
}

impl PartialEq<String> for Interned<str> {
    #[inline]
    fn eq(&self, other: &String) -> bool {
        self.as_slice() == other
    }
}

impl PartialEq<Interned<str>> for String {
    #[inline]
    fn eq(&self, other: &Interned<str>) -> bool {
        self == other.as_slice()
    }
}

#[cfg(feature = "bytes")]
impl PartialEq<Vec<u8>> for Interned<[u8]> {
    #[inline]
    fn eq(&self, other: &Vec<u8>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

#[cfg(feature = "bytes")]
impl PartialEq<Interned<[u8]>> for Vec<u8> {
    #[inline]
    fn eq(&self, other: &Interned<[u8]>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<T> Eq for Interned<T> where T: ?Sized + PartialEq {}

impl<T> Hash for Interned<T>
where
    T: ?Sized + Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

impl<T> Borrow<T> for Interned<T>
where
    T: ?Sized,
{
    #[inline]
    fn borrow(&self) -> &T {
        self.as_slice()
    }
}

impl<T> Borrow<T> for &Interned<T>
where
    T: ?Sized,
{
    #[inline]
    fn borrow(&self) -> &T {
        self.as_slice()
    }
}

impl<T> AsRef<T> for Interned<T>
where
    T: ?Sized,
{
    #[inline]
    fn as_ref(&self) -> &T {
        self.as_slice()
    }
}

/// Wrapper around `&'static` slices.
///
/// # Safety
///
/// Even though `Box` is a "unique owner" of the data in the `Owned` varint, it
/// should not be mutably dereferenced, because `as_static_slice` promises the
/// slice to be valid as long as the `Slice` is not dropped.
///
/// This is achieved by not exposing the `Slice` enum directly and only allowing
/// shared access to its internals.
enum Slice<T: 'static + ?Sized> {
    /// True `'static` references.
    Static(&'static T),
    /// Owned `'static` references.
    Owned(Box<T>),
}

impl<T> From<&'static T> for Slice<T>
where
    T: ?Sized,
{
    #[inline]
    fn from(slice: &'static T) -> Self {
        Self::Static(slice)
    }
}

impl From<String> for Slice<str> {
    #[inline]
    fn from(owned: String) -> Self {
        Self::Owned(owned.into_boxed_str())
    }
}

impl From<Cow<'static, str>> for Slice<str> {
    #[inline]
    fn from(string: Cow<'static, str>) -> Self {
        match string {
            Cow::Borrowed(slice) => slice.into(),
            Cow::Owned(owned) => owned.into(),
        }
    }
}

#[cfg(feature = "bytes")]
impl From<Vec<u8>> for Slice<[u8]> {
    #[inline]
    fn from(owned: Vec<u8>) -> Self {
        Self::Owned(owned.into_boxed_slice())
    }
}

#[cfg(feature = "bytes")]
impl From<Cow<'static, [u8]>> for Slice<[u8]> {
    #[inline]
    fn from(bytes: Cow<'static, [u8]>) -> Self {
        match bytes {
            Cow::Borrowed(slice) => slice.into(),
            Cow::Owned(owned) => owned.into(),
        }
    }
}

impl<T> Slice<T>
where
    T: ?Sized,
{
    /// Return a reference to the inner slice.
    #[inline]
    fn as_slice(&self) -> &T {
        match self {
            Self::Static(slice) => slice,
            Self::Owned(owned) => &**owned,
        }
    }

    /// Return a `'static` reference to the inner slice.
    ///
    /// # Safety
    ///
    /// This returns a reference with an unbounded lifetime. It is the caller's
    /// responsibility to make sure it is not used after this `Slice` is
    /// dropped.
    #[inline]
    unsafe fn as_static_slice(&self) -> &'static T {
        match self {
            Self::Static(slice) => slice,
            #[allow(trivial_casts)]
            Self::Owned(owned) => &*(&**owned as *const T),
        }
    }
}

impl<T> Default for Slice<T>
where
    T: ?Sized,
    &'static T: Default,
{
    #[inline]
    fn default() -> Self {
        Self::Static(<_>::default())
    }
}

impl fmt::Debug for Slice<str> {
    /// Formats the string slice using the given formatter.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.as_slice())
    }
}

#[cfg(feature = "bytes")]
impl fmt::Debug for Slice<[u8]> {
    /// Formats the byte slice using the given formatter.
    ///
    /// If alternate format is specified, e.g. `{:#?}`, the slice is assumed to
    /// be conventionally UTF-8 and converted to a [`String`] lossily with
    /// [`String::from_utf8_lossy`].
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "{:?}", String::from_utf8_lossy(self.as_slice()))
        } else {
            write!(f, "{:?}", self.as_slice())
        }
    }
}

impl<T> Deref for Slice<T>
where
    T: ?Sized,
{
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T> PartialEq<Slice<T>> for Slice<T>
where
    T: ?Sized + PartialEq,
{
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<T> PartialEq<T> for Slice<T>
where
    T: ?Sized + PartialEq,
{
    #[inline]
    fn eq(&self, other: &T) -> bool {
        self.as_slice() == other
    }
}

impl PartialEq<String> for Slice<str> {
    #[inline]
    fn eq(&self, other: &String) -> bool {
        self.as_slice() == other
    }
}

impl PartialEq<Slice<str>> for String {
    #[inline]
    fn eq(&self, other: &Slice<str>) -> bool {
        self == other.as_slice()
    }
}

#[cfg(feature = "bytes")]
impl PartialEq<Vec<u8>> for Slice<[u8]> {
    #[inline]
    fn eq(&self, other: &Vec<u8>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

#[cfg(feature = "bytes")]
impl PartialEq<Slice<[u8]>> for Vec<u8> {
    #[inline]
    fn eq(&self, other: &Slice<[u8]>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<T> Eq for Slice<T> where T: ?Sized + PartialEq {}

impl<T> Hash for Slice<T>
where
    T: ?Sized + Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_slice().hash(state);
    }
}

impl<T> Borrow<T> for Slice<T>
where
    T: ?Sized,
{
    #[inline]
    fn borrow(&self) -> &T {
        self.as_slice()
    }
}

impl<T> Borrow<T> for &Slice<T>
where
    T: ?Sized,
{
    #[inline]
    fn borrow(&self) -> &T {
        self.as_slice()
    }
}

impl<T> AsRef<T> for Slice<T>
where
    T: ?Sized,
{
    #[inline]
    fn as_ref(&self) -> &T {
        self.as_slice()
    }
}
