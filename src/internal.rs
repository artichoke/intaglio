//! A Wrapper around interned strings that maintains the safety invariants of
//! the `'static` slices handed out to the interner.

use core::fmt;
use std::borrow::Cow;
#[cfg(feature = "cstr")]
use std::ffi::{CStr, CString};
#[cfg(feature = "osstr")]
use std::ffi::{OsStr, OsString};
#[cfg(feature = "path")]
use std::path::{Path, PathBuf};

/// Wrapper around `&'static` slices that does not allow mutable access to the
/// inner slice.
pub struct Interned<T: 'static + ?Sized>(Slice<T>);

impl From<Cow<'static, str>> for Interned<str> {
    #[inline]
    fn from(cow: Cow<'static, str>) -> Self {
        Self(cow.into())
    }
}

#[cfg(feature = "bytes")]
impl From<Cow<'static, [u8]>> for Interned<[u8]> {
    #[inline]
    fn from(cow: Cow<'static, [u8]>) -> Self {
        Self(cow.into())
    }
}

#[cfg(feature = "cstr")]
impl From<Cow<'static, CStr>> for Interned<CStr> {
    #[inline]
    fn from(cow: Cow<'static, CStr>) -> Self {
        Self(cow.into())
    }
}

#[cfg(feature = "osstr")]
impl From<Cow<'static, OsStr>> for Interned<OsStr> {
    #[inline]
    fn from(cow: Cow<'static, OsStr>) -> Self {
        Self(cow.into())
    }
}

#[cfg(feature = "path")]
impl From<Cow<'static, Path>> for Interned<Path> {
    #[inline]
    fn from(cow: Cow<'static, Path>) -> Self {
        Self(cow.into())
    }
}

impl<T> Interned<T>
where
    T: ?Sized,
{
    /// Return a reference to the inner slice.
    #[inline]
    pub const fn as_slice(&self) -> &T {
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
        // SAFETY: `Interned::as_static_slice`'s caller upheld safety invariants
        // are the same as `Slice::as_static_slice`'s caller upheld safety
        // invariants.
        unsafe { self.0.as_static_slice() }
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

#[cfg(feature = "cstr")]
impl fmt::Debug for Interned<CStr> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "{:#?}", self.0)
        } else {
            write!(f, "{:?}", self.0)
        }
    }
}

#[cfg(feature = "osstr")]
impl fmt::Debug for Interned<OsStr> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "{:#?}", self.0)
        } else {
            write!(f, "{:?}", self.0)
        }
    }
}

#[cfg(feature = "path")]
impl fmt::Debug for Interned<Path> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "{:#?}", self.0)
        } else {
            write!(f, "{:?}", self.0)
        }
    }
}

/// Wrapper around `&'static` slices.
///
/// # Safety
///
/// Even though `Box` is a "unique owner" of the data in the `Owned` variant, it
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
    fn from(cow: Cow<'static, str>) -> Self {
        match cow {
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
    fn from(cow: Cow<'static, [u8]>) -> Self {
        match cow {
            Cow::Borrowed(slice) => slice.into(),
            Cow::Owned(owned) => owned.into(),
        }
    }
}

#[cfg(feature = "cstr")]
impl From<CString> for Slice<CStr> {
    #[inline]
    fn from(owned: CString) -> Self {
        Self::Owned(owned.into_boxed_c_str())
    }
}

#[cfg(feature = "cstr")]
impl From<Cow<'static, CStr>> for Slice<CStr> {
    #[inline]
    fn from(cow: Cow<'static, CStr>) -> Self {
        match cow {
            Cow::Borrowed(slice) => slice.into(),
            Cow::Owned(owned) => owned.into(),
        }
    }
}

#[cfg(feature = "osstr")]
impl From<OsString> for Slice<OsStr> {
    #[inline]
    fn from(owned: OsString) -> Self {
        Self::Owned(owned.into_boxed_os_str())
    }
}

#[cfg(feature = "osstr")]
impl From<Cow<'static, OsStr>> for Slice<OsStr> {
    #[inline]
    fn from(cow: Cow<'static, OsStr>) -> Self {
        match cow {
            Cow::Borrowed(slice) => slice.into(),
            Cow::Owned(owned) => owned.into(),
        }
    }
}

#[cfg(feature = "path")]
impl From<PathBuf> for Slice<Path> {
    #[inline]
    fn from(owned: PathBuf) -> Self {
        Self::Owned(owned.into_boxed_path())
    }
}

#[cfg(feature = "path")]
impl From<Cow<'static, Path>> for Slice<Path> {
    #[inline]
    fn from(cow: Cow<'static, Path>) -> Self {
        match cow {
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
    const fn as_slice(&self) -> &T {
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
            Self::Owned(owned) => {
                // Coerce the `Box<T>` to a pointer.
                let ptr: *const T = &**owned;
                // SAFETY: This expression creates a reference with a `'static`
                // lifetime from an owned buffer, which is permissible because:
                //
                // - `Slice` is an internal implementation detail of the various
                //   symbol table data structures
                // - The various symbol tables never give out `'static` references
                //   to underlying byte contents.
                // - The `map` field of the various symbol tables which contains
                //   the `'static` references, is dropped before the owned buffers
                //   stored in this `Slice`.
                unsafe {
                    // Coerce the pointer to a `&'static T`.
                    &*ptr
                }
            }
        }
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

#[cfg(feature = "cstr")]
impl fmt::Debug for Slice<CStr> {
    /// Formats the `CStr` slice using the given formatter.
    ///
    /// If alternate format is specified, e.g. `{:#?}`, the slice is assumed to
    /// be conventionally UTF-8 and converted to a [`String`] lossily with
    /// [`String::from_utf8_lossy`].
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(
                f,
                "{:?}",
                String::from_utf8_lossy(self.as_slice().to_bytes())
            )
        } else {
            write!(f, "{:?}", self.as_slice())
        }
    }
}

#[cfg(feature = "osstr")]
impl fmt::Debug for Slice<OsStr> {
    /// Formats the `OsStr` slice using the given formatter.
    ///
    /// If alternate format is specified, e.g. `{:#?}`, the slice is assumed to
    /// be conventionally UTF-8 and converted to a [`String`] lossily with
    /// [`OsStr::to_string_lossy`].
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "{:?}", self.as_slice().to_string_lossy())
        } else {
            write!(f, "{:?}", self.as_slice())
        }
    }
}

#[cfg(feature = "path")]
impl fmt::Debug for Slice<Path> {
    /// Formats the `Path` slice using the given formatter.
    ///
    /// If alternate format is specified, e.g. `{:#?}`, the slice is assumed to
    /// be conventionally UTF-8 and converted to a [`String`] lossily with
    /// [`Path::to_string_lossy`].
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "{:?}", self.as_slice().to_string_lossy())
        } else {
            write!(f, "{:?}", self.as_slice())
        }
    }
}
