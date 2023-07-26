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

use self::boxed::PinBox;

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
        // SAFETY: `Interned::as_static_slice`'s caller upheld safety invariants
        // are the same as `Slice::as_static_slice`'s caller upheld safety
        // invariants.
        unsafe { self.0.as_static_slice() }
    }
}

impl fmt::Debug for Interned<str> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

#[cfg(feature = "bytes")]
impl fmt::Debug for Interned<[u8]> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

#[cfg(feature = "cstr")]
impl fmt::Debug for Interned<CStr> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

#[cfg(feature = "osstr")]
impl fmt::Debug for Interned<OsStr> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

#[cfg(feature = "path")]
impl fmt::Debug for Interned<Path> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
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
    Owned(PinBox<T>),
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
        Self::Owned(PinBox::new(owned.into_boxed_str()))
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
        Self::Owned(PinBox::new(owned.into_boxed_slice()))
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
        Self::Owned(PinBox::new(owned.into_boxed_c_str()))
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
        Self::Owned(PinBox::new(owned.into_boxed_os_str()))
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
        Self::Owned(PinBox::new(owned.into_boxed_path()))
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
    fn as_slice(&self) -> &T {
        match self {
            Self::Static(slice) => slice,
            Self::Owned(owned) => {
                // SAFETY: `PinBox` acts like `Box`.
                unsafe { owned.as_ref() }
            }
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
                // - `PinBox` acts like `Box`.
                unsafe {
                    // Coerce the pointer to a `&'static T`.
                    owned.as_ref()
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

/// An abstraction over a `Box<T>` where T is an unsized slice type which moves
/// the box by raw pointer. This type is required to satisfy Miri with
/// `-Zmiri-retag-fields`. See #235, #236.
///
/// The `PinBox` type is derived from:
///
/// - <https://github.com/CAD97/simple-interner/blob/24a836e9f8a0173faf48438d711442c2a86659c1/src/interner.rs#L26-L56>
/// - <https://github.com/artichoke/intaglio/pull/236#issuecomment-1651058752>
/// - <https://github.com/artichoke/intaglio/pull/236#issuecomment-1652003240>
///
/// This code is placed into the public domain by @CAD97:
///
/// - <https://github.com/artichoke/intaglio/pull/236#issuecomment-1652393974>
mod boxed {
    use core::fmt;
    use core::marker::PhantomData;
    use core::ptr::NonNull;

    /// A wrapper around box that does not provide &mut access to the pointee and
    /// uses raw-pointer borrowing rules to avoid invalidating extant references.
    ///
    /// The resolved reference is guaranteed valid until the `PinBox` is dropped.
    ///
    /// This type is meant to allow the owned data in the given `Box<T>` to be moved
    /// without being retagged by Miri. See #235, #236.
    pub(crate) struct PinBox<T: ?Sized> {
        ptr: NonNull<T>,
        _marker: PhantomData<Box<T>>,
    }

    impl<T: ?Sized> PinBox<T> {
        #[inline]
        pub(crate) fn new(x: Box<T>) -> Self {
            let ptr = Box::into_raw(x);
            // SAFETY: `ptr` is derived from `Box::into_raw` and can never be null.
            let ptr = unsafe { NonNull::new_unchecked(ptr) };
            Self {
                ptr,
                _marker: PhantomData,
            }
        }

        #[inline]
        pub(crate) unsafe fn as_ref<'a>(&self) -> &'a T {
            // SAFETY: `PinBox` acts like `Box`, `self.ptr` is non-null and points
            // to a live `Box`.
            unsafe { self.ptr.as_ref() }
        }
    }

    impl<T: ?Sized> Drop for PinBox<T> {
        fn drop(&mut self) {
            // SAFETY: `PinBox` acts like `Box`.
            unsafe {
                drop(Box::from_raw(self.ptr.as_ptr()));
            }
        }
    }

    impl<T: ?Sized + fmt::Debug> fmt::Debug for PinBox<T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            // SAFETY: `PinBox` acts like `Box`.
            let s = unsafe { self.as_ref() };
            s.fmt(f)
        }
    }

    #[cfg(test)]
    mod tests {
        use core::fmt::Write;

        use super::PinBox;

        #[test]
        fn test_drop() {
            let x = "abc".to_string().into_boxed_str();
            let x = PinBox::new(x);
            drop(x);
        }

        #[test]
        fn test_as_ref() {
            let x = "abc".to_string().into_boxed_str();
            let x = PinBox::new(x);

            // SAFETY: `PinBox` acts like `Box` and contains a valid pointer.
            assert_eq!(unsafe { x.as_ref() }, "abc");
        }

        #[test]
        fn test_debug_format() {
            let x = "abc".to_string().into_boxed_str();
            let x = PinBox::new(x);

            let mut buf = String::new();
            write!(&mut buf, "{x:?}").unwrap();
            assert_eq!(buf, "\"abc\"");
        }
    }
}

#[cfg(test)]
mod tests {
    use core::fmt::Write;
    use std::borrow::Cow;
    #[cfg(feature = "cstr")]
    use std::ffi::CStr;
    #[cfg(feature = "osstr")]
    use std::ffi::OsStr;
    #[cfg(feature = "path")]
    use std::path::Path;

    use super::Interned;

    #[test]
    fn test_interned_static_str_debug_format() {
        let s = Interned::from(Cow::Borrowed("abc"));
        let mut buf = String::new();
        write!(&mut buf, "{s:?}").unwrap();
        assert_eq!(buf, "\"abc\"");
    }

    #[test]
    fn test_interned_owned_str_debug_format() {
        let s = Interned::<str>::from(Cow::Owned("abc".to_string()));
        let mut buf = String::new();
        write!(&mut buf, "{s:?}").unwrap();
        assert_eq!(buf, "\"abc\"");
    }

    #[test]
    #[cfg(feature = "bytes")]
    fn test_interned_static_bytes_debug_format() {
        let s = Interned::from(Cow::Borrowed(&b"abc"[..]));
        let mut buf = String::new();
        write!(&mut buf, "{s:?}").unwrap();
        assert_eq!(buf, "[97, 98, 99]");

        let s = Interned::from(Cow::Borrowed(&b"\xFF"[..]));
        let mut buf = String::new();
        write!(&mut buf, "{s:?}").unwrap();
        assert_eq!(buf, "[255]");

        let s = Interned::from(Cow::Borrowed(&b"abc"[..]));
        let mut buf = String::new();
        write!(&mut buf, "{s:#?}").unwrap();
        assert_eq!(buf, "\"abc\"");

        let s = Interned::from(Cow::Borrowed(&b"\xFF"[..]));
        let mut buf = String::new();
        write!(&mut buf, "{s:#?}").unwrap();
        assert_eq!(buf, "\"\u{FFFD}\"");
    }

    #[test]
    #[cfg(feature = "bytes")]
    fn test_interned_owned_bytes_debug_format() {
        let s = Interned::<[u8]>::from(Cow::Owned(b"abc".to_vec()));
        let mut buf = String::new();
        write!(&mut buf, "{s:?}").unwrap();
        assert_eq!(buf, "[97, 98, 99]");

        let s = Interned::<[u8]>::from(Cow::Owned(b"\xFF".to_vec()));
        let mut buf = String::new();
        write!(&mut buf, "{s:?}").unwrap();
        assert_eq!(buf, "[255]");

        let s = Interned::<[u8]>::from(Cow::Owned(b"abc".to_vec()));
        let mut buf = String::new();
        write!(&mut buf, "{s:#?}").unwrap();
        assert_eq!(buf, "\"abc\"");

        let s = Interned::<[u8]>::from(Cow::Owned(b"\xFF".to_vec()));
        let mut buf = String::new();
        write!(&mut buf, "{s:#?}").unwrap();
        assert_eq!(buf, "\"\u{FFFD}\"");
    }

    #[test]
    #[cfg(feature = "cstr")]
    fn test_interned_static_cstr_debug_format() {
        let s = Interned::from(Cow::Borrowed(
            CStr::from_bytes_with_nul(b"abc\x00").unwrap(),
        ));
        let mut buf = String::new();
        write!(&mut buf, "{s:?}").unwrap();
        assert_eq!(buf, "\"abc\"");

        let s = Interned::from(Cow::Borrowed(
            CStr::from_bytes_with_nul(b"\xFF\x00").unwrap(),
        ));
        let mut buf = String::new();
        write!(&mut buf, "{s:?}").unwrap();
        assert_eq!(buf, r#""\xff""#);

        let s = Interned::from(Cow::Borrowed(
            CStr::from_bytes_with_nul(b"abc\x00").unwrap(),
        ));
        let mut buf = String::new();
        write!(&mut buf, "{s:#?}").unwrap();
        assert_eq!(buf, "\"abc\"");

        let s = Interned::from(Cow::Borrowed(
            CStr::from_bytes_with_nul(b"\xFF\x00").unwrap(),
        ));
        let mut buf = String::new();
        write!(&mut buf, "{s:#?}").unwrap();
        assert_eq!(buf, "\"\u{FFFD}\"");
    }

    #[test]
    #[cfg(feature = "cstr")]
    fn test_interned_owned_cstring_debug_format() {
        let s = Interned::<CStr>::from(Cow::Owned(
            CStr::from_bytes_with_nul(b"abc\x00").unwrap().to_owned(),
        ));
        let mut buf = String::new();
        write!(&mut buf, "{s:?}").unwrap();
        assert_eq!(buf, "\"abc\"");

        let s = Interned::<CStr>::from(Cow::Owned(
            CStr::from_bytes_with_nul(b"\xFF\x00").unwrap().to_owned(),
        ));
        let mut buf = String::new();
        write!(&mut buf, "{s:?}").unwrap();
        assert_eq!(buf, r#""\xff""#);

        let s = Interned::<CStr>::from(Cow::Owned(
            CStr::from_bytes_with_nul(b"abc\x00").unwrap().to_owned(),
        ));
        let mut buf = String::new();
        write!(&mut buf, "{s:#?}").unwrap();
        assert_eq!(buf, "\"abc\"");

        let s = Interned::<CStr>::from(Cow::Owned(
            CStr::from_bytes_with_nul(b"\xFF\x00").unwrap().to_owned(),
        ));
        let mut buf = String::new();
        write!(&mut buf, "{s:#?}").unwrap();
        assert_eq!(buf, "\"\u{FFFD}\"");
    }

    #[test]
    #[cfg(feature = "osstr")]
    fn test_interned_static_osstr_debug_format() {
        let s = Interned::from(Cow::Borrowed(OsStr::new("abc")));
        let mut buf = String::new();
        write!(&mut buf, "{s:?}").unwrap();
        assert_eq!(buf, "\"abc\"");

        let s = Interned::from(Cow::Borrowed(OsStr::new("abc")));
        let mut buf = String::new();
        write!(&mut buf, "{s:#?}").unwrap();
        assert_eq!(buf, "\"abc\"");
    }

    #[test]
    #[cfg(feature = "osstr")]
    fn test_interned_owned_osstring_debug_format() {
        let s = Interned::<OsStr>::from(Cow::Owned(OsStr::new("abc").to_owned()));
        let mut buf = String::new();
        write!(&mut buf, "{s:?}").unwrap();
        assert_eq!(buf, "\"abc\"");

        let s = Interned::<OsStr>::from(Cow::Owned(OsStr::new("abc").to_owned()));
        let mut buf = String::new();
        write!(&mut buf, "{s:#?}").unwrap();
        assert_eq!(buf, "\"abc\"");
    }

    #[test]
    #[cfg(feature = "path")]
    fn test_interned_static_path_debug_format() {
        let s = Interned::from(Cow::Borrowed(Path::new("abc")));
        let mut buf = String::new();
        write!(&mut buf, "{s:?}").unwrap();
        assert_eq!(buf, "\"abc\"");

        let s = Interned::from(Cow::Borrowed(Path::new("abc")));
        let mut buf = String::new();
        write!(&mut buf, "{s:#?}").unwrap();
        assert_eq!(buf, "\"abc\"");
    }

    #[test]
    #[cfg(feature = "path")]
    fn test_interned_owned_pathbuf_debug_format() {
        let s = Interned::<Path>::from(Cow::Owned(Path::new("abc").to_owned()));
        let mut buf = String::new();
        write!(&mut buf, "{s:?}").unwrap();
        assert_eq!(buf, "\"abc\"");

        let s = Interned::<Path>::from(Cow::Owned(Path::new("abc").to_owned()));
        let mut buf = String::new();
        write!(&mut buf, "{s:#?}").unwrap();
        assert_eq!(buf, "\"abc\"");
    }
}
