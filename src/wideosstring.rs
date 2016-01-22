use std;
use std::string;
use std::mem;
use std::ops;
use std::ffi::{OsString, OsStr};
use std::os::windows::ffi::{OsStringExt, OsStrExt};

/// Owned, mutable Wide OS strings.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct WideOsString {
    inner: Vec<u16>,
}

/// Slices into Wide OS strings.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct WideOsStr {
    inner: [u16],
}

impl WideOsString {
    /// Constructs a new empty `WideOsString`.
    pub fn new() -> WideOsString {
        WideOsString { inner: vec![] }
    }

    /// Constructs a `WideOsString` from a possibly ill-formed UTF-16 slice.
    pub fn from_raw<R>(raw: R) -> WideOsString
        where R: Into<Vec<u16>>
    {
        WideOsString { inner: raw.into() }
    }

    /// Encodes a `WideOsString` from an `OsStr` slice.
    pub fn from_str<S: AsRef<OsStr> + ?Sized>(s: &S) -> WideOsString {
        WideOsString { inner: s.as_ref().encode_wide().collect() }
    }

    /// Converts to a `WideOsStr` slice.
    pub fn as_wide_os_str(&self) -> &WideOsStr {
        self
    }

    /// Converts the `WideOsString` to a `String` if it contains valid Unicode data.
    pub fn to_string(&self) -> Result<String, string::FromUtf16Error> {
        String::from_utf16(&self.inner)
    }

    /// Converts the `WideOsString` to a `String`.
    ///
    /// Any non-Unicode sequences are replaced with U+FFFD REPLACEMENT CHARACTER.
    pub fn to_string_lossy(&self) -> String {
        String::from_utf16_lossy(&self.inner)
    }

    /// Converts the `WideOsString` to a `OsString`.
    pub fn to_os_string(&self) -> OsString {
        OsString::from_wide(&self.inner)
    }

    /// Extends the string with the given `&WideOsStr` slice.
    pub fn push<T: AsRef<WideOsStr>>(&mut self, s: T) {
        self.inner.extend_from_slice(&s.as_ref().inner)
    }

    /// Extends the string with the given `&WideOsStr` slice.
    pub fn push_str<T: AsRef<OsStr>>(&mut self, s: T) {
        self.inner.extend(s.as_ref().encode_wide())
    }
}

impl Into<Vec<u16>> for WideOsString {
    fn into(self) -> Vec<u16> {
        self.inner
    }
}

impl From<String> for WideOsString {
    fn from(s: String) -> WideOsString {
        WideOsString::from_str(&s)
    }
}

impl From<OsString> for WideOsString {
    fn from(s: OsString) -> WideOsString {
        WideOsString::from_str(&s)
    }
}

impl From<WideOsString> for OsString {
    fn from(s: WideOsString) -> OsString {
        s.to_os_string()
    }
}

impl<'a, T: ?Sized + AsRef<WideOsStr>> From<&'a T> for WideOsString {
    fn from(s: &'a T) -> WideOsString {
        s.as_ref().to_wide_os_string()
    }
}

impl ops::Index<ops::RangeFull> for WideOsString {
    type Output = WideOsStr;

    #[inline]
    fn index(&self, _index: ops::RangeFull) -> &WideOsStr {
        WideOsStr::from_inner(&self.inner)
    }
}

impl ops::Deref for WideOsString {
    type Target = WideOsStr;

    #[inline]
    fn deref(&self) -> &WideOsStr {
        &self[..]
    }
}

impl WideOsStr {
    /// Coerces into a `WideOsStr` slice.
    pub fn new<S: AsRef<WideOsStr> + ?Sized>(s: &S) -> &WideOsStr {
        s.as_ref()
    }

    fn from_inner(inner: &[u16]) -> &WideOsStr {
        unsafe { mem::transmute(inner) }
    }

    /// Copies the slice into an owned `OsString`.
    pub fn to_os_string(&self) -> OsString {
        OsString::from_wide(&self.inner)
    }

    /// Copies the slice into an owned `WideOsString`.
    pub fn to_wide_os_string(&self) -> WideOsString {
        WideOsString { inner: self.inner.to_owned() }
    }

    /// Converts the slice to a `String` if it contains valid Unicode data.
    pub fn to_string(&self) -> Result<String, string::FromUtf16Error> {
        String::from_utf16(&self.inner)
    }

    /// Converts the slice to a `String`.
    ///
    /// Any non-Unicode sequences are replaced with U+FFFD REPLACEMENT CHARACTER.
    pub fn to_string_lossy(&self) -> String {
        String::from_utf16_lossy(&self.inner)
    }
}

impl std::borrow::Borrow<WideOsStr> for WideOsString {
    fn borrow(&self) -> &WideOsStr {
        &self[..]
    }
}

impl ToOwned for WideOsStr {
    type Owned = WideOsString;
    fn to_owned(&self) -> WideOsString {
        self.to_wide_os_string()
    }
}

impl AsRef<WideOsStr> for WideOsStr {
    fn as_ref(&self) -> &WideOsStr {
        self
    }
}

impl AsRef<WideOsStr> for WideOsString {
    fn as_ref(&self) -> &WideOsStr {
        self
    }
}

impl AsRef<[u16]> for WideOsStr {
    fn as_ref(&self) -> &[u16] {
        &self.inner
    }
}

impl AsRef<[u16]> for WideOsString {
    fn as_ref(&self) -> &[u16] {
        &self.inner
    }
}
