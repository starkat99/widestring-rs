use std;
use std::mem;
use std::ffi::{OsString, OsStr};
use std::os::windows::ffi::{OsStringExt, OsStrExt};

/// An owned, mutable "wide" string for windows FFI that is *not* nul-aware.
///
/// `WideString` is not aware of nul values. Strings may or may not be nul-terminated, and may
/// contain invalid and ill-formed UTF-16 data. These values are intended to be used with windows
/// FFI functions that directly use string length, where the values are known to have proper
/// nul-termination already, or where strings are merely being passed through without modification.
///
/// `WideCString` should be used instead if nul-aware strings are required.
///
/// `WideString` values can be converted to and from many other string types, including `OsString`
/// and `String`, making proper Unicode windows FFI safe and easy.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct WideString {
    inner: Vec<u16>,
}

/// Wide string reference for `WideString`.
///
/// `WideStr` is aware of nul values. Strings may or may not be nul-terminated, and may
/// contain invalid and ill-formed UTF-16 data. These values are intended to be used with windows
/// FFI functions that directly use string length, where the values are known to have proper
/// nul-termination already, or where strings are merely being passed through without modification.
///
/// `WideCStr` should be used instead of nul-aware strings are required.
///
/// `WideStr` values can be converted to many other string types, including `OsString` and `String`,
/// making proper Unicode windows FFI safe and easy.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct WideStr {
    inner: [u16],
}

impl WideString {
    /// Constructs a new empty `WideString`.
    pub fn new() -> WideString {
        WideString { inner: vec![] }
    }

    /// Constructs a `WideString` from a vector of possibly invalid or ill-formed UTF-16 data.
    ///
    /// No checks are made on the contents of the vector.
    pub fn from_vec<T: Into<Vec<u16>>>(raw: T) -> WideString {
        WideString { inner: raw.into() }
    }

    /// Encodes a `WideString` copy from an `OsStr`.
    ///
    /// This makes a wide string copy of the `OsStr`. Since `OsStr` makes no guaruntees that it is
    /// valid UTF-8, there is no guaruntee that the resulting `WideString` will be valid UTF-16.
    pub fn from_str<S: AsRef<OsStr> + ?Sized>(s: &S) -> WideString {
        WideString { inner: s.as_ref().encode_wide().collect() }
    }

    /// Constructs a `WideString` from a `u16` pointer and a length.
    ///
    /// The `len` argument is the number of *elements*, not the number of bytes.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements.
    ///
    /// # Panics
    ///
    /// Panics if `len` is greater than 0 but `p` is a null pointer.
    pub unsafe fn from_ptr(p: *const u16, len: usize) -> WideString {
        if len == 0 {
            return WideString::new();
        }
        assert!(!p.is_null());
        let slice = std::slice::from_raw_parts(p, len);
        WideString::from_vec(slice)
    }

    /// Converts to a `WideStr` reference.
    pub fn as_wide_str(&self) -> &WideStr {
        self
    }

    /// Converts the wide string into a `Vec<u16>`, consuming the string in the process.
    pub fn into_vec(self) -> Vec<u16> {
        self.inner
    }

    /// Extends the wide string with the given `&WideStr`.
    ///
    /// No checks are performed on the strings. It is possible to end up nul values inside the
    /// string, and it is up to the caller to determine if that is acceptable.
    pub fn push<T: AsRef<WideStr>>(&mut self, s: T) {
        self.inner.extend_from_slice(&s.as_ref().inner)
    }

    /// Extends the wide string with the given `&[u16]` slice.
    ///
    /// No checks are performed on the strings. It is possible to end up nul values inside the
    /// string, and it is up to the caller to determine if that is acceptable.
    pub fn push_slice<T: AsRef<[u16]>>(&mut self, s: T) {
        self.inner.extend_from_slice(&s.as_ref())
    }

    /// Extends the string with the given `&OsStr`.
    ///
    /// No checks are performed on the strings. It is possible to end up nul values inside the
    /// string, and it is up to the caller to determine if that is acceptable.
    pub fn push_str<T: AsRef<OsStr>>(&mut self, s: T) {
        self.inner.extend(s.as_ref().encode_wide())
    }
}

impl Into<Vec<u16>> for WideString {
    fn into(self) -> Vec<u16> {
        self.into_vec()
    }
}

impl From<String> for WideString {
    fn from(s: String) -> WideString {
        WideString::from_str(&s)
    }
}

impl From<OsString> for WideString {
    fn from(s: OsString) -> WideString {
        WideString::from_str(&s)
    }
}

impl From<WideString> for OsString {
    fn from(s: WideString) -> OsString {
        s.to_os_string()
    }
}

impl<'a, T: ?Sized + AsRef<WideStr>> From<&'a T> for WideString {
    fn from(s: &'a T) -> WideString {
        s.as_ref().to_wide_string()
    }
}

impl std::ops::Index<std::ops::RangeFull> for WideString {
    type Output = WideStr;

    #[inline]
    fn index(&self, _index: std::ops::RangeFull) -> &WideStr {
        WideStr::from_slice(&self.inner)
    }
}

impl std::ops::Deref for WideString {
    type Target = WideStr;

    #[inline]
    fn deref(&self) -> &WideStr {
        &self[..]
    }
}

impl WideStr {
    /// Coerces a value into a `WideStr`.
    pub fn new<'a, S: AsRef<WideStr> + ?Sized>(s: &'a S) -> &'a WideStr {
        s.as_ref()
    }

    /// Constructs a `WideStr` from a `u16` pointer and a length.
    ///
    /// The `len` argument is the number of *elements*, not the number of bytes.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements.
    ///
    /// # Panics
    ///
    /// This function panics if `p` is null.
    ///
    /// # Caveat
    ///
    /// The lifetime for the returned string is inferred from its usage. To prevent accidental
    /// misuse, it's suggested to tie the lifetime to whichever source lifetime is safe in the
    /// context, such as by providing a helper function taking the lifetime of a host value for the
    /// string, or by explicit annotation.
    pub unsafe fn from_ptr<'a>(p: *const u16, len: usize) -> &'a WideStr {
        assert!(!p.is_null());
        mem::transmute(std::slice::from_raw_parts(p, len))
    }

    /// Constructs a `WideStr` from a slice of `u16` values.
    ///
    /// No checks are performed on the slice.
    pub fn from_slice<'a>(slice: &'a [u16]) -> &'a WideStr {
        unsafe { mem::transmute(slice) }
    }

    /// Decodes a wide string to an owned `OsString`.
    ///
    /// This makes a string copy of the `WideStr`. Since `WideStr` makes no guaruntees that it is
    /// valid UTF-16, there is no guaruntee that the resulting `OsString` will be valid UTF-8.
    pub fn to_os_string(&self) -> OsString {
        OsString::from_wide(&self.inner)
    }

    /// Copies the wide string to a new owned `WideString`.
    pub fn to_wide_string(&self) -> WideString {
        WideString::from_vec(&self.inner)
    }

    /// Copies the wide string to a `String` if it contains valid UTF-16 data.
    ///
    /// # Failures
    ///
    /// Returns an error if the string contains any invalid UTF-16 data.
    pub fn to_string(&self) -> Result<String, std::string::FromUtf16Error> {
        String::from_utf16(&self.inner)
    }

    /// Copies the wide string to a `String`.
    ///
    /// Any non-Unicode sequences are replaced with U+FFFD REPLACEMENT CHARACTER.
    pub fn to_string_lossy(&self) -> String {
        String::from_utf16_lossy(&self.inner)
    }

    /// Converts to a slice of the wide string.
    pub fn as_slice(&self) -> &[u16] {
        &self.inner
    }

    /// Returns a raw pointer to the wide string.
    ///
    /// The pointer is valid only as long as the lifetime of this reference.
    pub fn as_ptr(&self) -> *const u16 {
        self.inner.as_ptr()
    }

    /// Returns the length of the wide string as number of UTF-16 values.
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns whether this wide string contains no data.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

impl std::borrow::Borrow<WideStr> for WideString {
    fn borrow(&self) -> &WideStr {
        &self[..]
    }
}

impl ToOwned for WideStr {
    type Owned = WideString;
    fn to_owned(&self) -> WideString {
        self.to_wide_string()
    }
}

impl AsRef<WideStr> for WideStr {
    fn as_ref(&self) -> &WideStr {
        self
    }
}

impl AsRef<WideStr> for WideString {
    fn as_ref(&self) -> &WideStr {
        self
    }
}

impl AsRef<[u16]> for WideStr {
    fn as_ref(&self) -> &[u16] {
        self.as_slice()
    }
}

impl AsRef<[u16]> for WideString {
    fn as_ref(&self) -> &[u16] {
        self.as_slice()
    }
}
