use super::super::platform;
use std;
use std::ffi::{OsStr, OsString};
use std::mem;

/// An owned, mutable "wide" string for FFI that is **not** nul-aware.
///
/// `U16String` is not aware of nul values. Strings may or may not be nul-terminated, and may
/// contain invalid and ill-formed UTF-16 data. These strings are intended to be used with
/// FFI functions (such as Windows API) that directly use string length, where the strings are
/// known to have proper nul-termination already, or where strings are merely being passed through
/// without modification.
///
/// `WideCString` should be used instead if nul-aware strings are required.
///
/// `U16String` can be converted to and from many other string types, including `OsString` and
/// `String`, making proper Unicode Windows FFI safe and easy.
///
/// # Examples
///
/// The following example constructs a `U16String` and shows how to convert a `U16String` to a
/// regular Rust `String`.
///
/// ```rust
/// use widestring::ffi::U16String;
/// let v = vec![84u16, 104u16, 101u16]; // 'T' 'h' 'e'
/// // Create a wide string from the vector
/// let wstr = U16String::from_vec(v);
/// // Convert to a rust string!
/// let rust_str = wstr.to_string_lossy();
/// assert_eq!(rust_str, "The");
/// ```
#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct U16String {
    inner: Vec<u16>,
}

/// Wide string reference for `U16String`.
///
/// `U16Str` is aware of nul values. Strings may or may not be nul-terminated, and may
/// contain invalid and ill-formed UTF-16 data. These strings are intended to be used with
/// FFI functions (such as Windows API) that directly use string length, where the strings are
/// known to have proper nul-termination already, or where strings are merely being passed through
/// without modification.
///
/// `WideCStr` should be used instead of nul-aware strings are required.
///
/// `U16Str` can be converted to many other string types, including `OsString` and `String`, making
/// proper Unicode Windows FFI safe and easy.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct U16Str {
    inner: [u16],
}

impl U16String {
    /// Constructs a new empty `U16String`.
    pub fn new() -> U16String {
        U16String { inner: vec![] }
    }

    /// Constructs a `U16String` from a vector of possibly invalid or ill-formed UTF-16 data.
    ///
    /// No checks are made on the contents of the vector.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::ffi::U16String;
    /// let v = vec![84u16, 104u16, 101u16]; // 'T' 'h' 'e'
    /// # let cloned = v.clone();
    /// // Create a wide string from the vector
    /// let wstr = U16String::from_vec(v);
    /// # assert_eq!(wstr.into_vec(), cloned);
    /// ```
    pub fn from_vec<T: Into<Vec<u16>>>(raw: T) -> U16String {
        U16String { inner: raw.into() }
    }

    /// Encodes a `U16String` copy from an `OsStr`.
    ///
    /// This makes a wide string copy of the `OsStr`. Since `OsStr` makes no guarantees that it is
    /// valid data, there is no guarantee that the resulting `U16String` will be valid UTF-16.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::ffi::U16String;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wstr = U16String::from_str(s);
    ///
    /// assert_eq!(wstr.to_string().unwrap(), s);
    /// ```
    pub fn from_str<S: AsRef<OsStr> + ?Sized>(s: &S) -> U16String {
        U16String {
            inner: platform::os_to_wide(s.as_ref()),
        }
    }

    /// Constructs a `U16String` from a `u16` pointer and a length.
    ///
    /// The `len` argument is the number of `u16` elements, **not** the number of bytes.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements.
    ///
    /// # Panics
    ///
    /// Panics if `len` is greater than 0 but `p` is a null pointer.
    pub unsafe fn from_ptr(p: *const u16, len: usize) -> U16String {
        if len == 0 {
            return U16String::new();
        }
        assert!(!p.is_null());
        let slice = std::slice::from_raw_parts(p, len);
        U16String::from_vec(slice)
    }

    /// Creates a `U16String` with the given capacity.
    ///
    /// The string will be able to hold exactly `capacity` partial code units without reallocating.
    /// If `capacity` is set to 0, the string will not initially allocate.
    pub fn with_capacity(capacity: usize) -> U16String {
        U16String {
            inner: Vec::with_capacity(capacity),
        }
    }

    /// Returns the capacity this `U16String` can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Truncate the `U16String` to zero length.
    pub fn clear(&mut self) {
        self.inner.clear()
    }

    /// Reserves the capacity for at least `additional` more capacity to be inserted in the given
    /// `U16String`.
    ///
    /// More space may be reserved to avoid frequent allocations.
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional)
    }

    /// Reserves the minimum capacity for exactly `additional` more capacity to be inserted in the
    /// given `U16String`. Does nothing if the capcity is already sufficient.
    ///
    /// Note that the allocator may give more space than is requested. Therefore capacity can not be
    /// relied upon to be precisely minimal. Prefer `reserve` if future insertions are expected.
    pub fn reserve_exact(&mut self, additional: usize) {
        self.inner.reserve_exact(additional)
    }

    /// Converts to a `U16Str` reference.
    pub fn as_wide_str(&self) -> &U16Str {
        self
    }

    /// Converts the wide string into a `Vec<u16>`, consuming the string in the process.
    pub fn into_vec(self) -> Vec<u16> {
        self.inner
    }

    /// Extends the wide string with the given `&U16Str`.
    ///
    /// No checks are performed on the strings. It is possible to end up nul values inside the
    /// string, and it is up to the caller to determine if that is acceptable.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::ffi::U16String;
    /// let s = "MyString";
    /// let mut wstr = U16String::from_str(s);
    /// let cloned = wstr.clone();
    /// // Push the clone to the end, repeating the string twice.
    /// wstr.push(cloned);
    ///
    /// assert_eq!(wstr.to_string().unwrap(), "MyStringMyString");
    /// ```
    pub fn push<T: AsRef<U16Str>>(&mut self, s: T) {
        self.inner.extend_from_slice(&s.as_ref().inner)
    }

    /// Extends the wide string with the given `&[u16]` slice.
    ///
    /// No checks are performed on the strings. It is possible to end up nul values inside the
    /// string, and it is up to the caller to determine if that is acceptable.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::ffi::U16String;
    /// let s = "MyString";
    /// let mut wstr = U16String::from_str(s);
    /// let cloned = wstr.clone();
    /// // Push the clone to the end, repeating the string twice.
    /// wstr.push_slice(cloned);
    ///
    /// assert_eq!(wstr.to_string().unwrap(), "MyStringMyString");
    /// ```
    pub fn push_slice<T: AsRef<[u16]>>(&mut self, s: T) {
        self.inner.extend_from_slice(&s.as_ref())
    }

    /// Extends the string with the given `&OsStr`.
    ///
    /// No checks are performed on the strings. It is possible to end up nul values inside the
    /// string, and it is up to the caller to determine if that is acceptable.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::ffi::U16String;
    /// let s = "MyString";
    /// let mut wstr = U16String::from_str(s);
    /// // Push the original to the end, repeating the string twice.
    /// wstr.push_str(s);
    ///
    /// assert_eq!(wstr.to_string().unwrap(), "MyStringMyString");
    /// ```
    pub fn push_str<T: AsRef<OsStr>>(&mut self, s: T) {
        self.inner.extend(platform::os_to_wide(s.as_ref()))
    }

    /// Shrinks the capacity of the `U16String` to match its length.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::ffi::U16String;
    ///
    /// let mut s = U16String::from_str("foo");
    ///
    /// s.reserve(100);
    /// assert!(s.capacity() >= 100);
    ///
    /// s.shrink_to_fit();
    /// assert_eq!(3, s.capacity());
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit();
    }

    /// Converts this `U16String` into a boxed `U16Str`.
    ///
    /// # Examples
    ///
    /// ```
    /// use widestring::ffi::{U16String, U16Str};
    ///
    /// let s = U16String::from_str("hello");
    ///
    /// let b: Box<U16Str> = s.into_boxed_wide_str();
    /// ```
    pub fn into_boxed_wide_str(self) -> Box<U16Str> {
        let rw = Box::into_raw(self.inner.into_boxed_slice()) as *mut U16Str;
        unsafe { Box::from_raw(rw) }
    }
}

impl Into<Vec<u16>> for U16String {
    fn into(self) -> Vec<u16> {
        self.into_vec()
    }
}

impl<'a> From<U16String> for std::borrow::Cow<'a, U16Str> {
    fn from(s: U16String) -> std::borrow::Cow<'a, U16Str> {
        std::borrow::Cow::Owned(s)
    }
}

impl From<String> for U16String {
    fn from(s: String) -> U16String {
        U16String::from_str(&s)
    }
}

impl From<OsString> for U16String {
    fn from(s: OsString) -> U16String {
        U16String::from_str(&s)
    }
}

impl From<U16String> for OsString {
    fn from(s: U16String) -> OsString {
        s.to_os_string()
    }
}

impl<'a, T: ?Sized + AsRef<U16Str>> From<&'a T> for U16String {
    fn from(s: &'a T) -> U16String {
        s.as_ref().to_wide_string()
    }
}

impl std::ops::Index<std::ops::RangeFull> for U16String {
    type Output = U16Str;

    #[inline]
    fn index(&self, _index: std::ops::RangeFull) -> &U16Str {
        U16Str::from_slice(&self.inner)
    }
}

impl std::ops::Deref for U16String {
    type Target = U16Str;

    #[inline]
    fn deref(&self) -> &U16Str {
        &self[..]
    }
}

impl PartialEq<U16Str> for U16String {
    #[inline]
    fn eq(&self, other: &U16Str) -> bool {
        self.as_wide_str() == other
    }
}

impl PartialOrd<U16Str> for U16String {
    #[inline]
    fn partial_cmp(&self, other: &U16Str) -> Option<std::cmp::Ordering> {
        self.as_wide_str().partial_cmp(other)
    }
}

impl<'a> PartialEq<&'a U16Str> for U16String {
    #[inline]
    fn eq(&self, other: &&'a U16Str) -> bool {
        self.as_wide_str() == *other
    }
}

impl<'a> PartialOrd<&'a U16Str> for U16String {
    #[inline]
    fn partial_cmp(&self, other: &&'a U16Str) -> Option<std::cmp::Ordering> {
        self.as_wide_str().partial_cmp(*other)
    }
}

impl<'a> PartialEq<std::borrow::Cow<'a, U16Str>> for U16String {
    #[inline]
    fn eq(&self, other: &std::borrow::Cow<'a, U16Str>) -> bool {
        self.as_wide_str() == other.as_ref()
    }
}

impl<'a> PartialOrd<std::borrow::Cow<'a, U16Str>> for U16String {
    #[inline]
    fn partial_cmp(&self, other: &std::borrow::Cow<'a, U16Str>) -> Option<std::cmp::Ordering> {
        self.as_wide_str().partial_cmp(other.as_ref())
    }
}

impl U16Str {
    /// Coerces a value into a `U16Str`.
    pub fn new<'a, S: AsRef<U16Str> + ?Sized>(s: &'a S) -> &'a U16Str {
        s.as_ref()
    }

    /// Constructs a `U16Str` from a `u16` pointer and a length.
    ///
    /// The `len` argument is the number of `u16` elements, **not** the number of bytes.
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
    pub unsafe fn from_ptr<'a>(p: *const u16, len: usize) -> &'a U16Str {
        assert!(!p.is_null());
        mem::transmute(std::slice::from_raw_parts(p, len))
    }

    /// Constructs a `U16Str` from a slice of `u16` code points.
    ///
    /// No checks are performed on the slice.
    pub fn from_slice<'a>(slice: &'a [u16]) -> &'a U16Str {
        unsafe { mem::transmute(slice) }
    }

    /// Decodes a wide string to an owned `OsString`.
    ///
    /// This makes a string copy of the `U16Str`. Since `U16Str` makes no guarantees that it is
    /// valid UTF-16, there is no guarantee that the resulting `OsString` will be valid data.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::ffi::U16String;
    /// use std::ffi::OsString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wstr = U16String::from_str(s);
    /// // Create an OsString from the wide string
    /// let osstr = wstr.to_os_string();
    ///
    /// assert_eq!(osstr, OsString::from(s));
    /// ```
    pub fn to_os_string(&self) -> OsString {
        platform::os_from_wide(&self.inner)
    }

    /// Copies the wide string to a new owned `U16String`.
    pub fn to_wide_string(&self) -> U16String {
        U16String::from_vec(&self.inner)
    }

    /// Copies the wide string to a `String` if it contains valid UTF-16 data.
    ///
    /// # Failures
    ///
    /// Returns an error if the string contains any invalid UTF-16 data.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::ffi::U16String;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wstr = U16String::from_str(s);
    /// // Create a regular string from the wide string
    /// let s2 = wstr.to_string().unwrap();
    ///
    /// assert_eq!(s2, s);
    /// ```
    pub fn to_string(&self) -> Result<String, std::string::FromUtf16Error> {
        String::from_utf16(&self.inner)
    }

    /// Copies the wide string to a `String`.
    ///
    /// Any non-Unicode sequences are replaced with U+FFFD REPLACEMENT CHARACTER.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::ffi::U16String;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wstr = U16String::from_str(s);
    /// // Create a regular string from the wide string
    /// let lossy = wstr.to_string_lossy();
    ///
    /// assert_eq!(lossy, s);
    /// ```
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

    /// Returns the length of the wide string as number of UTF-16 code units (**not** code
    /// points and **not** number of bytes).
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns whether this wide string contains no data.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Converts a `Box<U16Str>` into a `U16String` without copying or allocating.
    pub fn into_wide_string(self: Box<U16Str>) -> U16String {
        let boxed = unsafe { Box::from_raw(Box::into_raw(self) as *mut [u16]) };
        U16String {
            inner: boxed.into_vec(),
        }
    }
}

impl std::borrow::Borrow<U16Str> for U16String {
    fn borrow(&self) -> &U16Str {
        &self[..]
    }
}

impl ToOwned for U16Str {
    type Owned = U16String;
    fn to_owned(&self) -> U16String {
        self.to_wide_string()
    }
}

impl<'a> From<&'a U16Str> for std::borrow::Cow<'a, U16Str> {
    fn from(s: &'a U16Str) -> std::borrow::Cow<'a, U16Str> {
        std::borrow::Cow::Borrowed(s)
    }
}

impl AsRef<U16Str> for U16Str {
    fn as_ref(&self) -> &U16Str {
        self
    }
}

impl AsRef<U16Str> for U16String {
    fn as_ref(&self) -> &U16Str {
        self
    }
}

impl AsRef<[u16]> for U16Str {
    fn as_ref(&self) -> &[u16] {
        self.as_slice()
    }
}

impl AsRef<[u16]> for U16String {
    fn as_ref(&self) -> &[u16] {
        self.as_slice()
    }
}

impl<'a> From<&'a U16Str> for Box<U16Str> {
    fn from(s: &'a U16Str) -> Box<U16Str> {
        let boxed: Box<[u16]> = Box::from(&s.inner);
        let rw = Box::into_raw(boxed) as *mut U16Str;
        unsafe { Box::from_raw(rw) }
    }
}

impl From<Box<U16Str>> for U16String {
    fn from(boxed: Box<U16Str>) -> U16String {
        boxed.into_wide_string()
    }
}

impl From<U16String> for Box<U16Str> {
    fn from(s: U16String) -> Box<U16Str> {
        s.into_boxed_wide_str()
    }
}

impl Default for Box<U16Str> {
    fn default() -> Box<U16Str> {
        let boxed: Box<[u16]> = Box::from([]);
        let rw = Box::into_raw(boxed) as *mut U16Str;
        unsafe { Box::from_raw(rw) }
    }
}
