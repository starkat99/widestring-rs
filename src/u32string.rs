use std;
use std::char;
use std::ffi::{OsStr, OsString};
use std::mem;

/// An owned, mutable 32-bit wide string for FFI that is **not** nul-aware.
///
/// `U32String` is not aware of nul values. Strings may or may not be nul-terminated, and may
/// contain invalid and ill-formed UTF-32 data. These strings are intended to be used with
/// FFI functions that directly use string length, where the strings are known to have proper
/// nul-termination already, or where strings are merely being passed through without modification.
///
/// `U32CString` should be used instead if nul-aware 32-bit strings are required.
///
/// `U32String` can be converted to and from many other standard Rust string types, including
/// `OsString` and `String`, making proper Unicode FFI safe and easy.
///
/// # Examples
///
/// The following example constructs a `U32String` and shows how to convert a `U32String` to a
/// regular Rust `String`.
///
/// ```rust
/// use widestring::U32String;
/// let s = "Test";
/// // Create a wide string from the rust string
/// let wstr = U32String::from_str(s);
/// // Convert back to a rust string
/// let rust_str = wstr.to_string_lossy();
/// assert_eq!(rust_str, "Test");
/// ```
#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct U32String {
    inner: Vec<u32>,
}

/// String slice reference for `U32String`.
///
/// `U32Str` is to `U32String` as `str` is to `String`.
///
/// `U32Str` is not aware of nul values. Strings may or may not be nul-terminated, and may
/// contain invalid and ill-formed UTF-32 data. These strings are intended to be used with
/// FFI functions that directly use string length, where the strings are known to have proper
/// nul-termination already, or where strings are merely being passed through without modification.
///
/// `WideCStr` should be used instead of nul-aware strings are required.
///
/// `U32Str` can be converted to many other string types, including `OsString` and `String`, making
/// proper Unicode FFI safe and easy.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct U32Str {
    inner: [u32],
}

/// A possible error value when converting a String from a UTF-32 byte slice.
///
/// This type is the error type for the `to_string` method on `U32Str`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FromUtf32Error();

impl U32String {
    /// Constructs a new empty `U32String`.
    pub fn new() -> U32String {
        U32String { inner: vec![] }
    }

    /// Constructs a `U32String` from a vector of possibly invalid or ill-formed UTF-32 data.
    ///
    /// No checks are made on the contents of the vector.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32String;
    /// let v = vec![84u32, 104u32, 101u32]; // 'T' 'h' 'e'
    /// # let cloned = v.clone();
    /// // Create a wide string from the vector
    /// let wstr = U32String::from_vec(v);
    /// # assert_eq!(wstr.into_vec(), cloned);
    /// ```
    pub fn from_vec(raw: impl Into<Vec<u32>>) -> U32String {
        U32String { inner: raw.into() }
    }

    /// Constructs a `U32String` from a vector of UTF-32 data.
    ///
    /// No checks are made on the contents of the vector.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32String;
    /// let v: Vec<char> = "Test".chars().collect();
    /// # let cloned: Vec<u32> = v.iter().map(|&c| c as u32).collect();
    /// // Create a wide string from the vector
    /// let wstr = U32String::from_chars(v);
    /// # assert_eq!(wstr.into_vec(), cloned);
    /// ```
    pub fn from_chars(raw: impl Into<Vec<char>>) -> U32String {
        U32String {
            inner: unsafe { mem::transmute(raw.into()) },
        }
    }

    /// Encodes a `U32String` copy from a `str`.
    ///
    /// This makes a wide string copy of the `str`. Since `str` will always be valid UTF-8, the
    /// resulting `U32String` will also be valid UTF-32.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32String;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wstr = U32String::from_str(s);
    ///
    /// assert_eq!(wstr.to_string().unwrap(), s);
    /// ```
    pub fn from_str<S: AsRef<str> + ?Sized>(s: &S) -> U32String {
        let v: Vec<char> = s.as_ref().chars().collect();
        U32String::from_chars(v)
    }

    /// Encodes a `U32String` copy from an `OsStr`.
    ///
    /// This makes a wide string copy of the `OsStr`. Since `OsStr` makes no guarantees that it is
    /// valid data, there is no guarantee that the resulting `U32String` will be valid UTF-32.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32String;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wstr = U32String::from_os_str(s);
    ///
    /// assert_eq!(wstr.to_string().unwrap(), s);
    /// ```
    pub fn from_os_str<S: AsRef<OsStr> + ?Sized>(s: &S) -> U32String {
        let v: Vec<char> = s.as_ref().to_string_lossy().chars().collect();
        U32String::from_chars(v)
    }

    /// Constructs a `U32String` from a `u32` pointer and a length.
    ///
    /// The `len` argument is the number of `u32` elements, **not** the number of bytes.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements.
    ///
    /// # Panics
    ///
    /// Panics if `len` is greater than 0 but `p` is a null pointer.
    pub unsafe fn from_ptr(p: *const u32, len: usize) -> U32String {
        if len == 0 {
            return U32String::new();
        }
        assert!(!p.is_null());
        let slice = std::slice::from_raw_parts(p, len);
        U32String::from_vec(slice)
    }

    /// Constructs a `U32String` from a `char` pointer and a length.
    ///
    /// The `len` argument is the number of `char` elements, **not** the number of bytes.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements.
    ///
    /// # Panics
    ///
    /// Panics if `len` is greater than 0 but `p` is a null pointer.
    pub unsafe fn from_char_ptr(p: *const char, len: usize) -> U32String {
        if len == 0 {
            return U32String::new();
        }
        assert!(!p.is_null());
        let slice = std::slice::from_raw_parts(p, len);
        U32String::from_chars(slice)
    }

    /// Creates a `U32String` with the given capacity.
    ///
    /// The string will be able to hold exactly `capacity` partial code units without reallocating.
    /// If `capacity` is set to 0, the string will not initially allocate.
    pub fn with_capacity(capacity: usize) -> U32String {
        U32String {
            inner: Vec::with_capacity(capacity),
        }
    }

    /// Returns the capacity this `U32String` can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Truncate the `U32String` to zero length.
    pub fn clear(&mut self) {
        self.inner.clear()
    }

    /// Reserves the capacity for at least `additional` more capacity to be inserted in the given
    /// `U32String`.
    ///
    /// More space may be reserved to avoid frequent allocations.
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional)
    }

    /// Reserves the minimum capacity for exactly `additional` more capacity to be inserted in the
    /// given `U32String`. Does nothing if the capcity is already sufficient.
    ///
    /// Note that the allocator may give more space than is requested. Therefore capacity can not be
    /// relied upon to be precisely minimal. Prefer `reserve` if future insertions are expected.
    pub fn reserve_exact(&mut self, additional: usize) {
        self.inner.reserve_exact(additional)
    }

    /// Converts to a `U32Str` reference.
    pub fn as_u32_str(&self) -> &U32Str {
        self
    }

    /// Converts the wide string into a `Vec<u32>`, consuming the string in the process.
    pub fn into_vec(self) -> Vec<u32> {
        self.inner
    }

    /// Extends the wide string with the given `&U32Str`.
    ///
    /// No checks are performed on the strings. It is possible to end up nul values inside the
    /// string, and it is up to the caller to determine if that is acceptable.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32String;
    /// let s = "MyString";
    /// let mut wstr = U32String::from_str(s);
    /// let cloned = wstr.clone();
    /// // Push the clone to the end, repeating the string twice.
    /// wstr.push(cloned);
    ///
    /// assert_eq!(wstr.to_string().unwrap(), "MyStringMyString");
    /// ```
    pub fn push(&mut self, s: impl AsRef<U32Str>) {
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
    /// use widestring::U32String;
    /// let s = "MyString";
    /// let mut wstr = U32String::from_str(s);
    /// let cloned = wstr.clone();
    /// // Push the clone to the end, repeating the string twice.
    /// wstr.push_slice(cloned);
    ///
    /// assert_eq!(wstr.to_string().unwrap(), "MyStringMyString");
    /// ```
    pub fn push_slice(&mut self, s: impl AsRef<[u32]>) {
        self.inner.extend_from_slice(&s.as_ref())
    }

    /// Extends the string with the given `&str`.
    ///
    /// No checks are performed on the strings. It is possible to end up nul values inside the
    /// string, and it is up to the caller to determine if that is acceptable.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32String;
    /// let s = "MyString";
    /// let mut wstr = U32String::from_str(s);
    /// // Push the original to the end, repeating the string twice.
    /// wstr.push_str(s);
    ///
    /// assert_eq!(wstr.to_string().unwrap(), "MyStringMyString");
    /// ```
    pub fn push_str(&mut self, s: impl AsRef<str>) {
        self.inner.extend(s.as_ref().chars().map(|c| c as u32))
    }

    /// Extends the string with the given `&OsStr`.
    ///
    /// No checks are performed on the strings. It is possible to end up nul values inside the
    /// string, and it is up to the caller to determine if that is acceptable.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32String;
    /// let s = "MyString";
    /// let mut wstr = U32String::from_str(s);
    /// // Push the original to the end, repeating the string twice.
    /// wstr.push_os_str(s);
    ///
    /// assert_eq!(wstr.to_string().unwrap(), "MyStringMyString");
    /// ```
    pub fn push_os_str(&mut self, s: impl AsRef<OsStr>) {
        self.inner
            .extend(s.as_ref().to_string_lossy().chars().map(|c| c as u32))
    }

    /// Shrinks the capacity of the `U32String` to match its length.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32String;
    ///
    /// let mut s = U32String::from_str("foo");
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

    /// Converts this `U32String` into a boxed `U32Str`.
    ///
    /// # Examples
    ///
    /// ```
    /// use widestring::{U32String, U32Str};
    ///
    /// let s = U32String::from_str("hello");
    ///
    /// let b: Box<U32Str> = s.into_boxed_u32_str();
    /// ```
    pub fn into_boxed_u32_str(self) -> Box<U32Str> {
        let rw = Box::into_raw(self.inner.into_boxed_slice()) as *mut U32Str;
        unsafe { Box::from_raw(rw) }
    }
}

impl Into<Vec<u32>> for U32String {
    fn into(self) -> Vec<u32> {
        self.into_vec()
    }
}

impl<'a> From<U32String> for std::borrow::Cow<'a, U32Str> {
    fn from(s: U32String) -> std::borrow::Cow<'a, U32Str> {
        std::borrow::Cow::Owned(s)
    }
}

impl Into<U32String> for Vec<u32> {
    fn into(self) -> U32String {
        U32String::from_vec(self)
    }
}

impl Into<U32String> for Vec<char> {
    fn into(self) -> U32String {
        U32String::from_chars(self)
    }
}

impl From<String> for U32String {
    fn from(s: String) -> U32String {
        U32String::from_str(&s)
    }
}

impl From<OsString> for U32String {
    fn from(s: OsString) -> U32String {
        U32String::from_os_str(&s)
    }
}

impl From<U32String> for OsString {
    fn from(s: U32String) -> OsString {
        s.to_os_string()
    }
}

impl<'a, T: ?Sized + AsRef<U32Str>> From<&'a T> for U32String {
    fn from(s: &'a T) -> U32String {
        s.as_ref().to_u32_string()
    }
}

impl std::ops::Index<std::ops::RangeFull> for U32String {
    type Output = U32Str;

    #[inline]
    fn index(&self, _index: std::ops::RangeFull) -> &U32Str {
        U32Str::from_slice(&self.inner)
    }
}

impl std::ops::Deref for U32String {
    type Target = U32Str;

    #[inline]
    fn deref(&self) -> &U32Str {
        &self[..]
    }
}

impl PartialEq<U32Str> for U32String {
    #[inline]
    fn eq(&self, other: &U32Str) -> bool {
        self.as_u32_str() == other
    }
}

impl PartialOrd<U32Str> for U32String {
    #[inline]
    fn partial_cmp(&self, other: &U32Str) -> Option<std::cmp::Ordering> {
        self.as_u32_str().partial_cmp(other)
    }
}

impl<'a> PartialEq<&'a U32Str> for U32String {
    #[inline]
    fn eq(&self, other: &&'a U32Str) -> bool {
        self.as_u32_str() == *other
    }
}

impl<'a> PartialOrd<&'a U32Str> for U32String {
    #[inline]
    fn partial_cmp(&self, other: &&'a U32Str) -> Option<std::cmp::Ordering> {
        self.as_u32_str().partial_cmp(*other)
    }
}

impl<'a> PartialEq<std::borrow::Cow<'a, U32Str>> for U32String {
    #[inline]
    fn eq(&self, other: &std::borrow::Cow<'a, U32Str>) -> bool {
        self.as_u32_str() == other.as_ref()
    }
}

impl<'a> PartialOrd<std::borrow::Cow<'a, U32Str>> for U32String {
    #[inline]
    fn partial_cmp(&self, other: &std::borrow::Cow<'a, U32Str>) -> Option<std::cmp::Ordering> {
        self.as_u32_str().partial_cmp(other.as_ref())
    }
}

impl U32Str {
    /// Coerces a value into a `U32Str`.
    pub fn new<S: AsRef<U32Str> + ?Sized>(s: &S) -> &U32Str {
        s.as_ref()
    }

    /// Constructs a `U32Str` from a `u32` pointer and a length.
    ///
    /// The `len` argument is the number of `u32` elements, **not** the number of bytes.
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
    pub unsafe fn from_ptr<'a>(p: *const u32, len: usize) -> &'a U32Str {
        assert!(!p.is_null());
        mem::transmute(std::slice::from_raw_parts(p, len))
    }

    /// Constructs a `U32Str` from a `char` pointer and a length.
    ///
    /// The `len` argument is the number of `char` elements, **not** the number of bytes.
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
    pub unsafe fn from_char_ptr<'a>(p: *const char, len: usize) -> &'a U32Str {
        assert!(!p.is_null());
        mem::transmute(std::slice::from_raw_parts(p, len))
    }

    /// Constructs a `U32Str` from a slice of `u32` code points.
    ///
    /// No checks are performed on the slice.
    pub fn from_slice(slice: &[u32]) -> &U32Str {
        unsafe { mem::transmute(slice) }
    }

    /// Constructs a `U32Str` from a slice of `u32` code points.
    ///
    /// No checks are performed on the slice.
    pub fn from_char_slice(slice: &[u32]) -> &U32Str {
        unsafe { mem::transmute(slice) }
    }

    /// Decodes a wide string to an owned `OsString`.
    ///
    /// This makes a string copy of the `U32Str`. Since `U32Str` makes no guarantees that it is
    /// valid UTF-32, there is no guarantee that the resulting `OsString` will be valid data.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32String;
    /// use std::ffi::OsString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wstr = U32String::from_str(s);
    /// // Create an OsString from the wide string
    /// let osstr = wstr.to_os_string();
    ///
    /// assert_eq!(osstr, OsString::from(s));
    /// ```
    pub fn to_os_string(&self) -> OsString {
        self.to_string_lossy().into()
    }

    /// Copies the wide string to a new owned `U32String`.
    pub fn to_u32_string(&self) -> U32String {
        U32String::from_vec(&self.inner)
    }

    /// Copies the wide string to a `String` if it contains valid UTF-32 data.
    ///
    /// # Failures
    ///
    /// Returns an error if the string contains any invalid UTF-32 data.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32String;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wstr = U32String::from_str(s);
    /// // Create a regular string from the wide string
    /// let s2 = wstr.to_string().unwrap();
    ///
    /// assert_eq!(s2, s);
    /// ```
    pub fn to_string(&self) -> Result<String, FromUtf32Error> {
        let chars: Vec<Option<char>> = self.inner.iter().map(|c| char::from_u32(*c)).collect();
        if chars.iter().any(|c| c.is_none()) {
            return Err(FromUtf32Error());
        }
        let size = chars.iter().filter_map(|o| o.map(|c| c.len_utf8())).sum();
        let mut vec = Vec::with_capacity(size);
        unsafe { vec.set_len(size) };
        let mut i = 0;
        for c in chars.iter().filter_map(|&o| o) {
            c.encode_utf8(&mut vec[i..]);
            i += c.len_utf8();
        }
        Ok(unsafe { String::from_utf8_unchecked(vec) })
    }

    /// Copies the wide string to a `String`.
    ///
    /// Any non-Unicode sequences are replaced with U+FFFD REPLACEMENT CHARACTER.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32String;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wstr = U32String::from_str(s);
    /// // Create a regular string from the wide string
    /// let lossy = wstr.to_string_lossy();
    ///
    /// assert_eq!(lossy, s);
    /// ```
    pub fn to_string_lossy(&self) -> String {
        let chars: Vec<char> = self.inner
            .iter()
            .map(|&c| char::from_u32(c).unwrap_or(char::REPLACEMENT_CHARACTER))
            .collect();
        let size = chars.iter().map(|c| c.len_utf8()).sum();
        let mut vec = Vec::with_capacity(size);
        unsafe { vec.set_len(size) };
        let mut i = 0;
        for c in chars {
            c.encode_utf8(&mut vec[i..]);
            i += c.len_utf8();
        }
        unsafe { String::from_utf8_unchecked(vec) }
    }

    /// Converts to a slice of the wide string.
    pub fn as_slice(&self) -> &[u32] {
        &self.inner
    }

    /// Returns a raw pointer to the wide string.
    ///
    /// The pointer is valid only as long as the lifetime of this reference.
    pub fn as_ptr(&self) -> *const u32 {
        self.inner.as_ptr()
    }

    /// Returns the length of the wide string as number of UTF-32 code units (**not** code
    /// points and **not** number of bytes).
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns whether this wide string contains no data.
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Converts a `Box<U32Str>` into a `U32String` without copying or allocating.
    pub fn into_u32_string(self: Box<U32Str>) -> U32String {
        let boxed = unsafe { Box::from_raw(Box::into_raw(self) as *mut [u32]) };
        U32String {
            inner: boxed.into_vec(),
        }
    }
}

impl std::borrow::Borrow<U32Str> for U32String {
    fn borrow(&self) -> &U32Str {
        &self[..]
    }
}

impl ToOwned for U32Str {
    type Owned = U32String;
    fn to_owned(&self) -> U32String {
        self.to_u32_string()
    }
}

impl<'a> From<&'a U32Str> for std::borrow::Cow<'a, U32Str> {
    fn from(s: &'a U32Str) -> std::borrow::Cow<'a, U32Str> {
        std::borrow::Cow::Borrowed(s)
    }
}

impl AsRef<U32Str> for U32Str {
    fn as_ref(&self) -> &U32Str {
        self
    }
}

impl AsRef<U32Str> for U32String {
    fn as_ref(&self) -> &U32Str {
        self
    }
}

impl AsRef<[u32]> for U32Str {
    fn as_ref(&self) -> &[u32] {
        self.as_slice()
    }
}

impl AsRef<[u32]> for U32String {
    fn as_ref(&self) -> &[u32] {
        self.as_slice()
    }
}

impl<'a> From<&'a U32Str> for Box<U32Str> {
    fn from(s: &'a U32Str) -> Box<U32Str> {
        let boxed: Box<[u32]> = Box::from(&s.inner);
        let rw = Box::into_raw(boxed) as *mut U32Str;
        unsafe { Box::from_raw(rw) }
    }
}

impl From<Box<U32Str>> for U32String {
    fn from(boxed: Box<U32Str>) -> U32String {
        boxed.into_u32_string()
    }
}

impl From<U32String> for Box<U32Str> {
    fn from(s: U32String) -> Box<U32Str> {
        s.into_boxed_u32_str()
    }
}

impl Default for Box<U32Str> {
    fn default() -> Box<U32Str> {
        let boxed: Box<[u16]> = Box::from([]);
        let rw = Box::into_raw(boxed) as *mut U32Str;
        unsafe { Box::from_raw(rw) }
    }
}

impl std::fmt::Display for FromUtf32Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "error converting from UTF-32 to UTF-8")
    }
}

impl std::error::Error for FromUtf32Error {
    fn description(&self) -> &str {
        "error converting from UTF-32 to UTF-8"
    }
}
