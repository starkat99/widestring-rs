//! Owned, growable wide strings
//!
//! This module contains the [`UString`] strings and related types.

use crate::{UChar, UStr, WideChar};
use alloc::{
    borrow::{Cow, ToOwned},
    boxed::Box,
    string::String,
    vec::Vec,
};
use core::{
    borrow::Borrow,
    char, cmp, mem,
    ops::{Deref, Index, RangeFull},
    slice,
};

/// An owned, mutable "wide" string for FFI that is **not** null-aware
///
/// [`UString`] is not aware of null values. Strings may or may not be null-terminated, and may
/// contain invalid and ill-formed UTF-16 or UTF-32 data. These strings are intended to be used
/// with FFI functions that directly use string length, where the strings are known to have proper
/// null-termination already, or where strings are merely being passed through without modification.
///
/// [`UCString`][crate::UCString] should be used instead if null-aware strings are required.
///
/// [`UString`] can be converted to and from many other standard Rust string types, including
/// [`OsString`][std::ffi::OsString] and [`String`], making proper Unicode FFI safe and easy.
///
/// Please prefer using the type aliases [`U16String`], [`U32String`], or [`WideString`] to using
/// this type directly.
///
/// # Examples
///
/// The following example constructs a [`U16String`] and shows how to convert a [`U16String`] to a
/// regular Rust [`String`].
///
/// ```rust
/// use widestring::U16String;
/// let s = "Test";
/// // Create a wide string from the rust string
/// let wstr = U16String::from_str(s);
/// // Convert back to a rust string
/// let rust_str = wstr.to_string_lossy();
/// assert_eq!(rust_str, "Test");
/// ```
///
/// The same example using [`U32String`] instead:
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
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
#[derive(Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UString<C: UChar> {
    pub(crate) inner: Vec<C>,
}

impl<C: UChar> UString<C> {
    /// Constructs a new empty [`UString`]
    #[inline]
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

    /// Constructs a [`UString`] from a vector
    ///
    /// No checks are made on the contents of the vector. It may or may not be valid character data.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U16String;
    /// let v = vec![84u16, 104u16, 101u16]; // 'T' 'h' 'e'
    /// # let cloned = v.clone();
    /// // Create a wide string from the vector
    /// let wstr = U16String::from_vec(v);
    /// # assert_eq!(wstr.into_vec(), cloned);
    /// ```
    ///
    /// ```rust
    /// use widestring::U32String;
    /// let v = vec![84u32, 104u32, 101u32]; // 'T' 'h' 'e'
    /// # let cloned = v.clone();
    /// // Create a wide string from the vector
    /// let wstr = U32String::from_vec(v);
    /// # assert_eq!(wstr.into_vec(), cloned);
    /// ```
    #[inline]
    pub fn from_vec(raw: impl Into<Vec<C>>) -> Self {
        Self { inner: raw.into() }
    }

    /// Constructs a [`UString`] copy from a pointer and a length
    ///
    /// The `len` argument is the number of elements, **not** the number of bytes.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements.
    ///
    /// In addition, the data must meet the safety conditions of [std::slice::from_raw_parts].
    ///
    /// # Panics
    ///
    /// Panics if `len` is greater than 0 but `p` is a null pointer.
    pub unsafe fn from_ptr(p: *const C, len: usize) -> Self {
        if len == 0 {
            return Self::new();
        }
        assert!(!p.is_null());
        let slice = slice::from_raw_parts(p, len);
        Self::from_vec(slice)
    }

    /// Constructs a [`UString`] with the given capacity
    ///
    /// The string will be able to hold exactly `capacity` elements without reallocating.
    /// If `capacity` is set to 0, the string will not initially allocate.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            inner: Vec::with_capacity(capacity),
        }
    }

    /// Returns the capacity this [`UString`] can hold without reallocating
    #[inline]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Truncates the [`UString`] to zero length
    #[inline]
    pub fn clear(&mut self) {
        self.inner.clear()
    }

    /// Reserves the capacity for at least `additional` more capacity to be inserted in the given
    /// [`UString`]
    ///
    /// More space may be reserved to avoid frequent allocations.
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional)
    }

    /// Reserves the minimum capacity for exactly `additional` more capacity to be inserted in the
    /// given [`UString`]. Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give more space than is requested. Therefore capacity can not
    /// be relied upon to be precisely minimal. Prefer [`reserve`][Self::reserve] if future
    /// insertions are expected.
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.inner.reserve_exact(additional)
    }

    /// Converts the string into a [`Vec`], consuming the string in the process
    #[inline]
    pub fn into_vec(self) -> Vec<C> {
        self.inner
    }

    /// Converts to a [`UStr`] reference
    #[inline]
    pub fn as_ustr(&self) -> &UStr<C> {
        self
    }

    /// Extends the string with the given string slice
    ///
    /// No checks are performed on the strings. It is possible to end up null values inside the
    /// string, and it is up to the caller to determine if that is acceptable.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U16String;
    /// let s = "MyString";
    /// let mut wstr = U16String::from_str(s);
    /// let cloned = wstr.clone();
    /// // Push the clone to the end, repeating the string twice.
    /// wstr.push(cloned);
    ///
    /// assert_eq!(wstr.to_string().unwrap(), "MyStringMyString");
    /// ```
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
    #[inline]
    pub fn push(&mut self, s: impl AsRef<UStr<C>>) {
        self.inner.extend_from_slice(&s.as_ref().inner)
    }

    /// Extends the string with the given slice
    ///
    /// No checks are performed on the strings. It is possible to end up null values inside the
    /// string, and it is up to the caller to determine if that is acceptable.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U16String;
    /// let s = "MyString";
    /// let mut wstr = U16String::from_str(s);
    /// let cloned = wstr.clone();
    /// // Push the clone to the end, repeating the string twice.
    /// wstr.push_slice(cloned);
    ///
    /// assert_eq!(wstr.to_string().unwrap(), "MyStringMyString");
    /// ```
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
    #[inline]
    pub fn push_slice(&mut self, s: impl AsRef<[C]>) {
        self.inner.extend_from_slice(s.as_ref())
    }

    /// Shrinks the capacity of the [`UString`] to match its length
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U16String;
    ///
    /// let mut s = U16String::from_str("foo");
    ///
    /// s.reserve(100);
    /// assert!(s.capacity() >= 100);
    ///
    /// s.shrink_to_fit();
    /// assert_eq!(3, s.capacity());
    /// ```
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
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.inner.shrink_to_fit();
    }

    /// Converts this [`UString`] into a boxed [`UStr`]
    ///
    /// # Examples
    ///
    /// ```
    /// use widestring::{U16String, U16Str};
    ///
    /// let s = U16String::from_str("hello");
    ///
    /// let b: Box<U16Str> = s.into_boxed_ustr();
    /// ```
    ///
    /// ```
    /// use widestring::{U32String, U32Str};
    ///
    /// let s = U32String::from_str("hello");
    ///
    /// let b: Box<U32Str> = s.into_boxed_ustr();
    /// ```
    pub fn into_boxed_ustr(self) -> Box<UStr<C>> {
        let rw = Box::into_raw(self.inner.into_boxed_slice()) as *mut UStr<C>;
        unsafe { Box::from_raw(rw) }
    }
}

impl UString<u16> {
    /// Encodes a [`U16String`] copy from a [`str`]
    ///
    /// This makes a string copy of the [`str`]. Since [`str`] will always be valid UTF-8, the
    /// resulting [`U16String`] will also be valid UTF-16.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U16String;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wstr = U16String::from_str(s);
    ///
    /// assert_eq!(wstr.to_string().unwrap(), s);
    /// ```
    #[allow(clippy::should_implement_trait)]
    #[inline]
    pub fn from_str<S: AsRef<str> + ?Sized>(s: &S) -> Self {
        Self {
            inner: s.as_ref().encode_utf16().collect(),
        }
    }

    /// Encodes a [`U16String`] copy from an [`OsStr`][std::ffi::OsStr]
    ///
    /// This makes a string copy of the [`OsStr`][std::ffi::OsStr]. Since [`OsStr`][std::ffi::OsStr]
    /// makes no  guarantees that it is valid data, there is no guarantee that the resulting
    /// [`U16String`] will be valid UTF-16.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U16String;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wstr = U16String::from_os_str(s);
    ///
    /// assert_eq!(wstr.to_string().unwrap(), s);
    /// ```
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    #[inline]
    pub fn from_os_str<S: AsRef<std::ffi::OsStr> + ?Sized>(s: &S) -> Self {
        Self {
            inner: crate::platform::os_to_wide(s.as_ref()),
        }
    }

    /// Extends the string with the given string slice
    ///
    /// No checks are performed on the strings. It is possible to end up null values inside the
    /// string, and it is up to the caller to determine if that is acceptable.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U16String;
    /// let s = "MyString";
    /// let mut wstr = U16String::from_str(s);
    /// // Push the original to the end, repeating the string twice.
    /// wstr.push_str(s);
    ///
    /// assert_eq!(wstr.to_string().unwrap(), "MyStringMyString");
    /// ```
    #[inline]
    pub fn push_str(&mut self, s: impl AsRef<str>) {
        self.inner.extend(s.as_ref().encode_utf16())
    }

    /// Extends the string with the given string slice
    ///
    /// No checks are performed on the strings. It is possible to end up null values inside the
    /// string, and it is up to the caller to determine if that is acceptable.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U16String;
    /// let s = "MyString";
    /// let mut wstr = U16String::from_str(s);
    /// // Push the original to the end, repeating the string twice.
    /// wstr.push_os_str(s);
    ///
    /// assert_eq!(wstr.to_string().unwrap(), "MyStringMyString");
    /// ```
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    #[inline]
    pub fn push_os_str(&mut self, s: impl AsRef<std::ffi::OsStr>) {
        self.inner.extend(crate::platform::os_to_wide(s.as_ref()))
    }
}

impl UString<u32> {
    /// Constructs a [`U32String`] from a [`char`][prim@char] vector
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
    pub fn from_chars(raw: impl Into<Vec<char>>) -> Self {
        let mut chars = raw.into();
        Self {
            inner: unsafe {
                let ptr = chars.as_mut_ptr() as *mut u32;
                let len = chars.len();
                let cap = chars.capacity();
                mem::forget(chars);
                Vec::from_raw_parts(ptr, len, cap)
            },
        }
    }

    /// Encodes a [`U32String`] copy from a [`str`]
    ///
    /// This makes a string copy of the [`str`]. Since [`str`] will always be valid UTF-8, the
    /// resulting [`U32String`] will also be valid UTF-32.
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
    #[allow(clippy::should_implement_trait)]
    #[inline]
    pub fn from_str<S: AsRef<str> + ?Sized>(s: &S) -> Self {
        let v: Vec<char> = s.as_ref().chars().collect();
        Self::from_chars(v)
    }

    /// Encodes a [`U32String`] copy from an [`OsStr`][std::ffi::OsStr]
    ///
    /// This makes a string copy of the [`OsStr`][std::ffi::OsStr]. Since [`OsStr`][std::ffi::OsStr]
    /// makes no guarantees that it is valid data, there is no guarantee that the resulting
    /// [`U32String`] will be valid UTF-32.
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
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    pub fn from_os_str<S: AsRef<std::ffi::OsStr> + ?Sized>(s: &S) -> Self {
        let v: Vec<char> = s.as_ref().to_string_lossy().chars().collect();
        Self::from_chars(v)
    }

    /// Constructs a [`U32String`] from a [`char`][prim@char] pointer and a length
    ///
    /// The `len` argument is the number of `char` elements, **not** the number of bytes.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements.
    ///
    /// In addition, the data must meet the safety conditions of [std::slice::from_raw_parts].
    ///
    /// # Panics
    ///
    /// Panics if `len` is greater than 0 but `p` is a null pointer.
    #[inline]
    pub unsafe fn from_char_ptr(p: *const char, len: usize) -> Self {
        Self::from_ptr(p as *const u32, len)
    }

    /// Extends the string with the given string slice
    ///
    /// No checks are performed on the strings. It is possible to end up null values inside the
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
    #[inline]
    pub fn push_str(&mut self, s: impl AsRef<str>) {
        self.inner.extend(s.as_ref().chars().map(|c| c as u32))
    }

    /// Extends the string with the given string slice
    ///
    /// No checks are performed on the strings. It is possible to end up null values inside the
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
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    #[inline]
    pub fn push_os_str(&mut self, s: impl AsRef<std::ffi::OsStr>) {
        self.inner
            .extend(s.as_ref().to_string_lossy().chars().map(|c| c as u32))
    }
}

impl core::fmt::Debug for U16String {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        crate::debug_fmt_u16(self.as_slice(), f)
    }
}

impl core::fmt::Debug for U32String {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        crate::debug_fmt_u32(self.as_slice(), f)
    }
}

impl<C: UChar> From<UString<C>> for Vec<C> {
    #[inline]
    fn from(value: UString<C>) -> Self {
        value.into_vec()
    }
}

impl<'a> From<UString<u16>> for Cow<'a, UStr<u16>> {
    #[inline]
    fn from(s: UString<u16>) -> Self {
        Cow::Owned(s)
    }
}

impl<'a> From<UString<u32>> for Cow<'a, UStr<u32>> {
    #[inline]
    fn from(s: UString<u32>) -> Self {
        Cow::Owned(s)
    }
}

impl From<Vec<u16>> for UString<u16> {
    #[inline]
    fn from(value: Vec<u16>) -> Self {
        Self::from_vec(value)
    }
}

impl From<Vec<u32>> for UString<u32> {
    #[inline]
    fn from(value: Vec<u32>) -> Self {
        Self::from_vec(value)
    }
}

impl From<Vec<char>> for UString<u32> {
    #[inline]
    fn from(value: Vec<char>) -> Self {
        Self::from_chars(value)
    }
}

impl From<String> for UString<u16> {
    #[inline]
    fn from(s: String) -> Self {
        Self::from_str(&s)
    }
}

impl From<String> for UString<u32> {
    #[inline]
    fn from(s: String) -> Self {
        Self::from_str(&s)
    }
}

#[cfg(feature = "std")]
impl From<std::ffi::OsString> for UString<u16> {
    #[inline]
    fn from(s: std::ffi::OsString) -> Self {
        Self::from_os_str(&s)
    }
}

#[cfg(feature = "std")]
impl From<std::ffi::OsString> for UString<u32> {
    #[inline]
    fn from(s: std::ffi::OsString) -> Self {
        Self::from_os_str(&s)
    }
}

#[cfg(feature = "std")]
impl From<UString<u16>> for std::ffi::OsString {
    #[inline]
    fn from(s: UString<u16>) -> Self {
        s.to_os_string()
    }
}

#[cfg(feature = "std")]
impl From<UString<u32>> for std::ffi::OsString {
    #[inline]
    fn from(s: UString<u32>) -> Self {
        s.to_os_string()
    }
}

impl<'a, C: UChar, T: ?Sized + AsRef<UStr<C>>> From<&'a T> for UString<C> {
    #[inline]
    fn from(s: &'a T) -> Self {
        s.as_ref().to_ustring()
    }
}

impl<C: UChar> Index<RangeFull> for UString<C> {
    type Output = UStr<C>;

    #[inline]
    fn index(&self, _index: RangeFull) -> &UStr<C> {
        UStr::from_slice(&self.inner)
    }
}

impl<C: UChar> Deref for UString<C> {
    type Target = UStr<C>;

    #[inline]
    fn deref(&self) -> &UStr<C> {
        &self[..]
    }
}

impl<C: UChar> PartialEq<UStr<C>> for UString<C> {
    #[inline]
    fn eq(&self, other: &UStr<C>) -> bool {
        self.as_ustr() == other
    }
}

impl<C: UChar> PartialOrd<UStr<C>> for UString<C> {
    #[inline]
    fn partial_cmp(&self, other: &UStr<C>) -> Option<cmp::Ordering> {
        self.as_ustr().partial_cmp(other)
    }
}

impl<'a, C: UChar> PartialEq<&'a UStr<C>> for UString<C> {
    #[inline]
    fn eq(&self, other: &&'a UStr<C>) -> bool {
        self.as_ustr() == *other
    }
}

impl<'a, C: UChar> PartialOrd<&'a UStr<C>> for UString<C> {
    #[inline]
    fn partial_cmp(&self, other: &&'a UStr<C>) -> Option<cmp::Ordering> {
        self.as_ustr().partial_cmp(*other)
    }
}

impl<'a, C: UChar> PartialEq<Cow<'a, UStr<C>>> for UString<C> {
    #[inline]
    fn eq(&self, other: &Cow<'a, UStr<C>>) -> bool {
        self.as_ustr() == other.as_ref()
    }
}

impl<'a, C: UChar> PartialOrd<Cow<'a, UStr<C>>> for UString<C> {
    #[inline]
    fn partial_cmp(&self, other: &Cow<'a, UStr<C>>) -> Option<cmp::Ordering> {
        self.as_ustr().partial_cmp(other.as_ref())
    }
}

impl<C: UChar> Borrow<UStr<C>> for UString<C> {
    #[inline]
    fn borrow(&self) -> &UStr<C> {
        &self[..]
    }
}

impl<C: UChar> ToOwned for UStr<C> {
    type Owned = UString<C>;

    #[inline]
    fn to_owned(&self) -> UString<C> {
        self.to_ustring()
    }
}

impl<'a> From<&'a UStr<u16>> for Cow<'a, UStr<u16>> {
    #[inline]
    fn from(s: &'a UStr<u16>) -> Self {
        Cow::Borrowed(s)
    }
}

impl<'a> From<&'a UStr<u32>> for Cow<'a, UStr<u32>> {
    #[inline]
    fn from(s: &'a UStr<u32>) -> Self {
        Cow::Borrowed(s)
    }
}

impl<C: UChar> AsRef<UStr<C>> for UStr<C> {
    #[inline]
    fn as_ref(&self) -> &Self {
        self
    }
}

impl<C: UChar> AsRef<UStr<C>> for UString<C> {
    #[inline]
    fn as_ref(&self) -> &UStr<C> {
        self
    }
}

impl<C: UChar> AsRef<[C]> for UStr<C> {
    #[inline]
    fn as_ref(&self) -> &[C] {
        self.as_slice()
    }
}

impl<C: UChar> AsRef<[C]> for UString<C> {
    #[inline]
    fn as_ref(&self) -> &[C] {
        self.as_slice()
    }
}

impl<'a, C: UChar> From<&'a UStr<C>> for Box<UStr<C>> {
    fn from(s: &'a UStr<C>) -> Self {
        let boxed: Box<[C]> = Box::from(&s.inner);
        let rw = Box::into_raw(boxed) as *mut UStr<C>;
        unsafe { Box::from_raw(rw) }
    }
}

impl<C: UChar> From<Box<UStr<C>>> for UString<C> {
    #[inline]
    fn from(boxed: Box<UStr<C>>) -> Self {
        boxed.into_ustring()
    }
}

impl<C: UChar> From<UString<C>> for Box<UStr<C>> {
    #[inline]
    fn from(s: UString<C>) -> Self {
        s.into_boxed_ustr()
    }
}

impl<C: UChar> Default for Box<UStr<C>> {
    #[inline]
    fn default() -> Self {
        let boxed: Box<[C]> = Box::from([]);
        let rw = Box::into_raw(boxed) as *mut UStr<C>;
        unsafe { Box::from_raw(rw) }
    }
}

/// An owned, mutable "wide" string for FFI that is **not** null-aware.
///
/// [`U16String`] is not aware of null values. Strings may or may not be null-terminated, and may
/// contain invalid and ill-formed UTF-16 data. These strings are intended to be used with
/// FFI functions that directly use string length, where the strings are known to have proper
/// null-termination already, or where strings are merely being passed through without modification.
///
/// [`U16CString`][crate::U16CString] should be used instead if null-aware strings are required.
///
/// [`U16String`] can be converted to and from many other standard Rust string types, including
/// [`OsString`][std::ffi::OsString] and [`String`], making proper Unicode FFI safe and easy.
///
/// # Examples
///
/// The following example constructs a [`U16String`] and shows how to convert a [`U16String`] to a
/// regular Rust [`String`].
///
/// ```rust
/// use widestring::U16String;
/// let s = "Test";
/// // Create a wide string from the rust string
/// let wstr = U16String::from_str(s);
/// // Convert back to a rust string
/// let rust_str = wstr.to_string_lossy();
/// assert_eq!(rust_str, "Test");
/// ```
pub type U16String = UString<u16>;

/// An owned, mutable 32-bit wide string for FFI that is **not** null-aware.
///
/// [`U32String`] is not aware of null values. Strings may or may not be null-terminated, and may
/// contain invalid and ill-formed UTF-32 data. These strings are intended to be used with
/// FFI functions that directly use string length, where the strings are known to have proper
/// null-termination already, or where strings are merely being passed through without modification.
///
/// [`U32CString`][crate::U32CString] should be used instead if null-aware 32-bit strings are
/// required.
///
/// [`U32String`] can be converted to and from many other standard Rust string types, including
/// [`OsString`][std::ffi::OsString] and [`String`], making proper Unicode FFI safe and easy.
///
/// # Examples
///
/// The following example constructs a [`U32String`] and shows how to convert a [`U32String`] to a
/// regular Rust [`String`].
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
pub type U32String = UString<u32>;

/// Alias for [`U16String`] or [`U32String`] depending on platform. Intended to match typical C
/// `wchar_t` size on platform.
pub type WideString = UString<WideChar>;
