use crate::{ContainsNull, UCStr, UChar, UStr, UString, WideChar};
use alloc::{
    borrow::{Cow, ToOwned},
    boxed::Box,
    vec::Vec,
};
use core::{
    borrow::Borrow,
    mem,
    ops::{Deref, Index, RangeFull},
    ptr, slice,
};

/// An owned, mutable C-style "wide" string for FFI that is null-aware and null-terminated
///
/// [`UCString`] is aware of null values. Unless unchecked conversions are used, all [`UCString`]
/// strings end with a null-terminator in the underlying buffer and contain no internal null values.
/// The strings may still contain invalid or ill-formed UTF-16 or UTF-32 data. These strings are
/// intended to be used with FFI functions such as Windows API that may require null-terminated
/// strings.
///
/// [`UCString`] can be converted to and from many other string types, including [`UString`],
/// [`OsString`][std::ffi::OsString], and [`String`], making proper Unicode FFI safe and easy.
///
/// Please prefer using the type aliases [`U16CString`], [`U32CString`], or [`WideCString`] to using
/// this type directly.
///
/// # Examples
///
/// The following example constructs a [`U16CString`] and shows how to convert a [`U16CString`] to a
/// regular Rust [`String`].
///
/// ```rust
/// use widestring::U16CString;
/// let s = "Test";
/// // Create a wide string from the rust string
/// let wstr = U16CString::from_str(s).unwrap();
/// // Convert back to a rust string
/// let rust_str = wstr.to_string_lossy();
/// assert_eq!(rust_str, "Test");
/// ```
///
/// The same example using [`U32CString`]:
///
/// ```rust
/// use widestring::U32CString;
/// let s = "Test";
/// // Create a wide string from the rust string
/// let wstr = U32CString::from_str(s).unwrap();
/// // Convert back to a rust string
/// let rust_str = wstr.to_string_lossy();
/// assert_eq!(rust_str, "Test");
/// ```
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UCString<C: UChar> {
    pub(crate) inner: Box<[C]>,
}

impl<C: UChar> UCString<C> {
    /// Constructs a [`UCString`] from a container of wide character data
    ///
    /// This method will consume the provided data and use the underlying elements to construct a
    /// new string. The data will be scanned for invalid interior null values.
    ///
    /// # Errors
    ///
    /// This function will return an error if the data contains a null value that is not the
    /// terminating null.
    /// The returned error will contain the original [`Vec`] as well as the position of the null
    /// value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U16CString;
    /// let v = vec![84u16, 104u16, 101u16]; // 'T' 'h' 'e'
    /// # let cloned = v.clone();
    /// // Create a wide string from the vector
    /// let wcstr = U16CString::from_vec(v).unwrap();
    /// # assert_eq!(wcstr.into_vec(), cloned);
    /// ```
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let v = vec![84u32, 104u32, 101u32]; // 'T' 'h' 'e'
    /// # let cloned = v.clone();
    /// // Create a wide string from the vector
    /// let wcstr = U32CString::from_vec(v).unwrap();
    /// # assert_eq!(wcstr.into_vec(), cloned);
    /// ```
    ///
    /// The following example demonstrates errors from null values in a vector.
    ///
    /// ```rust
    /// use widestring::U16CString;
    /// let v = vec![84u16, 0u16, 104u16, 101u16]; // 'T' NUL 'h' 'e'
    /// // Create a wide string from the vector
    /// let res = U16CString::from_vec(v);
    /// assert!(res.is_err());
    /// assert_eq!(res.err().unwrap().null_index(), 1);
    /// ```
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let v = vec![84u32, 0u32, 104u32, 101u32]; // 'T' NUL 'h' 'e'
    /// // Create a wide string from the vector
    /// let res = U32CString::from_vec(v);
    /// assert!(res.is_err());
    /// assert_eq!(res.err().unwrap().null_index(), 1);
    /// ```
    pub fn from_vec(v: impl Into<Vec<C>>) -> Result<Self, ContainsNull<C>> {
        let v = v.into();
        // Check for null vals, ignoring null terminator
        match v[..v.len() - 1].iter().position(|&val| val == UChar::NULL) {
            None => Ok(unsafe { Self::from_vec_unchecked(v) }),
            Some(pos) => Err(ContainsNull::new(pos, v)),
        }
    }

    /// Constructs a [`UCString`] from a container of wide character data, truncating at the first
    /// null terminator
    ///
    /// The string will be truncated at the first null value in the data.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U16CString;
    /// let v = vec![84u16, 104u16, 101u16, 0u16]; // 'T' 'h' 'e' NUL
    /// # let cloned = v[..3].to_owned();
    /// // Create a wide string from the vector
    /// let wcstr = U16CString::from_vec_truncate(v);
    /// # assert_eq!(wcstr.into_vec(), cloned);
    /// ```
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let v = vec![84u32, 104u32, 101u32, 0u32]; // 'T' 'h' 'e' NUL
    /// # let cloned = v[..3].to_owned();
    /// // Create a wide string from the vector
    /// let wcstr = U32CString::from_vec_truncate(v);
    /// # assert_eq!(wcstr.into_vec(), cloned);
    /// ```
    pub fn from_vec_truncate(v: impl Into<Vec<C>>) -> Self {
        let mut v = v.into();
        // Check for null vals
        if let Some(pos) = v.iter().position(|&val| val == UChar::NULL) {
            v.truncate(pos + 1);
        }
        unsafe { Self::from_vec_unchecked(v) }
    }

    /// Constructs a [`UCString`] from a vector without checking for interior null values
    ///
    /// A terminating null value will be appended if the vector does not already have a terminating
    /// null.
    ///
    /// # Safety
    ///
    /// This method is equivalent to [`from_vec`][Self::from_vec] except that no runtime assertion
    /// is made that `v` contains no interior null values. Providing a vector with any null values
    /// that are not the last value in the vector will result in an invalid [`UCString`].
    pub unsafe fn from_vec_unchecked(v: impl Into<Vec<C>>) -> Self {
        let mut v = v.into();
        match v.last() {
            None => v.push(UChar::NULL),
            Some(&c) if c != UChar::NULL => v.push(UChar::NULL),
            Some(_) => (),
        }
        Self {
            inner: v.into_boxed_slice(),
        }
    }

    /// Constructs a [`UCString`] from anything that can be converted to a [`UStr`]
    ///
    /// The string will be scanned for invalid interior null values.
    ///
    /// # Errors
    ///
    /// This function will return an error if the data contains a null value that is not the
    /// terminating null.
    /// The returned error will contain a [`Vec`] as well as the position of the null value.
    #[inline]
    pub fn from_ustr(s: impl AsRef<UStr<C>>) -> Result<Self, ContainsNull<C>> {
        Self::from_vec(s.as_ref().as_slice())
    }

    /// Constructs a [`UCString`] from anything that can be converted to a [`UStr`], truncating at
    /// the first null terminator
    ///
    /// The string will be truncated at the first null value in the string.
    #[inline]
    pub fn from_ustr_truncate(s: impl AsRef<UStr<C>>) -> Self {
        Self::from_vec_truncate(s.as_ref().as_slice())
    }

    /// Constructs a [`UCString`] from anything that can be converted to a [`UStr`], without
    /// scanning for invalid null values
    ///
    /// # Safety
    ///
    /// This method is equivalent to [`from_ustr`][Self::from_ustr] except that no runtime assertion
    /// is made that `v` contains no interior null values. Providing a string with any null values
    /// that are not the last value in the vector will result in an invalid [`UCString`].
    #[inline]
    pub unsafe fn from_ustr_unchecked(s: impl AsRef<UStr<C>>) -> Self {
        Self::from_vec_unchecked(s.as_ref().as_slice())
    }

    /// Constructs a new [`UCString`] copied from a null-terminated string pointer
    ///
    /// This will scan for null values beginning with `p`. The first null value will be used as the
    /// null terminator for the string, similar to how libc string functions such as `strlen` work.
    ///
    /// If you wish to avoid copying the string pointer, use [`UCStr::from_ptr_str`] instead.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid or has a
    /// null terminator, and the function could scan past the underlying buffer.
    ///
    /// In addition, the data must meet the safety conditions of [std::slice::from_raw_parts].
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
    #[inline]
    pub unsafe fn from_ptr_str(p: *const C) -> Self {
        UCStr::from_ptr_str(p).to_ucstring()
    }

    /// Constructs a [`UCString`] copied from a pointer and a length, checking for invalid interior
    /// null values
    ///
    /// The `len` argument is the number of elements, **not** the number of bytes, and does
    /// **not** include the null terminator of the string. If `len` is `0`, `p` is allowed to be a
    /// null pointer.
    ///
    /// The resulting string will always be null-terminated even if the pointer data is not.
    ///
    /// # Errors
    ///
    /// This will scan the pointer string for an interior null value and error if one is found. To
    /// avoid scanning for interior nulls, [`from_ptr_unchecked`][Self::from_ptr_unchecked] may be
    /// used instead.
    /// The returned error will contain a [`Vec`] as well as the position of the null value.
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
    pub unsafe fn from_ptr(p: *const C, len: usize) -> Result<Self, ContainsNull<C>> {
        if len == 0 {
            return Ok(Self::default());
        }
        assert!(!p.is_null());
        let slice = slice::from_raw_parts(p, len);
        Self::from_vec(slice)
    }

    /// Constructs a [`UCString`] copied from a pointer and a length, truncating at the first null
    /// terminator
    ///
    /// The `len` argument is the number of elements, **not** the number of bytes. This will scan
    /// for null values beginning with `p` until offset `len`. The first null value will be used as
    /// the null terminator for the string, ignoring any remaining values left before `len`. If no
    /// null value is found, the whole string of length `len` is used, and a new null-terminator
    /// will be added to the resulting string. If `len` is `0`, `p` is allowed to be a null pointer.
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
    pub unsafe fn from_ptr_truncate(p: *const C, len: usize) -> Self {
        if len == 0 {
            return Self::default();
        }
        assert!(!p.is_null());
        let slice = slice::from_raw_parts(p, len);
        Self::from_vec_truncate(slice)
    }

    /// Constructs a [`UCString`] copied from a pointer and a length without checking for any null
    /// values
    ///
    /// The `len` argument is the number of elements, **not** the number of bytes, and does
    /// **not** include the null terminator of the string. If `len` is `0`, `p` is allowed to be a
    /// null pointer.
    ///
    /// The resulting string will always be null-terminated even if the pointer data is not.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements.
    ///
    /// In addition, the data must meet the safety conditions of [std::slice::from_raw_parts].
    ///
    /// The interior values of the pointer are not scanned for null. Any interior null values or
    /// will result in an invalid [`UCString`].
    ///
    /// # Panics
    ///
    /// Panics if `len` is greater than 0 but `p` is a null pointer.
    pub unsafe fn from_ptr_unchecked(p: *const C, len: usize) -> Self {
        if len == 0 {
            return Self::default();
        }
        assert!(!p.is_null());
        let slice = slice::from_raw_parts(p, len);
        Self::from_vec_unchecked(slice)
    }

    /// Converts to a [`UCStr`] reference.
    #[inline]
    pub fn as_ucstr(&self) -> &UCStr<C> {
        self
    }

    /// Converts the string into a [`Vec`] without a null terminator, consuming the string in
    /// the process
    ///
    /// The resulting vector will **not** contain a null-terminator, and will contain no other null
    /// values.
    #[inline]
    pub fn into_vec(self) -> Vec<C> {
        let mut v = self.into_inner().into_vec();
        v.pop();
        v
    }

    /// Converts the string into a [`Vec`], consuming the string in the process
    ///
    /// The resulting vector will contain a null-terminator and no interior null values.
    #[inline]
    pub fn into_vec_with_null(self) -> Vec<C> {
        self.into_inner().into_vec()
    }

    /// Transfers ownership of the string to a C caller
    ///
    /// # Safety
    ///
    /// The pointer _must_ be returned to Rust and reconstituted using
    /// [`from_raw`][Self::from_raw] to be properly deallocated. Specifically, one should _not_ use
    /// the standard C `free` function to deallocate this string. Failure to call
    /// [`from_raw`][Self::from_raw] will lead to a memory leak.
    #[inline]
    pub fn into_raw(self) -> *mut C {
        Box::into_raw(self.into_inner()) as *mut C
    }

    /// Retakes ownership of a [`UCString`] that was transferred to C
    ///
    /// This should only be used in combination with [`into_raw`][Self::into_raw]. To construct a
    /// new [`UCString`] from a pointer, use [`from_ptr_str`][Self::from_ptr_str].
    ///
    /// # Safety
    ///
    /// This should only ever be called with a pointer that was earlier obtained by calling
    /// [`into_raw`][Self::into_raw]. Additionally, the length of the string will be recalculated
    /// from the pointer by scanning for the null-terminator.
    pub unsafe fn from_raw(p: *mut C) -> Self {
        assert!(!p.is_null());
        let mut i: isize = 0;
        while *p.offset(i) != UChar::NULL {
            i += 1;
        }
        let slice = slice::from_raw_parts_mut(p, i as usize + 1);
        Self {
            inner: Box::from_raw(slice),
        }
    }

    /// Converts this [`UCString`] into a boxed [`UCStr`]
    ///
    /// # Examples
    ///
    /// ```
    /// use widestring::{U16CString, U16CStr};
    ///
    /// let mut v = vec![102u16, 111u16, 111u16]; // "foo"
    /// let c_string = U16CString::from_vec(v.clone()).unwrap();
    /// let boxed = c_string.into_boxed_ucstr();
    /// v.push(0);
    /// assert_eq!(&*boxed, U16CStr::from_slice(&v).unwrap());
    /// ```
    ///
    /// ```
    /// use widestring::{U32CString, U32CStr};
    ///
    /// let mut v = vec![102u32, 111u32, 111u32]; // "foo"
    /// let c_string = U32CString::from_vec(v.clone()).unwrap();
    /// let boxed = c_string.into_boxed_ucstr();
    /// v.push(0);
    /// assert_eq!(&*boxed, U32CStr::from_slice(&v).unwrap());
    /// ```
    #[inline]
    pub fn into_boxed_ucstr(self) -> Box<UCStr<C>> {
        unsafe { Box::from_raw(Box::into_raw(self.into_inner()) as *mut UCStr<C>) }
    }

    #[allow(deprecated)]
    #[doc(hidden)]
    #[deprecated = "use `from_vec` instead"]
    pub fn new(v: impl Into<Vec<C>>) -> Result<Self, crate::NulError<C>> {
        Self::from_vec(v)
    }

    #[allow(deprecated)]
    #[doc(hidden)]
    #[deprecated = "use `from_vec_truncate` instead"]
    pub fn from_vec_with_nul(v: impl Into<Vec<C>>) -> Result<Self, crate::MissingNulError> {
        Ok(Self::from_vec_truncate(v))
    }

    #[allow(deprecated)]
    #[doc(hidden)]
    #[deprecated = "use `from_ustr_truncate` instead"]
    pub fn from_ustr_with_nul(s: impl AsRef<UStr<C>>) -> Result<Self, crate::MissingNulError> {
        Ok(Self::from_ustr_truncate(s))
    }

    #[allow(deprecated)]
    #[doc(hidden)]
    #[deprecated = "use `from_ptr_truncate` instead"]
    pub unsafe fn from_ptr_with_nul(
        p: *const C,
        len: usize,
    ) -> Result<Self, crate::MissingNulError> {
        Ok(Self::from_ptr_truncate(p, len))
    }

    #[doc(hidden)]
    #[deprecated = "use `from_vec_unchecked` instead"]
    pub unsafe fn from_vec_with_nul_unchecked(v: impl Into<Vec<C>>) -> Self {
        Self::from_vec_unchecked(v)
    }

    #[doc(hidden)]
    #[deprecated = "use `from_ustr_unchecked` instead"]
    pub unsafe fn from_ustr_with_nul_unchecked(v: impl AsRef<UStr<C>>) -> Self {
        Self::from_ustr_unchecked(v)
    }

    #[doc(hidden)]
    #[deprecated = "use `from_ptr_unchecked` instead"]
    pub unsafe fn from_ptr_with_nul_unchecked(p: *const C, len: usize) -> Self {
        Self::from_ptr_unchecked(p, len)
    }

    #[doc(hidden)]
    #[deprecated = "use `into_vec_with_null` instead"]
    pub fn into_vec_with_nul(self) -> Vec<C> {
        self.into_vec_with_null()
    }

    /// Bypass "move out of struct which implements [`Drop`] trait" restriction.
    fn into_inner(self) -> Box<[C]> {
        let result = unsafe { ptr::read(&self.inner) };
        mem::forget(self);
        result
    }
}

impl UCString<u16> {
    /// Encodes a [`U16CString`] copied from a [`str`]
    ///
    /// The string will be scanned for null values, which are invalid anywhere except the final
    /// character.
    ///
    /// The resulting string will always be null-terminated even if the original string is not.
    ///
    /// # Errors
    ///
    /// This function will return an error if the data contains a null value anywhere except the
    /// final position.
    /// The returned error will contain a [`Vec<u16>`] as well as the position of the null value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U16CString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wcstr = U16CString::from_str(s).unwrap();
    /// # assert_eq!(wcstr.to_string_lossy(), s);
    /// ```
    ///
    /// The following example demonstrates errors from null values in a string.
    ///
    /// ```rust
    /// use widestring::U16CString;
    /// let s = "My\u{0}String";
    /// // Create a wide string from the string
    /// let res = U16CString::from_str(s);
    /// assert!(res.is_err());
    /// assert_eq!(res.err().unwrap().null_index(), 2);
    /// ```
    #[allow(clippy::should_implement_trait)]
    #[inline]
    pub fn from_str(s: impl AsRef<str>) -> Result<Self, ContainsNull<u16>> {
        let v: Vec<u16> = s.as_ref().encode_utf16().collect();
        Self::from_vec(v)
    }

    /// Encodes a [`U16CString`] copied from a [`str`], without checking for interior null values
    ///
    /// The resulting string will always be null-terminated even if the original string is not.
    ///
    /// # Safety
    ///
    /// This method is equivalent to [`from_str`][Self::from_str] except that no runtime assertion
    /// is made that `s` contains no interior null values. Providing a string with null values that
    /// are not the last character will result in an invalid [`U16CString`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U16CString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wcstr = unsafe { U16CString::from_str_unchecked(s) };
    /// # assert_eq!(wcstr.to_string_lossy(), s);
    /// ```
    #[inline]
    pub unsafe fn from_str_unchecked(s: impl AsRef<str>) -> Self {
        let v: Vec<u16> = s.as_ref().encode_utf16().collect();
        Self::from_vec_unchecked(v)
    }

    /// Encodes a [`U16CString`] copied from a [`str`], truncating at the first null terminator
    ///
    /// The string will be truncated at the first null value in the string.
    /// The resulting string will always be null-terminated even if the original string is not.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U16CString;
    /// let s = "My\u{0}String";
    /// // Create a wide string from the string
    /// let wcstr = U16CString::from_str_truncate(s);
    /// assert_eq!(wcstr.to_string_lossy(), "My");
    /// ```
    #[inline]
    pub fn from_str_truncate(s: impl AsRef<str>) -> Self {
        let v: Vec<u16> = s.as_ref().encode_utf16().collect();
        Self::from_vec_truncate(v)
    }

    /// Encodes a [`U16CString`] copied from anything that can be converted to an
    /// [`OsStr`][std::ffi::OsStr]
    ///
    /// The string will be scanned for null values, which are invalid anywhere except the final
    /// character.
    /// The resulting string will always be null-terminated even if the original string is not.
    ///
    /// # Errors
    ///
    /// This function will return an error if the data contains a null value anywhere except the
    /// last character.
    /// The returned error will contain a [`Vec<u16>`] as well as the position of the nul value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U16CString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wcstr = U16CString::from_os_str(s).unwrap();
    /// # assert_eq!(wcstr.to_string_lossy(), s);
    /// ```
    ///
    /// The following example demonstrates errors from null values in the string.
    ///
    /// ```rust
    /// use widestring::U16CString;
    /// let s = "My\u{0}String";
    /// // Create a wide string from the string
    /// let res = U16CString::from_os_str(s);
    /// assert!(res.is_err());
    /// assert_eq!(res.err().unwrap().null_index(), 2);
    /// ```
    #[inline]
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    pub fn from_os_str(s: impl AsRef<std::ffi::OsStr>) -> Result<Self, ContainsNull<u16>> {
        let v = crate::platform::os_to_wide(s.as_ref());
        Self::from_vec(v)
    }

    /// Encodes a [`U16CString`] from anything that can be converted to an
    /// [`OsStr`][std::ffi::OsStr], without checking for null values.
    ///
    /// The resulting string will always be null-terminated even if the original string is not.
    ///
    /// # Safety
    ///
    /// This method is equivalent to [`from_os_str`][Self::from_os_str] except that no runtime
    /// assertion is made that `s` contains no interior null values. Providing a string with null
    /// values anywhere but the last character will result in an invalid [`U16CString`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U16CString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wcstr = unsafe { U16CString::from_os_str_unchecked(s) };
    /// # assert_eq!(wcstr.to_string_lossy(), s);
    /// ```
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    pub unsafe fn from_os_str_unchecked(s: impl AsRef<std::ffi::OsStr>) -> Self {
        let v = crate::platform::os_to_wide(s.as_ref());
        Self::from_vec_unchecked(v)
    }

    /// Encodes a [`U16CString`] copied from anything that can be converted to an
    /// [`OsStr`][std::ffi::OsStr], truncating at the first null terminator
    ///
    /// The string will be truncated at the first null value in the string.
    /// The resulting string will always be null-terminated even if the original string is not.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U16CString;
    /// let s = "My\u{0}String";
    /// // Create a wide string from the string
    /// let wcstr = U16CString::from_os_str_truncate(s);
    /// assert_eq!(wcstr.to_string_lossy(), "My");
    /// ```
    #[inline]
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    pub fn from_os_str_truncate(s: impl AsRef<std::ffi::OsStr>) -> Self {
        let v = crate::platform::os_to_wide(s.as_ref());
        Self::from_vec_truncate(v)
    }

    #[allow(deprecated)]
    #[doc(hidden)]
    #[deprecated = "use `from_str_truncate` instead"]
    pub fn from_str_with_nul(s: impl AsRef<str>) -> Result<Self, crate::MissingNulError> {
        Ok(Self::from_str_truncate(s))
    }

    #[cfg(feature = "std")]
    #[allow(deprecated)]
    #[doc(hidden)]
    #[deprecated = "use `from_os_str_truncate` instead"]
    pub fn from_os_str_with_nul(
        s: impl AsRef<std::ffi::OsStr>,
    ) -> Result<Self, crate::MissingNulError> {
        Ok(Self::from_os_str_truncate(s))
    }

    #[doc(hidden)]
    #[deprecated = "use `from_str_unchecked` instead"]
    pub unsafe fn from_str_with_nul_unchecked(s: impl AsRef<str>) -> Self {
        Self::from_str_unchecked(s)
    }

    #[cfg(feature = "std")]
    #[doc(hidden)]
    #[deprecated = "use `from_os_str_unchecked` instead"]
    pub unsafe fn from_os_str_with_nul_unchecked(s: impl AsRef<std::ffi::OsStr>) -> Self {
        Self::from_os_str_unchecked(s)
    }
}

impl UCString<u32> {
    /// Constructs a [`U32CString`] from a container of character data, checking for invalid null
    /// values
    ///
    /// This method will consume the provided data and use the underlying elements to construct a
    /// new string. The data will be scanned for invalid null values anywhere except the last
    /// character.
    /// The resulting string will always be null-terminated even if the original string is not.
    ///
    /// # Errors
    ///
    /// This function will return an error if the data contains a null value anywhere except the
    /// last character.
    /// The returned error will contain the [`Vec<u32>`] as well as the position of the null value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let v: Vec<char> = "Test".chars().collect();
    /// # let cloned: Vec<u32> = v.iter().map(|&c| c as u32).collect();
    /// // Create a wide string from the vector
    /// let wcstr = U32CString::from_chars(v).unwrap();
    /// # assert_eq!(wcstr.into_vec(), cloned);
    /// ```
    ///
    /// The following example demonstrates errors from null values in a vector.
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let v: Vec<char> = "T\u{0}est".chars().collect();
    /// // Create a wide string from the vector
    /// let res = U32CString::from_chars(v);
    /// assert!(res.is_err());
    /// assert_eq!(res.err().unwrap().null_index(), 1);
    /// ```
    pub fn from_chars(v: impl Into<Vec<char>>) -> Result<Self, ContainsNull<u32>> {
        let mut chars = v.into();
        let v: Vec<u32> = unsafe {
            let ptr = chars.as_mut_ptr() as *mut u32;
            let len = chars.len();
            let cap = chars.capacity();
            mem::forget(chars);
            Vec::from_raw_parts(ptr, len, cap)
        };
        Self::from_vec(v)
    }

    /// Constructs a [`U32CString`] from a container of character data, truncating at the first null
    /// value
    ///
    /// This method will consume the provided data and use the underlying elements to construct a
    /// new string. The string will be truncated at the first null value in the string.
    /// The resulting string will always be null-terminated even if the original string is not.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let v: Vec<char> = "Test\u{0}".chars().collect();
    /// # let cloned: Vec<u32> = v[..4].iter().map(|&c| c as u32).collect();
    /// // Create a wide string from the vector
    /// let wcstr = U32CString::from_chars_truncate(v);
    /// # assert_eq!(wcstr.into_vec(), cloned);
    /// ```
    pub fn from_chars_truncate(v: impl Into<Vec<char>>) -> Self {
        let mut chars = v.into();
        let v: Vec<u32> = unsafe {
            let ptr = chars.as_mut_ptr() as *mut u32;
            let len = chars.len();
            let cap = chars.capacity();
            mem::forget(chars);
            Vec::from_raw_parts(ptr, len, cap)
        };
        Self::from_vec_truncate(v)
    }

    /// Constructs a [`U32CString`] from character data without checking for null values
    ///
    /// A terminating null value will be appended if the vector does not already have a terminating
    /// null.
    ///
    /// # Safety
    ///
    /// This method is equivalent to [`from_chars`][Self::from_chars] except that no runtime
    /// assertion is made that `v` contains no interior null values. Providing a vector with null
    /// values anywhere but the last character will result in an invalid [`U32CString`].
    pub unsafe fn from_chars_unchecked(v: impl Into<Vec<char>>) -> Self {
        let mut chars = v.into();
        let v: Vec<u32> = {
            let ptr = chars.as_mut_ptr() as *mut u32;
            let len = chars.len();
            let cap = chars.capacity();
            mem::forget(chars);
            Vec::from_raw_parts(ptr, len, cap)
        };
        Self::from_vec_unchecked(v)
    }

    /// Encodes a [`U32CString`] copied from a [`str`], checking for invalid interior null values
    ///
    /// The string will be scanned for null values, which are invalid anywhere except the last
    /// character.
    /// The resulting string will always be null-terminated even if the original string is not.
    ///
    /// # Errors
    ///
    /// This function will return an error if the data contains a null value anywhere except the
    /// last character.
    /// The returned error will contain a [`Vec<u32>`] as well as the position of the null value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wcstr = U32CString::from_str(s).unwrap();
    /// # assert_eq!(wcstr.to_string_lossy(), s);
    /// ```
    ///
    /// The following example demonstrates errors from null values in a string.
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let s = "My\u{0}String";
    /// // Create a wide string from the string
    /// let res = U32CString::from_str(s);
    /// assert!(res.is_err());
    /// assert_eq!(res.err().unwrap().null_index(), 2);
    /// ```
    #[allow(clippy::should_implement_trait)]
    #[inline]
    pub fn from_str(s: impl AsRef<str>) -> Result<Self, ContainsNull<u32>> {
        let v: Vec<char> = s.as_ref().chars().collect();
        Self::from_chars(v)
    }

    /// Encodes a [`U32CString`] copied from a [`str`], without checking for null values.
    ///
    /// The resulting string will always be null-terminated even if the original string is not.
    ///
    /// # Safety
    ///
    /// This method is equivalent to [`from_str`][Self::from_str] except that no runtime assertion
    /// is made that `s` contains invalid null values. Providing a string with null values anywhere
    /// except the last character will result in an invalid [`U32CString`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wcstr = unsafe { U32CString::from_str_unchecked(s) };
    /// # assert_eq!(wcstr.to_string_lossy(), s);
    /// ```
    #[inline]
    pub unsafe fn from_str_unchecked(s: impl AsRef<str>) -> Self {
        let v: Vec<char> = s.as_ref().chars().collect();
        Self::from_chars_unchecked(v)
    }

    /// Encodes a [`U32CString`] copied from a [`str`], truncating at the first null terminator
    ///
    /// The string will be truncated at the first null value in the string.
    /// The resulting string will always be null-terminated even if the original string is not.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let s = "My\u{0}String";
    /// // Create a wide string from the string
    /// let wcstr = U32CString::from_str_truncate(s);
    /// assert_eq!(wcstr.to_string_lossy(), "My");
    /// ```
    #[inline]
    pub fn from_str_truncate(s: impl AsRef<str>) -> Self {
        let v: Vec<char> = s.as_ref().chars().collect();
        Self::from_chars_truncate(v)
    }

    /// Constructs a new [`UCString`] copied from a null-terminated [`char`] string pointer
    ///
    /// This will scan for null values beginning with `p`. The first null value will be used as the
    /// null terminator for the string, similar to how libc string functions such as `strlen` work.
    ///
    /// If you wish to avoid copying the string pointer, use [`UCStr::from_char_ptr_str`] instead.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid or has a
    /// null terminator, and the function could scan past the underlying buffer.
    ///
    /// In addition, the data must meet the safety conditions of [std::slice::from_raw_parts].
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
    #[inline]
    pub unsafe fn from_char_ptr_str(p: *const char) -> Self {
        Self::from_ptr_str(p as *const u32)
    }

    /// Constructs a [`UCString`] copied from a [`char`] pointer and a length, checking for invalid
    /// interior null values
    ///
    /// The `len` argument is the number of elements, **not** the number of bytes, and does
    /// **not** include the null terminator of the string. If `len` is `0`, `p` is allowed to be a
    /// null pointer.
    ///
    /// The resulting string will always be null-terminated even if the pointer data is not.
    ///
    /// # Errors
    ///
    /// This will scan the pointer string for an interior null value and error if one is found. To
    /// avoid scanning for interior nulls, [`from_ptr_unchecked`][Self::from_ptr_unchecked] may be
    /// used instead.
    /// The returned error will contain a [`Vec`] as well as the position of the null value.
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
    pub unsafe fn from_char_ptr(p: *const char, len: usize) -> Result<Self, ContainsNull<u32>> {
        Self::from_ptr(p as *const u32, len)
    }

    /// Constructs a [`UCString`] copied from a [`char`] pointer and a length, truncating at the
    /// first null terminator
    ///
    /// The `len` argument is the number of elements, **not** the number of bytes. This will scan
    /// for null values beginning with `p` until offset `len`. The first null value will be used as
    /// the null terminator for the string, ignoring any remaining values left before `len`. If no
    /// null value is found, the whole string of length `len` is used, and a new null-terminator
    /// will be added to the resulting string. If `len` is `0`, `p` is allowed to be a null pointer.
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
    pub unsafe fn from_char_ptr_truncate(p: *const char, len: usize) -> Self {
        Self::from_ptr_truncate(p as *const u32, len)
    }

    /// Constructs a [`UCString`] copied from a [`char`] pointer and a length without checking for
    /// any null values
    ///
    /// The `len` argument is the number of elements, **not** the number of bytes, and does
    /// **not** include the null terminator of the string. If `len` is `0`, `p` is allowed to be a
    /// null pointer.
    ///
    /// The resulting string will always be null-terminated even if the pointer data is not.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements.
    ///
    /// In addition, the data must meet the safety conditions of [std::slice::from_raw_parts].
    ///
    /// The interior values of the pointer are not scanned for null. Any interior null values or
    /// will result in an invalid [`UCString`].
    ///
    /// # Panics
    ///
    /// Panics if `len` is greater than 0 but `p` is a null pointer.
    pub unsafe fn from_char_ptr_unchecked(p: *const char, len: usize) -> Self {
        Self::from_ptr_unchecked(p as *const u32, len)
    }

    /// Encodes a [`U32CString`] copied from anything that can be converted to an
    /// [`OsStr`][std::ffi::OsStr], checking for invalid null values
    ///
    /// The string will be scanned for null values, which are invlaid anywhere except the last
    /// character.
    /// The resulting string will always be null-terminated even if the string is not.
    ///
    /// # Errors
    ///
    /// This function will return an error if the data contains a null value anywhere except the
    /// last character.
    /// The returned error will contain a [`Vec<u16>`] as well as the position of the null value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wcstr = U32CString::from_os_str(s).unwrap();
    /// # assert_eq!(wcstr.to_string_lossy(), s);
    /// ```
    ///
    /// The following example demonstrates errors from null values in a string.
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let s = "My\u{0}String";
    /// // Create a wide string from the string
    /// let res = U32CString::from_os_str(s);
    /// assert!(res.is_err());
    /// assert_eq!(res.err().unwrap().null_index(), 2);
    /// ```
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    #[inline]
    pub fn from_os_str(s: impl AsRef<std::ffi::OsStr>) -> Result<Self, ContainsNull<u32>> {
        let v: Vec<char> = s.as_ref().to_string_lossy().chars().collect();
        UCString::from_chars(v)
    }

    /// Encodes a [`U32CString`] copied from anything that can be converted to an
    /// [`OsStr`][std::ffi::OsStr], without checking for null values
    ///
    /// The resulting string will always be null-terminated even if the string is not.
    ///
    /// # Safety
    ///
    /// This method is equivalent to [`from_os_str`][Self::from_os_str] except that no runtime
    /// assertion is made that `s` contains invalid null values. Providing a string with null values
    /// anywhere except the last character will result in an invalid [`U32CString`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wcstr = unsafe { U32CString::from_os_str_unchecked(s) };
    /// # assert_eq!(wcstr.to_string_lossy(), s);
    /// ```
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    #[inline]
    pub unsafe fn from_os_str_unchecked(s: impl AsRef<std::ffi::OsStr>) -> Self {
        let v: Vec<char> = s.as_ref().to_string_lossy().chars().collect();
        UCString::from_chars_unchecked(v)
    }

    /// Encodes a [`U32CString`] copied from anything that can be converted to an
    /// [`OsStr`][std::ffi::OsStr], truncating at the first null terminator
    ///
    /// The string will be truncated at the first null value in the string.
    /// The resulting string will always be null-terminated even if the string is not.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let s = "My\u{0}String";
    /// // Create a wide string from the string
    /// let wcstr = U32CString::from_os_str_truncate(s);
    /// assert_eq!(wcstr.to_string_lossy(), "My");
    /// ```
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    #[inline]
    pub fn from_os_str_truncate(s: impl AsRef<std::ffi::OsStr>) -> Self {
        let v: Vec<char> = s.as_ref().to_string_lossy().chars().collect();
        UCString::from_chars_truncate(v)
    }

    #[allow(deprecated)]
    #[doc(hidden)]
    #[deprecated = "use `from_str_truncate` instead"]
    pub fn from_str_with_nul(s: impl AsRef<str>) -> Result<Self, crate::MissingNulError> {
        Ok(Self::from_str_truncate(s))
    }

    #[cfg(feature = "std")]
    #[allow(deprecated)]
    #[doc(hidden)]
    #[deprecated = "use `from_os_str_truncate` instead"]
    pub fn from_os_str_with_nul(
        s: impl AsRef<std::ffi::OsStr>,
    ) -> Result<Self, crate::MissingNulError> {
        Ok(Self::from_os_str_truncate(s))
    }

    #[allow(deprecated)]
    #[doc(hidden)]
    #[deprecated = "use `from_chars_truncate` instead"]
    pub fn from_chars_with_nul(v: impl Into<Vec<char>>) -> Result<Self, crate::MissingNulError> {
        Ok(Self::from_chars_truncate(v))
    }

    #[allow(deprecated)]
    #[doc(hidden)]
    #[deprecated = "use `from_char_ptr_truncate` instead"]
    pub unsafe fn from_char_ptr_with_nul(
        p: *const char,
        len: usize,
    ) -> Result<Self, crate::MissingNulError> {
        Ok(Self::from_char_ptr_truncate(p, len))
    }

    #[doc(hidden)]
    #[deprecated = "use `from_str_unchecked` instead"]
    pub unsafe fn from_str_with_nul_unchecked(s: impl AsRef<str>) -> Self {
        Self::from_str_unchecked(s)
    }

    #[cfg(feature = "std")]
    #[doc(hidden)]
    #[deprecated = "use `from_os_str_unchecked` instead"]
    pub unsafe fn from_os_str_with_nul_unchecked(s: impl AsRef<std::ffi::OsStr>) -> Self {
        Self::from_os_str_unchecked(s)
    }

    #[doc(hidden)]
    #[deprecated = "use `from_chars_unchecked` instead"]
    pub unsafe fn from_chars_with_nul_unchecked(v: impl Into<Vec<char>>) -> Self {
        Self::from_chars_unchecked(v)
    }

    #[doc(hidden)]
    #[deprecated = "use `from_char_ptr_unchecked` instead"]
    pub unsafe fn from_char_ptr_with_nul_unchecked(p: *const char, len: usize) -> Self {
        Self::from_char_ptr_unchecked(p, len)
    }
}

impl<C: UChar> From<UCString<C>> for Vec<C> {
    #[inline]
    fn from(value: UCString<C>) -> Self {
        value.into_vec()
    }
}

impl<'a, C: UChar> From<UCString<C>> for Cow<'a, UCStr<C>> {
    #[inline]
    fn from(s: UCString<C>) -> Cow<'a, UCStr<C>> {
        Cow::Owned(s)
    }
}

#[cfg(feature = "std")]
impl From<UCString<u16>> for std::ffi::OsString {
    #[inline]
    fn from(s: UCString<u16>) -> std::ffi::OsString {
        s.to_os_string()
    }
}

#[cfg(feature = "std")]
impl From<UCString<u32>> for std::ffi::OsString {
    #[inline]
    fn from(s: UCString<u32>) -> std::ffi::OsString {
        s.to_os_string()
    }
}

impl<C: UChar> From<UCString<C>> for UString<C> {
    #[inline]
    fn from(s: UCString<C>) -> Self {
        s.to_ustring()
    }
}

impl<'a, C: UChar, T: ?Sized + AsRef<UCStr<C>>> From<&'a T> for UCString<C> {
    #[inline]
    fn from(s: &'a T) -> Self {
        s.as_ref().to_ucstring()
    }
}

impl<C: UChar> Index<RangeFull> for UCString<C> {
    type Output = UCStr<C>;

    #[inline]
    fn index(&self, _index: RangeFull) -> &UCStr<C> {
        UCStr::from_inner(&self.inner)
    }
}

impl<C: UChar> Deref for UCString<C> {
    type Target = UCStr<C>;

    #[inline]
    fn deref(&self) -> &UCStr<C> {
        &self[..]
    }
}

impl<C: UChar> Default for UCString<C> {
    fn default() -> Self {
        unsafe { Self::from_vec_unchecked(Vec::new()) }
    }
}

// Turns this `UCString` into an empty string to prevent
// memory unsafe code from working by accident. Inline
// to prevent LLVM from optimizing it away in debug builds.
impl<C: UChar> Drop for UCString<C> {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            *self.inner.get_unchecked_mut(0) = UChar::NULL;
        }
    }
}

impl<C: UChar> Borrow<UCStr<C>> for UCString<C> {
    #[inline]
    fn borrow(&self) -> &UCStr<C> {
        &self[..]
    }
}

impl<C: UChar> ToOwned for UCStr<C> {
    type Owned = UCString<C>;

    #[inline]
    fn to_owned(&self) -> UCString<C> {
        self.to_ucstring()
    }
}

impl<'a> From<&'a UCStr<u16>> for Cow<'a, UCStr<u16>> {
    #[inline]
    fn from(s: &'a UCStr<u16>) -> Cow<'a, UCStr<u16>> {
        Cow::Borrowed(s)
    }
}

impl<'a> From<&'a UCStr<u32>> for Cow<'a, UCStr<u32>> {
    #[inline]
    fn from(s: &'a UCStr<u32>) -> Cow<'a, UCStr<u32>> {
        Cow::Borrowed(s)
    }
}

impl<C: UChar> AsRef<UCStr<C>> for UCString<C> {
    #[inline]
    fn as_ref(&self) -> &UCStr<C> {
        self
    }
}

impl<C: UChar> AsRef<[C]> for UCString<C> {
    #[inline]
    fn as_ref(&self) -> &[C] {
        self.as_slice()
    }
}

impl<C: UChar> From<Box<UCStr<C>>> for UCString<C> {
    #[inline]
    fn from(s: Box<UCStr<C>>) -> Self {
        s.into_ucstring()
    }
}

impl<C: UChar> From<UCString<C>> for Box<UCStr<C>> {
    #[inline]
    fn from(s: UCString<C>) -> Box<UCStr<C>> {
        s.into_boxed_ucstr()
    }
}

/// An owned, mutable C-style "wide" string for FFI that is nul-aware and nul-terminated.
///
/// `U16CString` is aware of nul values. Unless unchecked conversions are used, all `U16CString`
/// strings end with a nul-terminator in the underlying buffer and contain no internal nul values.
/// The strings may still contain invalid or ill-formed UTF-16 data. These strings are intended to
/// be used with FFI functions such as Windows API that may require nul-terminated strings.
///
/// `U16CString` can be converted to and from many other string types, including `U16String`,
/// `OsString`, and `String`, making proper Unicode FFI safe and easy.
///
/// # Examples
///
/// The following example constructs a `U16CString` and shows how to convert a `U16CString` to a
/// regular Rust `String`.
///
/// ```rust
/// use widestring::U16CString;
/// let s = "Test";
/// // Create a wide string from the rust string
/// let wstr = U16CString::from_str(s).unwrap();
/// // Convert back to a rust string
/// let rust_str = wstr.to_string_lossy();
/// assert_eq!(rust_str, "Test");
/// ```
pub type U16CString = UCString<u16>;

/// An owned, mutable C-style wide string for FFI that is nul-aware and nul-terminated.
///
/// `U32CString` is aware of nul values. Unless unchecked conversions are used, all `U32CString`
/// strings end with a nul-terminator in the underlying buffer and contain no internal nul values.
/// The strings may still contain invalid or ill-formed UTF-32 data. These strings are intended to
/// be used with FFI functions such as Windows API that may require nul-terminated strings.
///
/// `U32CString` can be converted to and from many other string types, including `U32String`,
/// `OsString`, and `String`, making proper Unicode FFI safe and easy.
///
/// # Examples
///
/// The following example constructs a `U32CString` and shows how to convert a `U32CString` to a
/// regular Rust `String`.
///
/// ```rust
/// use widestring::U32CString;
/// let s = "Test";
/// // Create a wide string from the rust string
/// let wstr = U32CString::from_str(s).unwrap();
/// // Convert back to a rust string
/// let rust_str = wstr.to_string_lossy();
/// assert_eq!(rust_str, "Test");
/// ```
pub type U32CString = UCString<u32>;

/// Alias for `U16String` or `U32String` depending on platform. Intended to match typical C `wchar_t` size on platform.
pub type WideCString = UCString<WideChar>;
