//! Wide string slices
//!
//! This module contains the [`UStr`] string slices and related types.

use crate::{UChar, WideChar};
#[cfg(feature = "alloc")]
use alloc::{
    boxed::Box,
    string::{FromUtf16Error, String},
    vec::Vec,
};
use core::{char, fmt::Write, slice};

/// String slice reference for [`UString`][crate::UString]
///
/// [`UStr`] is to [`UString`][crate::UString] as [`str`] is to [`String`].
///
/// [`UStr`] is not aware of null values. Strings may or may not be null-terminated, and may
/// contain invalid and ill-formed UTF-16 or UTF-32 data. These strings are intended to be used
/// with FFI functions that directly use string length, where the strings are known to have proper
/// null-termination already, or where strings are merely being passed through without modification.
///
/// [`UCStr`][crate::UCStr] should be used instead if null-aware strings are required.
///
/// [`UStr`] can be converted to many other string types, including [`OsString`][std::ffi::OsString]
/// and [`String`], making proper Unicode FFI safe and easy.
///
/// Please prefer using the type aliases [`U16Str`], [`U32Str`] or [`WideStr`] to using this type
/// directly.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UStr<C: UChar> {
    pub(crate) inner: [C],
}

impl<C: UChar> UStr<C> {
    /// Coerces a value into a [`UStr`]
    #[inline]
    pub fn new<S: AsRef<Self> + ?Sized>(s: &S) -> &Self {
        s.as_ref()
    }

    /// Constructs a [`UStr`] from a pointer and a length
    ///
    /// The `len` argument is the number of elements, **not** the number of bytes. No copying or
    /// allocation is performed, the resulting value is a direct reference to the pointer bytes.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements.
    ///
    /// In addition, the data must meet the safety conditions of [std::slice::from_raw_parts].
    /// In particular, the returned string reference *must not be mutated* for the duration of
    /// lifetime `'a`, except inside an [`UnsafeCell`][std::cell::UnsafeCell].
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
    pub unsafe fn from_ptr<'a>(p: *const C, len: usize) -> &'a Self {
        assert!(!p.is_null());
        let slice: *const [C] = slice::from_raw_parts(p, len);
        &*(slice as *const UStr<C>)
    }

    /// Constructs a mutable [`UStr`] from a mutable pointer and a length
    ///
    /// The `len` argument is the number of elements, **not** the number of bytes. No copying or
    /// allocation is performed, the resulting value is a direct reference to the pointer bytes.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements.
    ///
    /// In addition, the data must meet the safety conditions of [std::slice::from_raw_parts_mut].
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
    pub unsafe fn from_ptr_mut<'a>(p: *mut C, len: usize) -> &'a mut Self {
        assert!(!p.is_null());
        let slice: *mut [C] = slice::from_raw_parts_mut(p, len);
        &mut *(slice as *mut UStr<C>)
    }

    /// Constructs a [`UStr`] from a slice of character data
    ///
    /// No checks are performed on the slice. It may or may not be valid for its encoding.
    #[inline]
    pub fn from_slice(slice: &[C]) -> &Self {
        let ptr: *const [C] = slice;
        unsafe { &*(ptr as *const UStr<C>) }
    }

    /// Constructs a mutable [`UStr`] from a mutable slice of character data
    ///
    /// No checks are performed on the slice. It may or may not be valid for its encoding.
    #[inline]
    pub fn from_slice_mut(slice: &mut [C]) -> &mut Self {
        let ptr: *mut [C] = slice;
        unsafe { &mut *(ptr as *mut UStr<C>) }
    }

    /// Copies the string reference to a new owned [`UString`][crate::UString]
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    #[inline]
    pub fn to_ustring(&self) -> crate::UString<C> {
        crate::UString::from_vec(&self.inner)
    }

    /// Converts to a slice of the string
    #[inline]
    pub fn as_slice(&self) -> &[C] {
        &self.inner
    }

    /// Converts to a mutable slice of the string
    pub fn as_mut_slice(&mut self) -> &mut [C] {
        &mut self.inner
    }

    /// Returns a raw pointer to the string
    ///
    /// The caller must ensure that the string outlives the pointer this function returns, or else
    /// it will end up pointing to garbage.
    ///
    /// The caller must also ensure that the memory the pointer (non-transitively) points to is
    /// never written to (except inside an `UnsafeCell`) using this pointer or any pointer derived
    /// from it. If you need to mutate the contents of the string, use
    /// [`as_mut_ptr`][Self::as_mut_ptr].
    ///
    /// Modifying the container referenced by this string may cause its buffer to be reallocated,
    /// which would also make any pointers to it invalid.
    #[inline]
    pub fn as_ptr(&self) -> *const C {
        self.inner.as_ptr()
    }

    /// Returns an unsafe mutable raw pointer to the string
    ///
    /// The caller must ensure that the string outlives the pointer this function returns, or else
    /// it will end up pointing to garbage.
    ///
    /// Modifying the container referenced by this string may cause its buffer to be reallocated,
    /// which would also make any pointers to it invalid.
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut C {
        self.inner.as_mut_ptr()
    }

    /// Returns the length of the string as number of elements (**not** number of bytes)
    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns whether this string contains no data
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Converts a [`Box<UStr>`] into a [`UString`][crate::UString] without copying or allocating
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    pub fn into_ustring(self: Box<Self>) -> crate::UString<C> {
        let boxed = unsafe { Box::from_raw(Box::into_raw(self) as *mut [C]) };
        crate::UString {
            inner: boxed.into_vec(),
        }
    }

    /// Returns an object that implements [`Display`][std::fmt::Display] for printing strings that
    /// may contain non-Unicode data
    ///
    /// A [`UStr`] might contain ill-formed UTF encoding. This struct implements the
    /// [`Display`][std::fmt::Display] trait in a way that decoding the string is lossy but no heap
    /// allocations are performed, such as by [`to_string_lossy`][UStr::to_string_lossy].
    ///
    /// By default, invalid Unicode data is replaced with
    /// [`U+FFFD REPLACEMENT CHARACTER`][std::char::REPLACEMENT_CHARACTER] (�). If you wish to simply
    /// skip any invalid Uncode data and forego the replacement, you may use the
    /// [alternate formatting][std::fmt#sign0] with `{:#}`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use widestring::U16Str;
    ///
    /// // 𝄞mus<invalid>ic<invalid>
    /// let s = U16Str::from_slice(&[
    ///     0xD834, 0xDD1E, 0x006d, 0x0075, 0x0073, 0xDD1E, 0x0069, 0x0063, 0xD834,
    /// ]);
    ///
    /// assert_eq!(format!("{}", s.display()),
    /// "𝄞mus�ic�"
    /// );
    /// ```
    ///
    /// Using alternate formatting style to skip invalid values entirely:
    ///
    /// ```
    /// use widestring::U16Str;
    ///
    /// // 𝄞mus<invalid>ic<invalid>
    /// let s = U16Str::from_slice(&[
    ///     0xD834, 0xDD1E, 0x006d, 0x0075, 0x0073, 0xDD1E, 0x0069, 0x0063, 0xD834,
    /// ]);
    ///
    /// assert_eq!(format!("{:#}", s.display()),
    /// "𝄞music"
    /// );
    /// ```
    #[inline]
    pub fn display(&self) -> Display<'_, C> {
        Display { str: self }
    }
}

impl UStr<u16> {
    /// Decodes a string reference to an owned [`OsString`][std::ffi::OsString]
    ///
    /// This makes a string copy of the [`U16Str`]. Since [`U16Str`] makes no guarantees that it is
    /// valid UTF-16, there is no guarantee that the resulting [`OsString`][std::ffi::OsString] will
    /// be valid encoding either.
    ///
    /// Note that the encoding of [`OsString`][std::ffi::OsString] is platform-dependent, so on
    /// some platforms this may make an encoding conversions, while on other platforms (such as
    /// windows) no changes to the string will be made.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U16String;
    /// use std::ffi::OsString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wstr = U16String::from_str(s);
    /// // Create an OsString from the wide string
    /// let osstr = wstr.to_os_string();
    ///
    /// assert_eq!(osstr, OsString::from(s));
    /// ```
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    #[inline]
    pub fn to_os_string(&self) -> std::ffi::OsString {
        crate::platform::os_from_wide(&self.inner)
    }

    /// Decodes the string reference to a [`String`] if it contains valid UTF-16 data.
    ///
    /// # Failures
    ///
    /// Returns an error if the string contains any invalid UTF-16 data.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U16String;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wstr = U16String::from_str(s);
    /// // Create a regular string from the wide string
    /// let s2 = wstr.to_string().unwrap();
    ///
    /// assert_eq!(s2, s);
    /// ```
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    #[inline]
    pub fn to_string(&self) -> Result<String, FromUtf16Error> {
        String::from_utf16(&self.inner)
    }

    /// Decodes the string reference to a [`String`] even if it is invalid UTF-16 data
    ///
    /// Any non-Unicode sequences are replaced with `U+FFFD REPLACEMENT CHARACTER`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U16String;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wstr = U16String::from_str(s);
    /// // Create a regular string from the wide string
    /// let lossy = wstr.to_string_lossy();
    ///
    /// assert_eq!(lossy, s);
    /// ```
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    #[inline]
    pub fn to_string_lossy(&self) -> String {
        String::from_utf16_lossy(&self.inner)
    }
}

impl UStr<u32> {
    /// Constructs a [`U32Str`] from a [`char`][prim@char] pointer and a length
    ///
    /// The `len` argument is the number of `char` elements, **not** the number of bytes. No copying
    /// or allocation is performed, the resulting value is a direct reference to the pointer bytes.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements.
    ///
    /// In addition, the data must meet the safety conditions of [std::slice::from_raw_parts].
    /// In particular, the returned string reference *must not be mutated* for the duration of
    /// lifetime `'a`, except inside an [`UnsafeCell`][std::cell::UnsafeCell].
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
    pub unsafe fn from_char_ptr<'a>(p: *const char, len: usize) -> &'a Self {
        Self::from_ptr(p as *const u32, len)
    }

    /// Constructs a mutable [`U32Str`] from a mutable [`char`][prim@char] pointer and a length
    ///
    /// The `len` argument is the number of `char` elements, **not** the number of bytes. No copying
    /// or allocation is performed, the resulting value is a direct reference to the pointer bytes.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements.
    ///
    /// In addition, the data must meet the safety conditions of [std::slice::from_raw_parts_mut].
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
    pub unsafe fn from_char_ptr_mut<'a>(p: *mut char, len: usize) -> &'a mut Self {
        Self::from_ptr_mut(p as *mut u32, len)
    }

    /// Constructs a [`U32Str`] from a [`char`][prim@char] slice
    ///
    /// No checks are performed on the slice.
    #[inline]
    pub fn from_char_slice(slice: &[char]) -> &Self {
        let ptr: *const [char] = slice;
        unsafe { &*(ptr as *const Self) }
    }

    /// Constructs a mutable [`U32Str`] from a mutable [`char`][prim@char] slice
    ///
    /// No checks are performed on the slice.
    #[inline]
    pub fn from_char_slice_mut(slice: &mut [char]) -> &mut Self {
        let ptr: *mut [char] = slice;
        unsafe { &mut *(ptr as *mut Self) }
    }

    /// Decodes a string to an owned [`OsString`][std::ffi::OsString]
    ///
    /// This makes a string copy of the [`U32Str`]. Since [`U32Str`] makes no guarantees that it is
    /// valid UTF-32, there is no guarantee that the resulting [`OsString`][std::ffi::OsString] will
    /// be valid data.
    ///
    /// Note that the encoding of [`OsString`][std::ffi::OsString] is platform-dependent, so on
    /// some platforms this may make an encoding conversions, while on other platforms no changes to
    /// the string will be made.
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
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    #[inline]
    pub fn to_os_string(&self) -> std::ffi::OsString {
        self.to_string_lossy().into()
    }

    /// Decodes the string to a [`String`] if it contains valid UTF-32 data.
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
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    pub fn to_string(&self) -> Result<String, crate::FromUtf32Error> {
        let chars: Vec<Option<char>> = self.inner.iter().map(|c| char::from_u32(*c)).collect();
        if chars.iter().any(|c| c.is_none()) {
            return Err(crate::FromUtf32Error::new());
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

    /// Decodes the string reference to a [`String`] even if it is invalid UTF-32 data
    ///
    /// Any non-Unicode sequences are replaced with `U+FFFD REPLACEMENT CHARACTER`.
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
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    pub fn to_string_lossy(&self) -> String {
        let chars: Vec<char> = self
            .inner
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
}

impl core::fmt::Debug for U16Str {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        crate::debug_fmt_u16(self.as_slice(), f)
    }
}

impl core::fmt::Debug for U32Str {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        crate::debug_fmt_u32(self.as_slice(), f)
    }
}

/// String slice reference for [`U16String`][crate::U16String]
///
/// [`U16Str`] is to [`U16String`][crate::U16String] as [`str`] is to [`String`].
///
/// [`U16Str`] is not aware of null values. Strings may or may not be null-terminated, and may
/// contain invalid and ill-formed UTF-16 data. These strings are intended to be used with
/// FFI functions that directly use string length, where the strings are known to have proper
/// null-termination already, or where strings are merely being passed through without modification.
///
/// [`U16CStr`][crate::U16CStr] should be used instead of null-aware strings are required.
///
/// [`U16Str`] can be converted to many other string types, including
/// [`OsString`][std::ffi::OsString] and [`String`], making proper Unicode FFI safe and easy.
pub type U16Str = UStr<u16>;

/// String slice reference for [`U32String`][crate::U32String]
///
/// [`U32Str`] is to [`U32String`][crate::U32String] as [`str`] is to [`String`].
///
/// [`U32Str`] is not aware of null values. Strings may or may not be null-terminated, and may
/// contain invalid and ill-formed UTF-32 data. These strings are intended to be used with
/// FFI functions that directly use string length, where the strings are known to have proper
/// null-termination already, or where strings are merely being passed through without modification.
///
/// [`U32CStr`][crate::U32CStr] should be used instead of nul-aware strings are required.
///
/// [`U32Str`] can be converted to many other string types, including
/// [`OsString`][std::ffi::OsString] and [`String`], making proper Unicode FFI safe and easy.
pub type U32Str = UStr<u32>;

/// Alias for [`U16Str`] or [`U32Str`] depending on platform. Intended to match typical C `wchar_t`
/// size on platform.
pub type WideStr = UStr<WideChar>;

/// Helper struct for printing [`UStr`] values with [`format!`] and `{}`
///
/// A [`UStr`] might contain ill-formed UTF encoding. This struct implements the
/// [`Display`][std::fmt::Display] trait in a way that decoding the string is lossy but no heap
/// allocations are performed, such as by [`to_string_lossy`][UStr::to_string_lossy]. It is created
/// by the [`display`][UStr::display] method on [`UStr`].
///
/// By default, invalid Unicode data is replaced with
/// [`U+FFFD REPLACEMENT CHARACTER`][std::char::REPLACEMENT_CHARACTER] (�). If you wish to simply
/// skip any invalid Uncode data and forego the replacement, you may use the
/// [alternate formatting][std::fmt#sign0] with `{:#}`.
pub struct Display<'a, C: UChar> {
    str: &'a UStr<C>,
}

impl<'a> core::fmt::Debug for Display<'a, u16> {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Debug::fmt(&self.str, f)
    }
}

impl<'a> core::fmt::Debug for Display<'a, u32> {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Debug::fmt(&self.str, f)
    }
}

impl<'a> core::fmt::Display for Display<'a, u16> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        for c in crate::decode_utf16_lossy(self.str.as_slice().iter().copied()) {
            // Allow alternate {:#} format which skips replacment chars entirely
            if c != core::char::REPLACEMENT_CHARACTER || !f.alternate() {
                f.write_char(c)?;
            }
        }
        Ok(())
    }
}

impl<'a> core::fmt::Display for Display<'a, u32> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        for c in crate::decode_utf32_lossy(self.str.as_slice().iter().copied()) {
            // Allow alternate {:#} format which skips replacment chars entirely
            if c != core::char::REPLACEMENT_CHARACTER || !f.alternate() {
                f.write_char(c)?;
            }
        }
        Ok(())
    }
}
