//! A wide string FFI module for converting to and from wide string variants.
//!
//! This module provides multiple types of wide strings: [`U16String`], [`U16CString`],
//! [`U32String`], and [`U32CString`]. These types are backed by two generic implementations
//! parameterized by element size: [`UString<C>`] and [`UCString<C>`]. The `UCString` types are
//! analogous to the standard [`CString`] FFI type, while the `UString` types are analogous to
//! [`OsString`]. Otherwise, `U16` and `U32` types differ only in character width.
//!
//! For [`U16String`] and [`U32String`], no guarantees are made about the underlying string data;
//! they are simply a sequence of UTF-16 *code units* or UTF-32 code points, both of which may be
//! ill-formed or contain null values. [`U16CString`] and [`U32CString`], on the other hand, are
//! aware of null values and are guaranteed to be terminated with a null value (unless unchecked
//! methods are used to construct the strings). Because [`U16CString`] and [`U32CString`] are
//! C-style, null-terminated strings, they will have no interior null values. All four string types
//! may still have unpaired UTF-16 surrogates or invalid UTF-32 code points; ill-formed data is
//! preserved until conversion to a basic Rust [`String`].
//!
//! Use [`U16String`] or [`U32String`] when you simply need to pass-through strings, or when you
//! know or don't care if you're not dealing with a null-terminated string, such as when string
//! lengths are provided and you are only reading strings from FFI, not writing them out to a FFI.
//!
//! Use [`U16CString`] or [`U32CString`] when you must properly handle null values, and must deal
//! with null-terminated C-style wide strings, such as when you pass strings into FFI functions.
//!
//! # Relationship to other Rust Strings
//!
//! Standard Rust strings [`String`] and [`str`] are well-formed Unicode data encoded as UTF-8. The
//! standard strings provide proper handling of Unicode and ensure strong safety guarantees.
//!
//! [`CString`] and [`CStr`] are strings used for C FFI. They handle null-terminated C-style
//! strings. However, they do not have a builtin encoding, and  conversions between C-style and
//! other Rust strings must specifically encode and decode the strings, and handle possibly invalid
//! encoding data. They are safe to use only in passing string-like data back and forth from C APIs
//! but do not provide any other guarantees, so may not be well-formed.
//!
//! [`OsString`] and [`OsStr`] are also strings for use with FFI. Unlike [`CString`], they do no
//! special handling of null values, but instead have an OS-specified encoding. While, for example,
//! on Linux systems this is usually the UTF-8 encoding, this is not the case for every platform.
//! The encoding may not even be 8-bit: on Windows, [`OsString`] uses a malformed encoding sometimes
//! referred to as "WTF-8". In any case, like [`CString`], [`OsString`] has no additional guarantees
//! and may not be well-formed.
//!
//! Due to the loss of safety of these other string types, conversion to standard Rust [`String`] is
//! lossy, and may require knowledge of the underlying encoding, including platform-specific
//! quirks.
//!
//! The wide strings in this crate are roughly based on the principles of the string types in
//! [`std::ffi`], though there are differences. [`U16String`], [`U32String`], [`U16Str`], and
//! [`U32Str`] are roughly similar in role to [`OsString`] and [`OsStr`], while [`U16CString`],
//! [`U32CString`], [`U16CStr`], and [`U32CStr`] are roughly similar in role to [`CString`] and
//! [`CStr`]. Conversion to FFI string types is generally very straight forward and safe, while
//! conversion directly between standard Rust [`String`] is a lossy conversion just as [`OsString`]
//! is.
//!
//! [`U16String`] and [`U16CString`] are treated as though they use UTF-16 encoding, even if they
//! may contain unpaired surrogates. [`U32String`] and [`U32CString`] are treated as though they use
//! UTF-32 encoding, even if they may contain values outside the valid Unicode character range.
//!
//! # Remarks on UTF-16 Code Units
//!
//! *Code units* are the 16-bit units that comprise UTF-16 sequences. Code units
//! can specify Unicode code points either as single units or in *surrogate pairs*. Because every
//! code unit might be part of a surrogate pair, many regular string operations, including
//! indexing into a wide string, writing to a wide string, or even iterating a wide string should
//! be handled with care and are greatly discouraged. Some operations have safer alternatives
//! provided, such as Unicode code point iteration instead of code unit iteration. Always keep in
//! mind that the number of code units (`len()`) of a wide string is **not** equivalent to the
//! number of Unicode characters in the string, merely the length of the UTF-16 encoding sequence.
//! In fact, Unicode code points do not even have a one-to-one mapping with characters!
//!
//! UTF-32 simply encodes Unicode code points as-is in 32-bit values, but Unicode character code
//! points are reserved only for 21-bits. Again, Unicode code points do not have a one-to-one
//! mapping with the concept of a visual character glyph.
//!
//! # FFI with C/C++ `wchar_t`
//!
//! C/C++'s `wchar_t` (and C++'s corresponding `widestring`) varies in size depending on compiler
//! and platform. Typically, `wchar_t` is 16-bits on Windows and 32-bits on most Unix-based
//! platforms. For convenience when using `wchar_t`-based FFI's, type aliases for the corresponding
//! string types are provided: [`WideString`] aliases [`U16String`] on Windows or [`U32String`]
//! elsewhere, [`WideCString`] aliases [`U16CString`] or [`U32CString`], etc. The [`WideChar`] alias
//! is also provided, aliasing [`u16`] or [`u32`].
//!
//! When not interacting with a FFI using `wchar_t`, it is recommended to use the string types
//! directly rather than via the wide alias.
//!
//! This crate supports `no_std` when default features are disabled. The `std` and `alloc` features
//! (enabled by default) enable the [`U16String`], [`U32String`], [`U16CString`], and [`U32CString`]
//! types and aliases. Other types do not require allocation and can be used in a `no_std`
//! environment.
//!
//! # Null values
//!
//! This crate uses the term "null" to refer to Unicode code point `U+0000` and its associated code
//! unit representation as zero-value bytes. This is also sometimes known as "nul" (with one 'l').
//! C-style strings end in a null value, while regular Rust strings allow interior null values and
//! are not terminated in null.
//!
//! # Examples
//!
//! The following example uses [`U16String`] to get Windows error messages, since `FormatMessageW`
//! returns a string length for us and we don't need to pass error messages into other FFI
//! functions so we don't need to worry about null values.
//!
//! ```rust
//! # #[cfg(any(not(windows), not(feature = "alloc")))]
//! # fn main() {}
//! # extern crate winapi;
//! # extern crate widestring;
//! # #[cfg(all(windows, feature = "alloc"))]
//! # fn main() {
//! use winapi::um::winbase::{FormatMessageW, LocalFree, FORMAT_MESSAGE_FROM_SYSTEM,
//!                           FORMAT_MESSAGE_ALLOCATE_BUFFER, FORMAT_MESSAGE_IGNORE_INSERTS};
//! use winapi::shared::ntdef::LPWSTR;
//! use winapi::shared::minwindef::HLOCAL;
//! use std::ptr;
//! use widestring::U16String;
//! # use winapi::shared::minwindef::DWORD;
//! # let error_code: DWORD = 0;
//!
//! let s: U16String;
//! unsafe {
//!     // First, get a string buffer from some windows api such as FormatMessageW...
//!     let mut buffer: LPWSTR = ptr::null_mut();
//!     let strlen = FormatMessageW(FORMAT_MESSAGE_FROM_SYSTEM |
//!                                 FORMAT_MESSAGE_ALLOCATE_BUFFER |
//!                                 FORMAT_MESSAGE_IGNORE_INSERTS,
//!                                 ptr::null(),
//!                                 error_code, // error code from GetLastError()
//!                                 0,
//!                                 (&mut buffer as *mut LPWSTR) as LPWSTR,
//!                                 0,
//!                                 ptr::null_mut());
//!
//!     // Get the buffer as a wide string
//!     s = U16String::from_ptr(buffer, strlen as usize);
//!     // Since U16String creates an owned copy, it's safe to free original buffer now
//!     // If you didn't want an owned copy, you could use &U16Str.
//!     LocalFree(buffer as HLOCAL);
//! }
//! // Convert to a regular Rust String and use it to your heart's desire!
//! let message = s.to_string_lossy();
//! # assert_eq!(message, "The operation completed successfully.\r\n");
//! # }
//! ```
//!
//! The following example is the functionally the same, only using [`U16CString`] instead.
//!
//! ```rust
//! # #[cfg(any(not(windows), not(feature = "alloc")))]
//! # fn main() {}
//! # extern crate winapi;
//! # extern crate widestring;
//! # #[cfg(all(windows, feature = "alloc"))]
//! # fn main() {
//! use winapi::um::winbase::{FormatMessageW, LocalFree, FORMAT_MESSAGE_FROM_SYSTEM,
//!                           FORMAT_MESSAGE_ALLOCATE_BUFFER, FORMAT_MESSAGE_IGNORE_INSERTS};
//! use winapi::shared::ntdef::LPWSTR;
//! use winapi::shared::minwindef::HLOCAL;
//! use std::ptr;
//! use widestring::U16CString;
//! # use winapi::shared::minwindef::DWORD;
//! # let error_code: DWORD = 0;
//!
//! let s: U16CString;
//! unsafe {
//!     // First, get a string buffer from some windows api such as FormatMessageW...
//!     let mut buffer: LPWSTR = ptr::null_mut();
//!     FormatMessageW(FORMAT_MESSAGE_FROM_SYSTEM |
//!                    FORMAT_MESSAGE_ALLOCATE_BUFFER |
//!                    FORMAT_MESSAGE_IGNORE_INSERTS,
//!                    ptr::null(),
//!                    error_code, // error code from GetLastError()
//!                    0,
//!                    (&mut buffer as *mut LPWSTR) as LPWSTR,
//!                    0,
//!                    ptr::null_mut());
//!
//!     // Get the buffer as a wide string
//!     s = U16CString::from_ptr_str(buffer);
//!     // Since U16CString creates an owned copy, it's safe to free original buffer now
//!     // If you didn't want an owned copy, you could use &U16CStr.
//!     LocalFree(buffer as HLOCAL);
//! }
//! // Convert to a regular Rust String and use it to your heart's desire!
//! let message = s.to_string_lossy();
//! # assert_eq!(message, "The operation completed successfully.\r\n");
//! # }
//! ```
//!
//! [`OsString`]: std::ffi::OsString
//! [`OsStr`]: std::ffi::OsStr
//! [`CString`]: std::ffi::CString
//! [`CStr`]: std::ffi::CStr

#![warn(
    missing_docs,
    missing_debug_implementations,
    trivial_casts,
    trivial_numeric_casts,
    future_incompatible
)]
#![cfg_attr(not(feature = "std"), no_std)]
#![doc(html_root_url = "https://docs.rs/widestring/")]
#![doc(test(attr(deny(warnings), allow(unused))))]
#![cfg_attr(docsrs, feature(doc_cfg))]

#[cfg(feature = "alloc")]
extern crate alloc;

pub mod error;
#[cfg(feature = "std")]
mod platform;
mod ucstr;
#[cfg(feature = "alloc")]
mod ucstring;
mod ustr;
#[cfg(feature = "alloc")]
mod ustring;

#[doc(no_inline)]
#[allow(deprecated)]
pub use error::{
    ContainsNull, FromUtf32Error, MissingNulError, MissingNullTerminator, NulError, NullError,
};
pub use ucstr::{U16CStr, U32CStr, UCStr, WideCStr};
#[cfg(feature = "alloc")]
pub use ucstring::*;
pub use ustr::*;
#[cfg(feature = "alloc")]
pub use ustring::*;

/// Marker trait for primitive types used to represent wide character data. Should not be used
/// directly.
pub trait UChar: core::fmt::Debug + Sized + Copy + Ord + Eq {
    /// NULL character value
    const NULL: Self;
    #[doc(hidden)]
    #[deprecated = "use `NULL` instead"]
    const NUL: Self;
}

impl UChar for u16 {
    const NULL: u16 = 0;
    #[doc(hidden)]
    const NUL: u16 = 0;
}

impl UChar for u32 {
    const NULL: u32 = 0;
    #[doc(hidden)]
    const NUL: u32 = 0;
}

#[cfg(not(windows))]
/// Alias for [`u16`] or [`u32`] depending on platform. Intended to match typical C `wchar_t` size
/// on platform.
pub type WideChar = u32;

#[cfg(windows)]
/// Alias for [`u16`] or [`u32`] depending on platform. Intended to match typical C `wchar_t` size
/// on platform.
pub type WideChar = u16;
