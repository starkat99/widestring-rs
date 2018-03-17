//! A wide string FFI library for converting to and from Wide "Unicode" strings.
//!
//! This crate provides two types of wide strings: `WideString` and `WideCString`. They differ
//! in the guarantees they provide. For `WideString`, no guarantees are made about the underlying
//! string data; it is simply a sequence of UTF-16 *code units*, which may be ill-formed or
//! contain nul values. `WideCString` on the other hand is aware of nul values and is guaranteed to
//! be terminated with a nul value (unless unchecked methods are used to construct the
//! `WideCString`). Because `WideCString` is a C-style, nul-terminated string, it will have no
//! interior nul values. A `WideCString` may still have ill-formed UTF-16 code units.
//!
//! Use `WideString` when you simply need to pass-through strings, or when you know or don't care if
//! you're not dealing with a nul-terminated string, such as when string lengths are provided and
//! you are only reading strings from FFI, not passing them into FFI.
//!
//! Use `WideCString` when you must properly handle nul values, and must deal with nul-terminated
//! C-style wide strings, such as when you pass strings into FFI functions.
//!
//! # Relationship to other Rust Strings
//!
//! Standard Rust strings `String` and `str` are well-formed Unicode data encoded as UTF-8. The
//! standard strings provide proper handling of Unicode and ensure strong safety guarantees.
//!
//! `CString` and `CStr` are strings used for C FFI. They handle nul-terminated C-style strings.
//! However, they do not have a builtin encoding, and conversions between C-style and other Rust
//! strings must specifically encode and decode the strings, and handle possibly invalid encoding
//! data. They are safe to use only in passing string-like data back and forth from C APIs but do
//! not provide any other guarantees, so may not be well-formed.
//!
//! `OsString` and `OsStr` are also strings for use with FFI. Unlike `CString`, they do no special
//! handling of nul values, but instead have an OS-specified encoding. While, for example, on Linux
//! systems this is usually the UTF-8 encoding, this is not the case for every platform. The encoding
//! may not even be 8-bit: on Windows, `OsString` uses 16-bit values, but may not always be
//! valid UTF-16-encoded. Like `CString`, `OsString` has no additional
//! guarantees and may not be well-formed.
//!
//! Due to the loss of safety of these other string types, conversion to standard Rust `String` is
//! lossy, and may require knowledge of the underlying encoding, including platform-specific quirks.
//!
//! The wide strings in this crate are roughly based on the principles of the string types in
//! `std::ffi`, though there are differences. `WideString` and `WideStr` are roughly similar in role
//! to `OsString` and `OsStr`, while `WideCString` and `WideCStr` are roughly similar in role to
//! `CString` and `CStr`. In fact, on Windows, `WideString` is nearly identical to `OsString`. It
//! can be useful to ensure consistent wide character size across other platforms, and that's where
//! these wide string types come into play. Conversion to other string types is very straight
//! forward and safe, while conversion directly between standard Rust `String` is a lossy conversion
//! just as `OsString` is. Just as `OsString`, the wide strings are assumed to have some sort of
//! UTF-16 encoding, but that encoding may be ill-formed.
//!
//! # Remarks on Code Units
//!
//! *Code units* are the 16-bit units that comprise UTF-16 sequences. Code units
//! can specify Unicode code points either as single units or in *surrogate pairs*. Because every
//! code unit might be part of a surrogate pair, many regular string operations, including
//! indexing into a wide string, writing to a wide string, or even iterating a wide string should be
//! handled with care and are greatly discouraged. Some operations have safer alternatives provided,
//! such as Unicode code point iteration instead of code unit iteration. Always keep in mind that
//! the number of code units (`len()`) of a wide string is **not** equivalent to the
//! number of Unicode characters in the string, merely the length of the UTF-16 encoding sequence.
//! In fact, Unicode code points do not even have a one-to-one mapping with characters!
//!
//! # Examples
//!
//! The following example uses `WideString` to get Windows error messages, since `FormatMessageW`
//! returns a string length for us and we don't need to pass error messages into other FFI
//! functions so we don't need to worry about nul values.
//!
//! ```rust
//! # #[cfg(not(windows))]
//! # fn main() {}
//! # extern crate winapi;
//! # extern crate widestring;
//! # #[cfg(windows)]
//! # fn main() {
//! use winapi::um::winbase::{FormatMessageW, LocalFree, FORMAT_MESSAGE_FROM_SYSTEM,
//!                           FORMAT_MESSAGE_ALLOCATE_BUFFER, FORMAT_MESSAGE_IGNORE_INSERTS};
//! use winapi::shared::ntdef::LPWSTR;
//! use winapi::shared::minwindef::HLOCAL;
//! use std::ptr;
//! use widestring::WideString;
//! # use winapi::shared::minwindef::DWORD;
//! # let error_code: DWORD = 0;
//!
//! let widestr: WideString;
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
//!     widestr = WideString::from_ptr(buffer, strlen as usize);
//!     // Since WideString creates an owned copy, it's safe to free original buffer now
//!     // If you didn't want an owned copy, you could use &WideStr.
//!     LocalFree(buffer as HLOCAL);
//! }
//! // Convert to a regular Rust String and use it to your heart's desire!
//! let message = widestr.to_string_lossy();
//! # assert_eq!(message, "The operation completed successfully.\r\n");
//! # }
//! ```
//!
//! The following example is the functionally the same, only using `WideCString` instead.
//!
//! ```rust
//! # #[cfg(not(windows))]
//! # fn main() {}
//! # extern crate winapi;
//! # extern crate widestring;
//! # #[cfg(windows)]
//! # fn main() {
//! use winapi::um::winbase::{FormatMessageW, LocalFree, FORMAT_MESSAGE_FROM_SYSTEM,
//!                           FORMAT_MESSAGE_ALLOCATE_BUFFER, FORMAT_MESSAGE_IGNORE_INSERTS};
//! use winapi::shared::ntdef::LPWSTR;
//! use winapi::shared::minwindef::HLOCAL;
//! use std::ptr;
//! use widestring::WideCString;
//! # use winapi::shared::minwindef::DWORD;
//! # let error_code: DWORD = 0;
//!
//! let widestr: WideCString;
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
//!     widestr = WideCString::from_ptr_str(buffer);
//!     // Since WideCString creates an owned copy, it's safe to free original buffer now
//!     // If you didn't want an owned copy, you could use &WideCStr.
//!     LocalFree(buffer as HLOCAL);
//! }
//! // Convert to a regular Rust String and use it to your heart's desire!
//! let message = widestr.to_string_lossy();
//! # assert_eq!(message, "The operation completed successfully.\r\n");
//! # }
//! ```

#![warn(missing_docs, missing_copy_implementations, missing_debug_implementations, trivial_casts,
        trivial_numeric_casts, unstable_features, unused_extern_crates, unused_import_braces,
        unused_qualifications)]

mod widestring;
mod widecstring;
mod platform;

pub use widestring::{WideStr, WideString};
pub use widecstring::{MissingNulError, NulError, WideCStr, WideCString};
