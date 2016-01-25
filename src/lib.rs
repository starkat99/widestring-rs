//! A wide string FFI library for converting to and from Windows Wide "Unicode" strings.
//!
//! This crate provides two types of wide strings: `WideString` and `WideCString`. They differ
//! in the guaruntees they provide. For `WideString`, no guaruntees are made about the underlying
//! string data; it is simply a sequence of UTF-16 values, which may be ill-formed or contain nul
//! values. `WideCString` on the other hand is aware of nul values and is guarunteed to be
//! terminated with a nul value (unless unchecked methods are used to construct the `WideCString`).
//! Because `WideCString` is a C-style, nul-terminated string, it will have no interior nul values.
//! A `WideCString` may still have ill-formed UTF-16 values.
//!
//! Use `WideString` when you simply need to pass-thru values, or when you know or don't care if
//! you're not dealing with a nul-terminated string, such as when string lengths are provided and
//! you are only reading strings from FFI, not passing them into FFI.
//!
//! Use `WideCString` when you must properly handle nul values, and must deal with nul-terminated
//! C-style wide strings, such as if you must pass string values into FFI functions.
//!
//! While these types are roughly based on the types in `std::os`, they are *not* an identical wide
//! version of `OsString` and `CString`, but do fill a similar, adjacent role.
//!
//! # Examples
//!
//! The following example uses `WideString` to get windows error messages, since `FormatMessageW`
//! returns a string length for us, and we don't need to pass error messages into other FFI
//! functions so we don't need to worry about nuls.
//!
//! ```rust
//! # extern crate winapi;
//! # extern crate kernel32;
//! # extern crate widestring;
//! use winapi::*;
//! use kernel32::{FormatMessageW, LocalFree};
//! use std::ptr;
//! use widestring::WideString;
//! # fn main() {
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
//! # extern crate winapi;
//! # extern crate kernel32;
//! # extern crate widestring;
//! use winapi::*;
//! use kernel32::{FormatMessageW, LocalFree};
//! use std::ptr;
//! use widestring::WideCString;
//! # fn main() {
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

#![warn(missing_docs,
        missing_copy_implementations,
        missing_debug_implementations,
        trivial_casts,
        trivial_numeric_casts,
        unstable_features,
        unused_extern_crates,
        unused_import_braces,
        unused_qualifications)]

// Confine crate to windows-only
#![cfg(target_os = "windows")]

mod widestring;
mod widecstring;

pub use widestring::{WideString, WideStr};
pub use widecstring::{WideCString, WideCStr, NulError, MissingNulError};
