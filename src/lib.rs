//! A wide string FFI library for converting to and from Windows Wide "Unicode" strings.

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

mod error;
mod wideosstring;

pub use error::NulError;
pub use wideosstring::{WideOsString, WideOsStr};
