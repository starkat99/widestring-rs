//! A wide string FFI library for converting to and from Wide "Unicode" strings.

#![warn(
        missing_docs, missing_copy_implementations, missing_debug_implementations, trivial_casts,
        trivial_numeric_casts, unstable_features, unused_extern_crates, unused_import_braces,
        unused_qualifications
)]

pub mod ffi;
mod platform;
