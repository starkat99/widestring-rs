#![cfg(windows)]

use std::ffi::{OsStr, OsString};
use std::os::windows::ffi::{OsStrExt, OsStringExt};

pub fn os_to_wide(s: &OsStr) -> Vec<u16> {
    s.encode_wide().collect()
}

pub fn os_from_wide(s: &[u16]) -> OsString {
    OsString::from_wide(s)
}
