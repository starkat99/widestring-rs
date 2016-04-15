#![cfg(windows)]

use std::ffi::{OsString, OsStr};
use std::os::windows::ffi::{OsStringExt, OsStrExt};

pub fn os_to_wide(s: &OsStr) -> Vec<u16> {
    s.encode_wide().collect()
}

pub fn os_from_wide(s: &[u16]) -> OsString {
    OsString::from_wide(s)
}
