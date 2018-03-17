use std::ffi::{OsStr, OsString};

pub fn os_to_wide(s: &OsStr) -> Vec<u16> {
    s.to_string_lossy().encode_utf16().collect()
}

pub fn os_from_wide(s: &[u16]) -> OsString {
    OsString::from(String::from_utf16_lossy(s))
}
