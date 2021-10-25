macro_rules! implement_utf16_macro {
    ($(#[$m:meta])* $name:ident $extra_len:literal $str:ident $fn:ident) => {
        $(#[$m])*
        #[macro_export]
        macro_rules! $name {
            ($text:expr) => {{
                const _WIDESTRING_U16_MACRO_UTF8: &$crate::internals::core::primitive::str = $text;
                const _WIDESTRING_U16_MACRO_LEN: $crate::internals::core::primitive::usize =
                    $crate::internals::length_as_utf16(_WIDESTRING_U16_MACRO_UTF8) + $extra_len;
                const _WIDESTRING_U16_MACRO_UTF16: [$crate::internals::core::primitive::u16;
                        _WIDESTRING_U16_MACRO_LEN] = {
                    let mut buffer = [0u16; _WIDESTRING_U16_MACRO_LEN];
                    let mut bytes = _WIDESTRING_U16_MACRO_UTF8.as_bytes();
                    let mut i = 0;
                    while let Some((ch, rest)) = $crate::internals::next_code_point(bytes) {
                        bytes = rest;
                        // https://doc.rust-lang.org/std/primitive.char.html#method.encode_utf16
                        if ch & 0xFFFF == ch {
                            buffer[i] = ch as $crate::internals::core::primitive::u16;
                            i += 1;
                        } else {
                            let code = ch - 0x1_0000;
                            buffer[i] = 0xD800 | ((code >> 10) as $crate::internals::core::primitive::u16);
                            buffer[i + 1] = 0xDC00 | ((code as $crate::internals::core::primitive::u16) & 0x3FF);
                            i += 2;
                        }
                    }
                    buffer
                };
                #[allow(unused_unsafe)]
                unsafe { $crate::$str::$fn(&_WIDESTRING_U16_MACRO_UTF16) }
            }};
        }
    }
}

implement_utf16_macro! {
    /// Converts a string literal into a `const` UTF-16 string slice of type
    /// [`U16Str`][crate::U16Str].
    ///
    /// The resulting `const` string slice will always be valid UTF-16.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "alloc")] {
    /// use widestring::{u16str, U16Str, U16String};
    ///
    /// const STRING: &U16Str = u16str!("My string");
    /// assert_eq!(U16String::from_str("My string"), STRING);
    /// # }
    /// ```
    u16str 0 U16Str from_slice
}

implement_utf16_macro! {
    /// Converts a string literal into a `const` UTF-16 string slice of type
    /// [`U16CStr`][crate::U16CStr].
    ///
    /// The resulting `const` string slice will always be valid UTF-16 and include a nul terminator.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "alloc")] {
    /// use widestring::{u16cstr, U16CStr, U16CString};
    ///
    /// const STRING: &U16CStr = u16cstr!("My string");
    /// assert_eq!(U16CString::from_str("My string").unwrap(), STRING);
    /// # }
    /// ```
    u16cstr 1 U16CStr from_slice_unchecked
}

macro_rules! implement_utf32_macro {
    ($(#[$m:meta])* $name:ident $extra_len:literal $str:ident $fn:ident) => {
        $(#[$m])*
        #[macro_export]
        macro_rules! $name {
            ($text:expr) => {{
                const _WIDESTRING_U32_MACRO_UTF8: &$crate::internals::core::primitive::str = $text;
                const _WIDESTRING_U32_MACRO_LEN: $crate::internals::core::primitive::usize =
                    $crate::internals::length_as_utf32(_WIDESTRING_U32_MACRO_UTF8) + $extra_len;
                const _WIDESTRING_U32_MACRO_UTF16: [$crate::internals::core::primitive::u32;
                        _WIDESTRING_U32_MACRO_LEN] = {
                    let mut buffer = [0u32; _WIDESTRING_U32_MACRO_LEN];
                    let mut bytes = _WIDESTRING_U32_MACRO_UTF8.as_bytes();
                    let mut i = 0;
                    while let Some((ch, rest)) = $crate::internals::next_code_point(bytes) {
                        bytes = rest;
                        buffer[i] = ch;
                        i += 1;
                    }
                    buffer
                };
                #[allow(unused_unsafe)]
                unsafe { $crate::$str::$fn(&_WIDESTRING_U32_MACRO_UTF16) }
            }};
        }
    }
}

implement_utf32_macro! {
    /// Converts a string literal into a `const` UTF-32 string slice of type
    /// [`U32Str`][crate::U32Str].
    ///
    /// The resulting `const` string slice will always be valid UTF-32.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "alloc")] {
    /// use widestring::{u32str, U32Str, U32String};
    ///
    /// const STRING: &U32Str = u32str!("My string");
    /// assert_eq!(U32String::from_str("My string"), STRING);
    /// # }
    /// ```
    u32str 0 U32Str from_slice
}

implement_utf32_macro! {
    /// Converts a string literal into a `const` UTF-32 string slice of type
    /// [`U32CStr`][crate::U32CStr].
    ///
    /// The resulting `const` string slice will always be valid UTF-32 and include a nul terminator.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "alloc")] {
    /// use widestring::{u32cstr, U32CStr, U32CString};
    ///
    /// const STRING: &U32CStr = u32cstr!("My string");
    /// assert_eq!(U32CString::from_str("My string").unwrap(), STRING);
    /// # }
    /// ```
    u32cstr 1 U32CStr from_slice_unchecked
}

/// Alias for [`u16str`] or [`u32str`] macros depending on platform. Intended to be used when using
/// [`WideStr`][crate::WideStr] type alias.
#[cfg(not(windows))]
#[macro_export]
macro_rules! widestr {
    ($text:expr) => {{
        use $crate::*;
        u32str!($text)
    }};
}

/// Alias for [`u16cstr`] or [`u32cstr`] macros depending on platform. Intended to be used when
/// using [`WideCStr`][crate::WideCStr] type alias.
#[cfg(not(windows))]
#[macro_export]
macro_rules! widecstr {
    ($text:expr) => {{
        use $crate::*;
        u32cstr!($text)
    }};
}

/// Alias for [`u16str`] or [`u32str`] macros depending on platform. Intended to be used when using
/// [`WideStr`][crate::WideStr] type alias.
#[cfg(windows)]
#[macro_export]
macro_rules! widestr {
    ($text:expr) => {{
        use $crate::*;
        u16str!($text)
    }};
}

/// Alias for [`u16cstr`] or [`u32cstr`] macros depending on platform. Intended to be used when
/// using [`WideCStr`][crate::WideCStr] type alias.
#[cfg(windows)]
#[macro_export]
macro_rules! widecstr {
    ($text:expr) => {{
        use $crate::*;
        u16cstr!($text)
    }};
}

#[doc(hidden)]
pub mod internals {
    pub use core;

    // A const implementation of https://github.com/rust-lang/rust/blob/d902752866cbbdb331e3cf28ff6bba86ab0f6c62/library/core/src/str/mod.rs#L509-L537
    // Assumes `utf8` is a valid &str
    pub const fn next_code_point(utf8: &[u8]) -> Option<(u32, &[u8])> {
        const CONT_MASK: u8 = 0b0011_1111;
        match utf8 {
            [one @ 0..=0b0111_1111, rest @ ..] => Some((*one as u32, rest)),
            [one @ 0b1100_0000..=0b1101_1111, two, rest @ ..] => Some((
                (((*one & 0b0001_1111) as u32) << 6) | ((*two & CONT_MASK) as u32),
                rest,
            )),
            [one @ 0b1110_0000..=0b1110_1111, two, three, rest @ ..] => Some((
                (((*one & 0b0000_1111) as u32) << 12)
                    | (((*two & CONT_MASK) as u32) << 6)
                    | ((*three & CONT_MASK) as u32),
                rest,
            )),
            [one, two, three, four, rest @ ..] => Some((
                (((*one & 0b0000_0111) as u32) << 18)
                    | (((*two & CONT_MASK) as u32) << 12)
                    | (((*three & CONT_MASK) as u32) << 6)
                    | ((*four & CONT_MASK) as u32),
                rest,
            )),
            [..] => None,
        }
    }

    // A const implementation of `s.chars().map(|ch| ch.len_utf16()).sum()`
    pub const fn length_as_utf16(s: &str) -> usize {
        let mut bytes = s.as_bytes();
        let mut len = 0;
        while let Some((ch, rest)) = next_code_point(bytes) {
            bytes = rest;
            len += if (ch & 0xFFFF) == ch { 1 } else { 2 };
        }
        len
    }

    // A const implementation of `s.chars().len()`
    pub const fn length_as_utf32(s: &str) -> usize {
        let mut bytes = s.as_bytes();
        let mut len = 0;
        while let Some((_, rest)) = next_code_point(bytes) {
            bytes = rest;
            len += 1;
        }
        len
    }
}

#[cfg(all(test, feature = "alloc"))]
mod test {
    use crate::{
        U16CStr, U16Str, U16String, U32CStr, U32Str, U32String, WideCStr, WideStr, WideString,
    };

    const U16STR_TEST: &U16Str = u16str!("TEST STR");
    const U16CSTR_TEST: &U16CStr = u16cstr!("TEST STR");
    const U32STR_TEST: &U32Str = u32str!("TEST STR");
    const U32CSTR_TEST: &U32CStr = u32cstr!("TEST STR");
    const WIDESTR_TEST: &WideStr = widestr!("TEST STR");
    const WIDECSTR_TEST: &WideCStr = widecstr!("TEST STR");

    #[test]
    fn str_macros() {
        let str = U16String::from_str("TEST STR");
        assert_eq!(&str, U16STR_TEST);
        assert_eq!(&str, U16CSTR_TEST);
        assert!(matches!(U16CSTR_TEST.as_slice_with_nul().last(), Some(&0)));

        let str = U32String::from_str("TEST STR");
        assert_eq!(&str, U32STR_TEST);
        assert_eq!(&str, U32CSTR_TEST);
        assert!(matches!(U32CSTR_TEST.as_slice_with_nul().last(), Some(&0)));

        let str = WideString::from_str("TEST STR");
        assert_eq!(&str, WIDESTR_TEST);
        assert_eq!(&str, WIDECSTR_TEST);
        assert!(matches!(WIDECSTR_TEST.as_slice_with_nul().last(), Some(&0)));
    }
}
