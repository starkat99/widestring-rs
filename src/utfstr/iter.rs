use super::{Utf16Str, Utf32Str};
use crate::{
    debug_fmt_char_iter, decode_utf16, decode_utf32,
    iter::{DecodeUtf16, DecodeUtf32},
};
use core::{
    fmt::Write,
    iter::{Copied, FlatMap, FusedIterator},
    slice::Iter,
};

/// An iterator over the [`char`]s of a string slice
///
/// This struct is created by the [`chars`][Utf16Str::chars] method on [`Utf16Str`]. See its
/// documentation for more.
#[derive(Clone)]
pub struct Utf16Chars<'a> {
    iter: DecodeUtf16<Copied<Iter<'a, u16>>>,
}

impl<'a> Utf16Chars<'a> {
    pub(super) fn new(s: &'a Utf16Str) -> Self {
        Self {
            iter: decode_utf16(s.as_slice().iter().copied()),
        }
    }
}

impl<'a> Iterator for Utf16Chars<'a> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // Utf16Str already ensures valid surrogate pairs
        self.iter.next().map(|r| r.unwrap())
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a> FusedIterator for Utf16Chars<'a> {}

impl<'a> core::fmt::Debug for Utf16Chars<'a> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        debug_fmt_char_iter(self.clone(), f)
    }
}

impl<'a> core::fmt::Display for Utf16Chars<'a> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.clone().try_for_each(|c| f.write_char(c))
    }
}

/// An iterator over the [`char`]s of a string slice
///
/// This struct is created by the [`chars`][Utf32Str::chars] method on [`Utf32Str`]. See its
/// documentation for more.
#[derive(Clone)]
pub struct Utf32Chars<'a> {
    iter: DecodeUtf32<Copied<Iter<'a, u32>>>,
}

impl<'a> Utf32Chars<'a> {
    pub(super) fn new(s: &'a Utf32Str) -> Self {
        Self {
            iter: decode_utf32(s.as_slice().iter().copied()),
        }
    }
}

impl<'a> Iterator for Utf32Chars<'a> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // Utf32Str already ensures valid code points
        self.iter.next().map(|r| r.unwrap())
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a> DoubleEndedIterator for Utf32Chars<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        // Utf32Str already ensures valid code points
        self.iter.next_back().map(|r| r.unwrap())
    }
}

impl<'a> FusedIterator for Utf32Chars<'a> {}

impl<'a> ExactSizeIterator for Utf32Chars<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<'a> core::fmt::Debug for Utf32Chars<'a> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        debug_fmt_char_iter(self.clone(), f)
    }
}

impl<'a> core::fmt::Display for Utf32Chars<'a> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.clone().try_for_each(|c| f.write_char(c))
    }
}

/// An iterator over the [`char`]s of a string slice, and their positions
///
/// This struct is created by the [`char_indices`][crate::Utf16Str::char_indices] method on
/// [`Utf16Str`][crate::Utf16Str] and [`Utf32Str`][crate::Utf32Str]. See its documentation for more.
#[derive(Debug, Clone)]
pub struct CharIndices<I> {
    offset: usize,
    iter: I,
}

impl<I> CharIndices<I> {
    /// Returns the byte position of the next character, or the length of the underlying string if
    /// there are no more characters.
    #[inline]
    pub fn offset(&self) -> usize {
        self.offset
    }
}

impl<'a> CharIndices<Utf16Chars<'a>> {
    pub(super) fn new(s: &'a Utf16Str) -> Self {
        Self {
            offset: 0,
            iter: Utf16Chars::new(s),
        }
    }
}

impl<'a> CharIndices<Utf32Chars<'a>> {
    pub(super) fn new(s: &'a Utf32Str) -> Self {
        Self {
            offset: 0,
            iter: Utf32Chars::new(s),
        }
    }
}

impl<I> Iterator for CharIndices<I>
where
    I: Iterator<Item = char>,
{
    type Item = (usize, char);

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.iter.next();
        if let Some(c) = result {
            let offset = self.offset;
            self.offset += c.len_utf16();
            Some((offset, c))
        } else {
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<I> FusedIterator for CharIndices<I> where I: Iterator<Item = char> {}

/// The return type of [`Utf16Str::escape_debug`][crate::Utf16Str::escape_debug].
#[derive(Debug, Clone)]
pub struct EscapeDebug<I> {
    iter: FlatMap<I, core::char::EscapeDebug, fn(char) -> core::char::EscapeDebug>,
}

impl<'a> EscapeDebug<Utf16Chars<'a>> {
    pub(super) fn new(s: &'a Utf16Str) -> Self {
        Self {
            iter: Utf16Chars::new(s).flat_map(|c| c.escape_debug()),
        }
    }
}

impl<'a> EscapeDebug<Utf32Chars<'a>> {
    pub(super) fn new(s: &'a Utf32Str) -> Self {
        Self {
            iter: Utf32Chars::new(s).flat_map(|c| c.escape_debug()),
        }
    }
}

/// The return type of [`Utf16Str::escape_default`][crate::Utf16Str::escape_default].
#[derive(Debug, Clone)]
pub struct EscapeDefault<I> {
    iter: FlatMap<I, core::char::EscapeDefault, fn(char) -> core::char::EscapeDefault>,
}

impl<'a> EscapeDefault<Utf16Chars<'a>> {
    pub(super) fn new(s: &'a Utf16Str) -> Self {
        Self {
            iter: Utf16Chars::new(s).flat_map(|c| c.escape_default()),
        }
    }
}

impl<'a> EscapeDefault<Utf32Chars<'a>> {
    pub(super) fn new(s: &'a Utf32Str) -> Self {
        Self {
            iter: Utf32Chars::new(s).flat_map(|c| c.escape_default()),
        }
    }
}

/// The return type of [`Utf16Str::escape_unicode`][crate::Utf16Str::escape_unicode].
#[derive(Debug, Clone)]
pub struct EscapeUnicode<I> {
    iter: FlatMap<I, core::char::EscapeUnicode, fn(char) -> core::char::EscapeUnicode>,
}

impl<'a> EscapeUnicode<Utf16Chars<'a>> {
    pub(super) fn new(s: &'a Utf16Str) -> Self {
        Self {
            iter: Utf16Chars::new(s).flat_map(|c| c.escape_unicode()),
        }
    }
}

impl<'a> EscapeUnicode<Utf32Chars<'a>> {
    pub(super) fn new(s: &'a Utf32Str) -> Self {
        Self {
            iter: Utf32Chars::new(s).flat_map(|c| c.escape_unicode()),
        }
    }
}

macro_rules! escape_impls {
    ($($name:ident),+) => {$(
        impl<I> core::fmt::Display for $name<I> where I: Iterator<Item = char> + Clone {
            #[inline]
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                self.clone().try_for_each(|c| f.write_char(c))
            }
        }

        impl< I> Iterator for $name<I> where I: Iterator<Item = char> {
            type Item = char;

            #[inline]
            fn next(&mut self) -> Option<Self::Item> {
                self.iter.next()
            }

            #[inline]
            fn size_hint(&self) -> (usize, Option<usize>) {
                self.iter.size_hint()
            }
        }

        impl<I> FusedIterator for $name<I> where I: Iterator<Item = char> {}
    )+}
}

escape_impls!(EscapeDebug, EscapeDefault, EscapeUnicode);
