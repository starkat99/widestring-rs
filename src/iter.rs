//! Iterators for working with wide strings

use crate::error::DecodeUtf32Error;
use core::char::DecodeUtf16;

/// An iterator that lossily decodes possibly ill-formed UTF-16 encoded code points from an iterator
/// of `u16`s
///
/// Any unpaired UTF-16 surrogate values are replaced by
/// [`U+FFFD REPLACEMENT_CHARACTER`][core::char::REPLACEMENT_CHARACTER] (�).
#[derive(Debug, Clone)]
pub struct DecodeUtf16Lossy<I>
where
    I: Iterator<Item = u16>,
{
    pub(crate) iter: DecodeUtf16<I>,
}

impl<I> Iterator for DecodeUtf16Lossy<I>
where
    I: Iterator<Item = u16>,
{
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .map(|res| res.unwrap_or(core::char::REPLACEMENT_CHARACTER))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// An iterator that decodes UTF-32 encoded code points from an iterator of `u32`s
#[derive(Debug, Clone)]
pub struct DecodeUtf32<I>
where
    I: Iterator<Item = u32>,
{
    pub(crate) iter: I,
}

impl<I> Iterator for DecodeUtf32<I>
where
    I: Iterator<Item = u32>,
{
    type Item = Result<char, DecodeUtf32Error>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .map(|u| core::char::from_u32(u).ok_or_else(|| DecodeUtf32Error::new(u)))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// An iterator that lossily decodes possibly ill-formed UTF-32 encoded code points from an iterator
/// of `u32`s
///
/// Any invalid UTF-32 values are replaced by
/// [`U+FFFD REPLACEMENT_CHARACTER`][core::char::REPLACEMENT_CHARACTER] (�).
#[derive(Debug, Clone)]
pub struct DecodeUtf32Lossy<I>
where
    I: Iterator<Item = u32>,
{
    pub(crate) iter: DecodeUtf32<I>,
}

impl<I> Iterator for DecodeUtf32Lossy<I>
where
    I: Iterator<Item = u32>,
{
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .map(|res| res.unwrap_or(core::char::REPLACEMENT_CHARACTER))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}
