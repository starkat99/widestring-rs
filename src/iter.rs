//! Iterators for working with wide string data.

use crate::{
    decode_utf16_surrogate_pair,
    error::{DecodeUtf16Error, DecodeUtf32Error},
    is_utf16_high_surrogate, is_utf16_low_surrogate, is_utf16_surrogate,
};
use core::{
    char,
    iter::{DoubleEndedIterator, ExactSizeIterator, FusedIterator},
};

/// An iterator that decodes UTF-16 encoded code points from an iterator of [`u16`]s.
///
/// This struct is created by [`decode_utf16`][crate::decode_utf16]. See its documentation for more.
///
/// This struct is identical to [`char::DecodeUtf16`] except it is a [`DoubleEndedIterator`] if
/// `I` is.
#[derive(Debug, Clone)]
pub struct DecodeUtf16<I>
where
    I: Iterator<Item = u16>,
{
    iter: I,
    forward_buf: Option<u16>,
    back_buf: Option<u16>,
}

impl<I> DecodeUtf16<I>
where
    I: Iterator<Item = u16>,
{
    pub(crate) fn new(iter: I) -> Self {
        Self {
            iter,
            forward_buf: None,
            back_buf: None,
        }
    }
}

impl<I> Iterator for DecodeUtf16<I>
where
    I: Iterator<Item = u16>,
{
    type Item = Result<char, DecodeUtf16Error>;

    fn next(&mut self) -> Option<Self::Item> {
        // Copied from char::DecodeUtf16
        let u = match self.forward_buf.take() {
            Some(buf) => buf,
            None => self.iter.next().or_else(|| self.back_buf.take())?,
        };

        if !is_utf16_surrogate(u) {
            // SAFETY: not a surrogate
            Some(Ok(unsafe { char::from_u32_unchecked(u as u32) }))
        } else if is_utf16_low_surrogate(u) {
            // a trailing surrogate
            Some(Err(DecodeUtf16Error::new(u)))
        } else {
            let u2 = match self.iter.next().or_else(|| self.back_buf.take()) {
                Some(u2) => u2,
                // eof
                None => return Some(Err(DecodeUtf16Error::new(u))),
            };
            if !is_utf16_low_surrogate(u2) {
                // not a trailing surrogate so we're not a valid
                // surrogate pair, so rewind to redecode u2 next time.
                self.forward_buf = Some(u2);
                return Some(Err(DecodeUtf16Error::new(u)));
            }

            // all ok, so lets decode it.
            // SAFETY: verified the surrogate pair
            unsafe { Some(Ok(decode_utf16_surrogate_pair(u, u2))) }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (low, high) = self.iter.size_hint();
        // we could be entirely valid surrogates (2 elements per
        // char), or entirely non-surrogates (1 element per char)
        (low / 2, high)
    }
}

impl<I> DoubleEndedIterator for DecodeUtf16<I>
where
    I: Iterator<Item = u16> + DoubleEndedIterator,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        let u2 = match self.back_buf.take() {
            Some(buf) => buf,
            None => self.iter.next_back().or_else(|| self.forward_buf.take())?,
        };

        if !is_utf16_surrogate(u2) {
            // SAFETY: not a surrogate
            Some(Ok(unsafe { char::from_u32_unchecked(u2 as u32) }))
        } else if is_utf16_high_surrogate(u2) {
            // a leading surrogate
            Some(Err(DecodeUtf16Error::new(u2)))
        } else {
            let u = match self.iter.next_back().or_else(|| self.forward_buf.take()) {
                Some(u) => u,
                // eof
                None => return Some(Err(DecodeUtf16Error::new(u2))),
            };
            if !is_utf16_high_surrogate(u) {
                // not a leading surrogate so we're not a valid
                // surrogate pair, so rewind to redecode u next time.
                self.back_buf = Some(u);
                return Some(Err(DecodeUtf16Error::new(u2)));
            }

            // all ok, so lets decode it.
            // SAFETY: verified the surrogate pair
            unsafe { Some(Ok(decode_utf16_surrogate_pair(u, u2))) }
        }
    }
}

impl<I> FusedIterator for DecodeUtf16<I> where I: Iterator<Item = u16> + FusedIterator {}

/// An iterator that lossily decodes possibly ill-formed UTF-16 encoded code points from an iterator
/// of [`u16`]s.
///
/// Any unpaired UTF-16 surrogate values are replaced by
/// [`U+FFFD REPLACEMENT_CHARACTER`][char::REPLACEMENT_CHARACTER] (�).
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
            .map(|res| res.unwrap_or(char::REPLACEMENT_CHARACTER))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<I> DoubleEndedIterator for DecodeUtf16Lossy<I>
where
    I: Iterator<Item = u16> + DoubleEndedIterator,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter
            .next_back()
            .map(|res| res.unwrap_or(char::REPLACEMENT_CHARACTER))
    }
}

impl<I> FusedIterator for DecodeUtf16Lossy<I> where I: Iterator<Item = u16> + FusedIterator {}

/// An iterator that decodes UTF-32 encoded code points from an iterator of `u32`s.
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
            .map(|u| char::from_u32(u).ok_or_else(|| DecodeUtf32Error::new(u)))
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<I> DoubleEndedIterator for DecodeUtf32<I>
where
    I: Iterator<Item = u32> + DoubleEndedIterator,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter
            .next_back()
            .map(|u| char::from_u32(u).ok_or_else(|| DecodeUtf32Error::new(u)))
    }
}

impl<I> FusedIterator for DecodeUtf32<I> where I: Iterator<Item = u32> + FusedIterator {}

impl<I> ExactSizeIterator for DecodeUtf32<I>
where
    I: Iterator<Item = u32> + ExactSizeIterator,
{
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}

/// An iterator that lossily decodes possibly ill-formed UTF-32 encoded code points from an iterator
/// of `u32`s.
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

impl<I> DoubleEndedIterator for DecodeUtf32Lossy<I>
where
    I: Iterator<Item = u32> + DoubleEndedIterator,
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter
            .next_back()
            .map(|res| res.unwrap_or(core::char::REPLACEMENT_CHARACTER))
    }
}

impl<I> FusedIterator for DecodeUtf32Lossy<I> where I: Iterator<Item = u32> + FusedIterator {}

impl<I> ExactSizeIterator for DecodeUtf32Lossy<I>
where
    I: Iterator<Item = u32> + ExactSizeIterator,
{
    #[inline]
    fn len(&self) -> usize {
        self.iter.len()
    }
}
