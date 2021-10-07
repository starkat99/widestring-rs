//! Errors returned by functions in this crate

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

/// An error returned to indicate a problem with null values occurred
///
/// The error will either being a [`MissingNullTerminator`] or [`ContainsNull`].
/// The error optionally returns the ownership of the invalid vector whenever a vector was owned.
#[derive(Debug, Clone)]
pub enum NullError<C> {
    /// A terminating null value was missing
    MissingNullTerminator(MissingNullTerminator),
    /// An interior null value was found
    ContainsNull(ContainsNull<C>),
}

impl<C> NullError<C> {
    /// Consumes this error, returning the underlying vector of values which generated the error in
    /// the first place
    #[inline]
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    pub fn into_vec(self) -> Option<Vec<C>> {
        match self {
            Self::MissingNullTerminator(_) => None,
            Self::ContainsNull(e) => e.into_vec(),
        }
    }
}

impl<C> core::fmt::Display for NullError<C> {
    #[inline]
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match self {
            Self::MissingNullTerminator(e) => e.fmt(f),
            Self::ContainsNull(e) => e.fmt(f),
        }
    }
}

#[cfg(feature = "std")]
impl<C: crate::UChar + 'static> std::error::Error for NullError<C> {
    #[inline]
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::MissingNullTerminator(e) => Some(e),
            Self::ContainsNull(e) => Some(e),
        }
    }
}

impl<C> From<MissingNullTerminator> for NullError<C> {
    #[inline]
    fn from(value: MissingNullTerminator) -> Self {
        Self::MissingNullTerminator(value)
    }
}

impl<C> From<ContainsNull<C>> for NullError<C> {
    #[inline]
    fn from(value: ContainsNull<C>) -> Self {
        Self::ContainsNull(value)
    }
}

/// An error returned from to indicate that a terminating null value was missing
#[derive(Debug, Clone)]
pub struct MissingNullTerminator;

impl core::fmt::Display for MissingNullTerminator {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "missing terminating null value")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for MissingNullTerminator {}

/// An error returned to indicate that an invalid null value was found in a string
///
/// The error indicates the position in the vector where the null value was found, as well as
/// returning the ownership of the invalid vector.
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
#[derive(Debug, Clone)]
pub struct ContainsNull<C> {
    index: usize,
    #[cfg(feature = "alloc")]
    pub(crate) inner: Option<Vec<C>>,
    #[cfg(not(feature = "alloc"))]
    _p: core::marker::PhantomData<C>,
}

impl<C> ContainsNull<C> {
    #[cfg(feature = "alloc")]
    pub(crate) fn new(index: usize, v: Vec<C>) -> Self {
        Self {
            index,
            inner: Some(v),
        }
    }

    #[cfg(feature = "alloc")]
    pub(crate) fn empty(index: usize) -> Self {
        Self { index, inner: None }
    }

    #[cfg(not(feature = "alloc"))]
    pub(crate) fn empty(index: usize) -> Self {
        Self {
            index,
            _p: core::marker::PhantomData,
        }
    }

    /// Returns the index of the invalid null value in the slice
    #[inline]
    pub fn null_index(&self) -> usize {
        self.index
    }

    #[doc(hidden)]
    #[deprecated = "use `null_index` instead"]
    pub fn nul_position(&self) -> usize {
        self.null_index()
    }

    /// Consumes this error, returning the underlying vector of values which generated the error in
    /// the first place
    #[inline]
    #[cfg(feature = "alloc")]
    #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    pub fn into_vec(self) -> Option<Vec<C>> {
        self.inner
    }
}

impl<C> core::fmt::Display for ContainsNull<C> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "invalid null value found at position {}", self.index)
    }
}

#[cfg(feature = "std")]
impl<C: crate::UChar> std::error::Error for ContainsNull<C> {}

/// A possible error value when converting a [`String`] from a [`u32`] string
///
/// This error occurs when a [`u32`] value is outside the 21-bit Unicode code point range
/// (>`U+10FFFF`) or is a UTF-16 surrogate value.
#[derive(Debug, Clone)]
pub struct FromUtf32Error;

impl core::fmt::Display for FromUtf32Error {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(
            f,
            "error converting from UTF-32 to UTF-8, the UTF-32 value is invalid"
        )
    }
}

#[cfg(feature = "std")]
impl std::error::Error for FromUtf32Error {}

/// An error that can be returned when decoding UTF-32 code points
///
/// This error occurs when a [`u32`] value is outside the 21-bit Unicode code point range
/// (>`U+10FFFF`) or is a UTF-16 surrogate value.
#[derive(Debug, Clone)]
pub struct DecodeUtf32Error {
    code: u32,
}

impl DecodeUtf32Error {
    pub(crate) fn new(code: u32) -> Self {
        Self { code }
    }

    /// Returns the invalid code point value which caused the error
    pub fn invalid_code_point(&self) -> u32 {
        self.code
    }
}

impl core::fmt::Display for DecodeUtf32Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "invalid UTF-32 code point: {:x}", self.code)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for DecodeUtf32Error {}

#[doc(hidden)]
#[deprecated = "use `ContainsNull` instead"]
pub type NulError<C> = ContainsNull<C>;

#[doc(hidden)]
#[deprecated = "use `MissingNullTerminator` instead"]
pub type MissingNulError = MissingNullTerminator;
