/// A type representing an owned C-compatible wide string
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct WideCString {
    inner: Vec<u16>,
}

/// Representation of a borrowed C wide string.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct WideCStr {
    inner: [u16],
}

impl WideCString {
    /// Constructs a new empty `WideCString` with only the trailing nul.
    pub fn new() -> WideCString {
        WideCString { inner: vec![0] }
    }

    pub unsafe fn from_vec_unchecked(v: Vec<u16>) -> WideCString {
        WideCString { inner: v }
    }
}