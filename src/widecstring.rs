use std;

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

/// An error returned from `WideCString` to indicate that a nul unit was found in the vector
/// provided.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NulError(usize, Vec<u16>);

impl NulError {
    /// Returns the position of the nul unit in the slice that was provided to `WideCString`.
    pub fn nul_position(&self) -> usize {
        self.0
    }

    /// Consumes this error, returning the underlying vector of u16 units which generated the error
    /// in the first place.
    pub fn into_vec(self) -> Vec<u16> {
        self.1
    }
}

impl WideCString {
    /// Constructs a new empty `WideCString` with only the trailing nul.
    pub fn new() -> WideCString {
        WideCString { inner: vec![0] }
    }

    /// Constructs a `WideCString` from a container of UTF-16 units.
    ///
    /// This method will consume the provided data and use the underlying units to construct a new
    /// string, ensuring that there is a trailing 0 value.
    ///
    /// # Errors
    ///
    /// This function will return an error if the units yielded contain an internal 0 (nul) value.
    /// The error returned will contain the `Vec<u16>` as well as the position of the nul unit.
    pub fn from_vec<T: Into<Vec<u16>>>(v: T) -> Result<WideCString, NulError> {
        let mut vals = v.into();
        // Check for nul vals
        match vals.iter().position(|&val| val == 0) {
            None => {
                // No nuls, but we need to add a nul at the end
                vals.push(0);
                Ok(WideCString { inner: vals })
            }
            // It's valid to have nul at end, but otherwise, an error
            Some(pos) if pos == vals.len() - 1 => Ok(WideCString { inner: vals }),
            Some(pos) => Err(NulError(pos, vals)),
        }
    }

    /// Creates a `WideCString` from a vector without checking for interior 0 values.
    ///
    /// This method is equivalent to `from_vec` except that no runtime assertion is made that `v`
    /// contains no 0 bytes, and it requires an actual vector, not anything that can be converted to
    /// one with `Into<Vec<u16>>`. Additionally, it does *not* ensure for a trailing 0 value.
    pub unsafe fn from_vec_unchecked(v: Vec<u16>) -> WideCString {
        WideCString { inner: v }
    }
}

impl std::fmt::Display for NulError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "nul unit found at position {}", self.0)
    }
}

impl std::error::Error for NulError {
    fn description(&self) -> &str {
        "nul unit found"
    }
}
