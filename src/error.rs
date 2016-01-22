use std;

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