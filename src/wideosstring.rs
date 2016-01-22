
/// Owned, mutable Wide OS strings.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct WideOsString {
    inner: Vec<u16>
}

/// Slices into Wide OS strings.
#[derive(Debug)]
pub struct WideOsStr {
    inner: [u16]
}

impl WideOsString {
    /// Constructs a new empty `WideOsString`.
    pub fn new() -> WideOsString {
        WideOsString {
            inner: vec![]
        }
    }
}