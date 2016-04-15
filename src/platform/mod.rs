#[cfg(windows)]
mod windows;

#[cfg(windows)]
pub use self::windows::*;

#[cfg(not(windows))]
mod other;

#[cfg(not(windows))]
pub use self::other::*;
