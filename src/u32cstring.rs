use super::{FromUtf32Error, U32Str, U32String};
use std;
use std::char;
use std::ffi::{OsStr, OsString};
use std::mem;

/// An owned, mutable C-style wide string for FFI that is nul-aware and nul-terminated.
///
/// `U32CString` is aware of nul values. Unless unchecked conversions are used, all `U32CString`
/// strings end with a nul-terminator in the underlying buffer and contain no internal nul values.
/// The strings may still contain invalid or ill-formed UTF-32 data. These strings are intended to
/// be used with FFI functions such as Windows API that may require nul-terminated strings.
///
/// `U32CString` can be converted to and from many other string types, including `U32String`,
/// `OsString`, and `String`, making proper Unicode FFI safe and easy.
///
/// # Examples
///
/// The following example constructs a `U32CString` and shows how to convert a `U32CString` to a
/// regular Rust `String`.
///
/// ```rust
/// use widestring::U32CString;
/// let s = "Test";
/// // Create a wide string from the rust string
/// let wstr = U32CString::from_str(s).unwrap();
/// // Convert back to a rust string
/// let rust_str = wstr.to_string_lossy();
/// assert_eq!(rust_str, "Test");
/// ```
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct U32CString {
    inner: Box<[u32]>,
}

/// C-style wide string reference for `U32CString`.
///
/// `U32CStr` is aware of nul values. Unless unchecked conversions are used, all `U32CStr`
/// strings end with a nul-terminator in the underlying buffer and contain no internal nul values.
/// The strings may still contain invalid or ill-formed UTF-32 data. These strings are intended to
/// be used with FFI functions such as Windows API that may require nul-terminated strings.
///
/// `U32CStr` can be converted to and from many other string types, including `U32String`,
/// `OsString`, and `String`, making proper Unicode FFI safe and easy.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct U32CStr {
    inner: [u32],
}

/// An error returned from `U32CString` to indicate that an invalid nul value was found.
///
/// The error indicates the position in the vector where the nul value was found, as well as
/// returning the ownership of the invalid vector.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct U32NulError(usize, Vec<u32>);

/// An error returned from `U32CString` and `U32CStr` to indicate that a terminating nul value
/// was missing.
///
/// The error optionally returns the ownership of the invalid vector whenever a vector was owned.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MissingU32NulError(Option<Vec<u32>>);

impl U32CString {
    /// Constructs a `U32CString` from a container of wide character data.
    ///
    /// This method will consume the provided data and use the underlying elements to construct a
    /// new string. The data will be scanned for invalid nul values.
    ///
    /// # Failures
    ///
    /// This function will return an error if the data contains a nul value.
    /// The returned error will contain the `Vec<u32>` as well as the position of the nul value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let v = vec![84u32, 104u32, 101u32]; // 'T' 'h' 'e'
    /// # let cloned = v.clone();
    /// // Create a wide string from the vector
    /// let wcstr = U32CString::new(v).unwrap();
    /// # assert_eq!(wcstr.into_vec(), cloned);
    /// ```
    ///
    /// The following example demonstrates errors from nul values in a vector.
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let v = vec![84u32, 0u32, 104u32, 101u32]; // 'T' NUL 'h' 'e'
    /// // Create a wide string from the vector
    /// let res = U32CString::new(v);
    /// assert!(res.is_err());
    /// assert_eq!(res.err().unwrap().nul_position(), 1);
    /// ```
    pub fn new(v: impl Into<Vec<u32>>) -> Result<U32CString, U32NulError> {
        let v = v.into();
        // Check for nul vals
        match v.iter().position(|&val| val == 0) {
            None => Ok(unsafe { U32CString::from_vec_unchecked(v) }),
            Some(pos) => Err(U32NulError(pos, v)),
        }
    }

    /// Constructs a `U32CString` from a nul-terminated container of UTF-32 data.
    ///
    /// This method will consume the provided data and use the underlying elements to construct a
    /// new string. The string will be truncated at the first nul value in the string.
    ///
    /// # Failures
    ///
    /// This function will return an error if the data does not contain a nul to terminate the
    /// string. The returned error will contain the consumed `Vec<u32>`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let v = vec![84u32, 104u32, 101u32, 0u32]; // 'T' 'h' 'e' NUL
    /// # let cloned = v[..3].to_owned();
    /// // Create a wide string from the vector
    /// let wcstr = U32CString::from_vec_with_nul(v).unwrap();
    /// # assert_eq!(wcstr.into_vec(), cloned);
    /// ```
    ///
    /// The following example demonstrates errors from missing nul values in a vector.
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let v = vec![84u32, 104u32, 101u32]; // 'T' 'h' 'e'
    /// // Create a wide string from the vector
    /// let res = U32CString::from_vec_with_nul(v);
    /// assert!(res.is_err());
    /// ```
    pub fn from_vec_with_nul(v: impl Into<Vec<u32>>) -> Result<U32CString, MissingU32NulError> {
        let mut v = v.into();
        // Check for nul vals
        match v.iter().position(|&val| val == 0) {
            None => Err(MissingU32NulError(Some(v))),
            Some(pos) => {
                v.truncate(pos + 1);
                Ok(unsafe { U32CString::from_vec_with_nul_unchecked(v) })
            }
        }
    }

    /// Creates a `U32CString` from a vector without checking for interior nul values.
    ///
    /// A terminating nul value will be appended if the vector does not already have a terminating
    /// nul.
    ///
    /// # Safety
    ///
    /// This method is equivalent to `new` except that no runtime assertion is made that `v`
    /// contains no nul values. Providing a vector with nul values will result in an invalid
    /// `U32CString`.
    pub unsafe fn from_vec_unchecked(v: impl Into<Vec<u32>>) -> U32CString {
        let mut v = v.into();
        match v.last() {
            None => v.push(0),
            Some(&c) if c != 0 => v.push(0),
            Some(_) => (),
        }
        U32CString::from_vec_with_nul_unchecked(v)
    }

    /// Creates a `U32CString` from a vector that should have a nul terminator, without checking
    /// for any nul values.
    ///
    /// # Safety
    ///
    /// This method is equivalent to `from_vec_with_nul` except that no runtime assertion is made
    /// that `v` contains no nul values. Providing a vector with interior nul values or without a
    /// terminating nul value will result in an invalid `U32CString`.
    pub unsafe fn from_vec_with_nul_unchecked(v: impl Into<Vec<u32>>) -> U32CString {
        U32CString {
            inner: v.into().into_boxed_slice(),
        }
    }

    /// Constructs a `U32CString` from a container of wide character data.
    ///
    /// This method will consume the provided data and use the underlying elements to construct a
    /// new string. The data will be scanned for invalid nul values.
    ///
    /// # Failures
    ///
    /// This function will return an error if the data contains a nul value.
    /// The returned error will contain the `Vec<u32>` as well as the position of the nul value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let v: Vec<char> = "Test".chars().collect();
    /// # let cloned: Vec<u32> = v.iter().map(|&c| c as u32).collect();
    /// // Create a wide string from the vector
    /// let wcstr = U32CString::from_chars(v).unwrap();
    /// # assert_eq!(wcstr.into_vec(), cloned);
    /// ```
    ///
    /// The following example demonstrates errors from nul values in a vector.
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let v: Vec<char> = "T\u{0}est".chars().collect();
    /// // Create a wide string from the vector
    /// let res = U32CString::from_chars(v);
    /// assert!(res.is_err());
    /// assert_eq!(res.err().unwrap().nul_position(), 1);
    /// ```
    pub fn from_chars(v: impl Into<Vec<char>>) -> Result<U32CString, U32NulError> {
        let v: Vec<u32> = unsafe { mem::transmute(v.into()) };
        U32CString::new(v)
    }

    /// Constructs a `U32CString` from a nul-terminated container of UTF-32 data.
    ///
    /// This method will consume the provided data and use the underlying elements to construct a
    /// new string. The string will be truncated at the first nul value in the string.
    ///
    /// # Failures
    ///
    /// This function will return an error if the data does not contain a nul to terminate the
    /// string. The returned error will contain the consumed `Vec<u32>`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let v: Vec<char> = "Test\u{0}".chars().collect();
    /// # let cloned: Vec<u32> = v[..4].iter().map(|&c| c as u32).collect();
    /// // Create a wide string from the vector
    /// let wcstr = U32CString::from_chars_with_nul(v).unwrap();
    /// # assert_eq!(wcstr.into_vec(), cloned);
    /// ```
    ///
    /// The following example demonstrates errors from missing nul values in a vector.
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let v: Vec<char> = "Test".chars().collect();
    /// // Create a wide string from the vector
    /// let res = U32CString::from_chars_with_nul(v);
    /// assert!(res.is_err());
    /// ```
    pub fn from_chars_with_nul(v: impl Into<Vec<char>>) -> Result<U32CString, MissingU32NulError> {
        let v: Vec<u32> = unsafe { mem::transmute(v.into()) };
        U32CString::from_vec_with_nul(v)
    }

    /// Creates a `U32CString` from a vector without checking for interior nul values.
    ///
    /// A terminating nul value will be appended if the vector does not already have a terminating
    /// nul.
    ///
    /// # Safety
    ///
    /// This method is equivalent to `new` except that no runtime assertion is made that `v`
    /// contains no nul values. Providing a vector with nul values will result in an invalid
    /// `U32CString`.
    pub unsafe fn from_chars_unchecked(v: impl Into<Vec<char>>) -> U32CString {
        let v: Vec<u32> = mem::transmute(v.into());
        U32CString::from_vec_unchecked(v)
    }

    /// Creates a `U32CString` from a vector that should have a nul terminator, without checking
    /// for any nul values.
    ///
    /// # Safety
    ///
    /// This method is equivalent to `from_vec_with_nul` except that no runtime assertion is made
    /// that `v` contains no nul values. Providing a vector with interior nul values or without a
    /// terminating nul value will result in an invalid `U32CString`.
    pub unsafe fn from_chars_with_nul_unchecked(v: impl Into<Vec<char>>) -> U32CString {
        let v: Vec<u32> = mem::transmute(v.into());
        U32CString::from_vec_with_nul_unchecked(v)
    }

    /// Constructs a `U32CString` from a `str`.
    ///
    /// The string will be scanned for invalid nul values.
    ///
    /// # Failures
    ///
    /// This function will return an error if the data contains a nul value.
    /// The returned error will contain a `Vec<u32>` as well as the position of the nul value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wcstr = U32CString::from_str(s).unwrap();
    /// # assert_eq!(wcstr.to_string_lossy(), s);
    /// ```
    ///
    /// The following example demonstrates errors from nul values in a vector.
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let s = "My\u{0}String";
    /// // Create a wide string from the string
    /// let res = U32CString::from_str(s);
    /// assert!(res.is_err());
    /// assert_eq!(res.err().unwrap().nul_position(), 2);
    /// ```
    pub fn from_str(s: impl AsRef<str>) -> Result<U32CString, U32NulError> {
        let v: Vec<char> = s.as_ref().chars().collect();
        U32CString::from_chars(v)
    }

    /// Constructs a `U32CString` from a `str`, without checking for interior nul values.
    ///
    /// # Safety
    ///
    /// This method is equivalent to `from_str` except that no runtime assertion is made that `s`
    /// contains no nul values. Providing a string with nul values will result in an invalid
    /// `U32CString`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wcstr = unsafe { U32CString::from_str_unchecked(s) };
    /// # assert_eq!(wcstr.to_string_lossy(), s);
    /// ```
    pub unsafe fn from_str_unchecked(s: impl AsRef<str>) -> U32CString {
        let v: Vec<char> = s.as_ref().chars().collect();
        U32CString::from_chars_unchecked(v)
    }

    /// Constructs a `U32CString` from a `str` with a nul terminator.
    ///
    /// The string will be truncated at the first nul value in the string.
    ///
    /// # Failures
    ///
    /// This function will return an error if the data does not contain a nul to terminate the
    /// string. The returned error will contain the consumed `Vec<u32>`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let s = "My\u{0}String";
    /// // Create a wide string from the string
    /// let wcstr = U32CString::from_str_with_nul(s).unwrap();
    /// assert_eq!(wcstr.to_string_lossy(), "My");
    /// ```
    ///
    /// The following example demonstrates errors from missing nul values in a vector.
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let res = U32CString::from_str_with_nul(s);
    /// assert!(res.is_err());
    /// ```
    pub fn from_str_with_nul(s: impl AsRef<str>) -> Result<U32CString, MissingU32NulError> {
        let v: Vec<char> = s.as_ref().chars().collect();
        U32CString::from_chars_with_nul(v)
    }

    /// Constructs a `U32CString` from a `str` that should have a terminating nul, but without
    /// checking for any nul values.
    ///
    /// # Safety
    ///
    /// This method is equivalent to `from_str_with_nul` except that no runtime assertion is made
    /// that `s` contains no nul values. Providing a vector with interior nul values or without a
    /// terminating nul value will result in an invalid `U32CString`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let s = "My String\u{0}";
    /// // Create a wide string from the string
    /// let wcstr = unsafe { U32CString::from_str_with_nul_unchecked(s) };
    /// assert_eq!(wcstr.to_string_lossy(), "My String");
    /// ```
    pub unsafe fn from_str_with_nul_unchecked(s: impl AsRef<str>) -> U32CString {
        let v: Vec<char> = s.as_ref().chars().collect();
        U32CString::from_chars_with_nul_unchecked(v)
    }

    /// Constructs a `U32CString` from anything that can be converted to an `OsStr`.
    ///
    /// The string will be scanned for invalid nul values.
    ///
    /// # Failures
    ///
    /// This function will return an error if the data contains a nul value.
    /// The returned error will contain a `Vec<u16>` as well as the position of the nul value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wcstr = U32CString::from_os_str(s).unwrap();
    /// # assert_eq!(wcstr.to_string_lossy(), s);
    /// ```
    ///
    /// The following example demonstrates errors from nul values in a vector.
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let s = "My\u{0}String";
    /// // Create a wide string from the string
    /// let res = U32CString::from_os_str(s);
    /// assert!(res.is_err());
    /// assert_eq!(res.err().unwrap().nul_position(), 2);
    /// ```
    pub fn from_os_str(s: impl AsRef<OsStr>) -> Result<U32CString, U32NulError> {
        let v: Vec<char> = s.as_ref().to_string_lossy().chars().collect();
        U32CString::from_chars(v)
    }

    /// Constructs a `U32CString` from anything that can be converted to an `OsStr`, without
    /// checking for interior nul values.
    ///
    /// # Safety
    ///
    /// This method is equivalent to `from_os_str` except that no runtime assertion is made that
    /// `s` contains no nul values. Providing a string with nul values will result in an invalid
    /// `U32CString`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wcstr = unsafe { U32CString::from_os_str_unchecked(s) };
    /// # assert_eq!(wcstr.to_string_lossy(), s);
    /// ```
    pub unsafe fn from_os_str_unchecked(s: impl AsRef<OsStr>) -> U32CString {
        let v: Vec<char> = s.as_ref().to_string_lossy().chars().collect();
        U32CString::from_chars_unchecked(v)
    }

    /// Constructs a `U32CString` from anything that can be converted to an `OsStr` with a nul
    /// terminator.
    ///
    /// The string will be truncated at the first nul value in the string.
    ///
    /// # Failures
    ///
    /// This function will return an error if the data does not contain a nul to terminate the
    /// string. The returned error will contain the consumed `Vec<u16>`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let s = "My\u{0}String";
    /// // Create a wide string from the string
    /// let wcstr = U32CString::from_os_str_with_nul(s).unwrap();
    /// assert_eq!(wcstr.to_string_lossy(), "My");
    /// ```
    ///
    /// The following example demonstrates errors from missing nul values in a vector.
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let res = U32CString::from_os_str_with_nul(s);
    /// assert!(res.is_err());
    /// ```
    pub fn from_os_str_with_nul(s: impl AsRef<OsStr>) -> Result<U32CString, MissingU32NulError> {
        let v: Vec<char> = s.as_ref().to_string_lossy().chars().collect();
        U32CString::from_chars_with_nul(v)
    }

    /// Constructs a `U32CString` from anything that can be converted to an `OsStr` that should
    /// have a terminating nul, but without checking for any nul values.
    ///
    /// # Safety
    ///
    /// This method is equivalent to `from_os_str_with_nul` except that no runtime assertion is
    /// made that `s` contains no nul values. Providing a vector with interior nul values or
    /// without a terminating nul value will result in an invalid `U32CString`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let s = "My String\u{0}";
    /// // Create a wide string from the string
    /// let wcstr = unsafe { U32CString::from_os_str_with_nul_unchecked(s) };
    /// assert_eq!(wcstr.to_string_lossy(), "My String");
    /// ```
    pub unsafe fn from_os_str_with_nul_unchecked(s: impl AsRef<OsStr>) -> U32CString {
        let v: Vec<char> = s.as_ref().to_string_lossy().chars().collect();
        U32CString::from_chars_with_nul_unchecked(v)
    }

    /// Constructs a `U32CString` from anything that can be converted to a `U32Str`.
    ///
    /// The string will be scanned for invalid nul values.
    ///
    /// # Failures
    ///
    /// This function will return an error if the data contains a nul value.
    /// The returned error will contain a `Vec<u32>` as well as the position of the nul value.
    pub fn from_u32_str(s: impl AsRef<U32Str>) -> Result<U32CString, U32NulError> {
        U32CString::new(s.as_ref().as_slice())
    }

    /// Constructs a `U32CString` from anything that can be converted to a `U32Str`, without
    /// scanning for invalid nul values.
    ///
    /// # Safety
    ///
    /// This method is equivalent to `from_u32_str` except that no runtime assertion is made that
    /// `s` contains no nul values. Providing a string with nul values will result in an invalid
    /// `U32CString`.
    pub unsafe fn from_u32_str_unchecked(s: impl AsRef<U32Str>) -> U32CString {
        U32CString::from_vec_unchecked(s.as_ref().as_slice())
    }

    /// Constructs a `U32CString` from anything that can be converted to a `U32Str` with a nul
    /// terminator.
    ///
    /// The string will be truncated at the first nul value in the string.
    ///
    /// # Failures
    ///
    /// This function will return an error if the data does not contain a nul to terminate the
    /// string. The returned error will contain the consumed `Vec<u16>`.
    pub fn from_u32_str_with_nul(s: impl AsRef<U32Str>) -> Result<U32CString, MissingU32NulError> {
        U32CString::from_vec_with_nul(s.as_ref().as_slice())
    }

    /// Constructs a `U32CString` from anything that can be converted to a `U32Str` with a nul
    /// terminator, without checking the string for any invalid interior nul values.
    ///
    /// # Safety
    ///
    /// This method is equivalent to `from_u32_str_with_nul` except that no runtime assertion is
    /// made that `s` contains no nul values. Providing a vector with interior nul values or
    /// without a terminating nul value will result in an invalid `U32CString`.
    pub unsafe fn from_u32_str_with_nul_unchecked(s: impl AsRef<U32Str>) -> U32CString {
        U32CString::from_vec_with_nul_unchecked(s.as_ref().as_slice())
    }

    /// Constructs a new `U32CString` copied from a `u32` nul-terminated string pointer.
    ///
    /// This will scan for nul values beginning with `p`. The first nul value will be used as the
    /// nul terminator for the string, similar to how libc string functions such as `strlen` work.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid or has a
    /// nul terminator, and the function could scan past the underlying buffer.
    ///
    /// `p` must be non-null.
    ///
    /// # Panics
    ///
    /// This function panics if `p` is null.
    ///
    /// # Caveat
    ///
    /// The lifetime for the returned string is inferred from its usage. To prevent accidental
    /// misuse, it's suggested to tie the lifetime to whichever source lifetime is safe in the
    /// context, such as by providing a helper function taking the lifetime of a host value for the
    /// string, or by explicit annotation.
    pub unsafe fn from_ptr_str(p: *const u32) -> U32CString {
        assert!(!p.is_null());
        let mut i: isize = 0;
        while *p.offset(i) != 0 {
            i = i + 1;
        }
        let slice = std::slice::from_raw_parts(p, i as usize + 1);
        U32CString::from_vec_with_nul_unchecked(slice)
    }

    /// Constructs a new `U32CString` copied from a `char` nul-terminated string pointer.
    ///
    /// This will scan for nul values beginning with `p`. The first nul value will be used as the
    /// nul terminator for the string, similar to how libc string functions such as `strlen` work.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid or has a
    /// nul terminator, and the function could scan past the underlying buffer.
    ///
    /// `p` must be non-null.
    ///
    /// # Panics
    ///
    /// This function panics if `p` is null.
    ///
    /// # Caveat
    ///
    /// The lifetime for the returned string is inferred from its usage. To prevent accidental
    /// misuse, it's suggested to tie the lifetime to whichever source lifetime is safe in the
    /// context, such as by providing a helper function taking the lifetime of a host value for the
    /// string, or by explicit annotation.
    pub unsafe fn from_char_ptr_str(p: *const char) -> U32CString {
        U32CString::from_ptr_str(mem::transmute(p))
    }

    /// Constructs a new `U32CString` copied from a `u32` pointer and a length.
    ///
    /// The `len` argument is the number of `u32` elements, **not** the number of bytes.
    ///
    /// The string will be scanned for invalid nul values.
    ///
    /// # Failures
    ///
    /// This function will return an error if the data contains a nul value.
    /// The returned error will contain a `Vec<u32>` as well as the position of the nul value.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements.
    ///
    /// # Panics
    ///
    /// Panics if `len` is greater than 0 but `p` is a null pointer.
    pub unsafe fn from_ptr(p: *const u32, len: usize) -> Result<U32CString, U32NulError> {
        if len == 0 {
            return Ok(U32CString::default());
        }
        assert!(!p.is_null());
        let slice = std::slice::from_raw_parts(p, len);
        U32CString::new(slice)
    }

    /// Constructs a new `U32CString` copied from a `u32` pointer and a length.
    ///
    /// The `len` argument is the number of `u32` elements, **not** the number of bytes.
    ///
    /// The string will **not** be checked for invalid nul values.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements. In addition, no checking for invalid nul values is performed, so if any elements
    /// of `p` are a nul value, the resulting `U32CString` will be invalid.
    ///
    /// # Panics
    ///
    /// Panics if `len` is greater than 0 but `p` is a null pointer.
    pub unsafe fn from_ptr_unchecked(p: *const u32, len: usize) -> U32CString {
        if len == 0 {
            return U32CString::default();
        }
        assert!(!p.is_null());
        let slice = std::slice::from_raw_parts(p, len);
        U32CString::from_vec_unchecked(slice)
    }

    /// Constructs a new `U32String` copied from a `u32` pointer and a length.
    ///
    /// The `len` argument is the number of `u32` elements, **not** the number of bytes.
    ///
    /// The string will be truncated at the first nul value in the string.
    ///
    /// # Failures
    ///
    /// This function will return an error if the data does not contain a nul to terminate the
    /// string. The returned error will contain the consumed `Vec<u32>`.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements.
    ///
    /// # Panics
    ///
    /// Panics if `len` is greater than 0 but `p` is a null pointer.
    pub unsafe fn from_ptr_with_nul(
        p: *const u32,
        len: usize,
    ) -> Result<U32CString, MissingU32NulError> {
        if len == 0 {
            return Ok(U32CString::default());
        }
        assert!(!p.is_null());
        let slice = std::slice::from_raw_parts(p, len);
        U32CString::from_vec_with_nul(slice)
    }

    /// Constructs a new `U32String` copied from a `u32` pointer and a length.
    ///
    /// The `len` argument is the number of `u32` elements, **not** the number of bytes.
    ///
    /// The data should end with a nul terminator, but no checking is done on whether the data
    /// actually ends with a nul terminator, or if the data contains any interior nul values.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements. In addition, no checking for nul values is performed, so if there data does not
    /// end with a nul terminator, or if there are any interior nul values, the resulting
    /// `U32CString` will be invalid.
    ///
    /// # Panics
    ///
    /// Panics if `len` is greater than 0 but `p` is a null pointer.
    pub unsafe fn from_ptr_with_nul_unchecked(p: *const u32, len: usize) -> U32CString {
        if len == 0 {
            return U32CString::default();
        }
        assert!(!p.is_null());
        let slice = std::slice::from_raw_parts(p, len);
        U32CString::from_vec_with_nul_unchecked(slice)
    }

    /// Constructs a new `U32CString` copied from a `char` pointer and a length.
    ///
    /// The `len` argument is the number of `char` elements, **not** the number of bytes.
    ///
    /// The string will be scanned for invalid nul values.
    ///
    /// # Failures
    ///
    /// This function will return an error if the data contains a nul value.
    /// The returned error will contain a `Vec<u32>` as well as the position of the nul value.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements.
    ///
    /// # Panics
    ///
    /// Panics if `len` is greater than 0 but `p` is a null pointer.
    pub unsafe fn from_char_ptr(p: *const char, len: usize) -> Result<U32CString, U32NulError> {
        U32CString::from_ptr(mem::transmute(p), len)
    }

    /// Constructs a new `U32CString` copied from a `char` pointer and a length.
    ///
    /// The `len` argument is the number of `char` elements, **not** the number of bytes.
    ///
    /// The string will **not** be checked for invalid nul values.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements. In addition, no checking for invalid nul values is performed, so if any elements
    /// of `p` are a nul value, the resulting `U32CString` will be invalid.
    ///
    /// # Panics
    ///
    /// Panics if `len` is greater than 0 but `p` is a null pointer.
    pub unsafe fn from_char_ptr_unchecked(p: *const u32, len: usize) -> U32CString {
        U32CString::from_ptr_unchecked(mem::transmute(p), len)
    }

    /// Constructs a new `U32String` copied from a `char` pointer and a length.
    ///
    /// The `len` argument is the number of `char` elements, **not** the number of bytes.
    ///
    /// The string will be truncated at the first nul value in the string.
    ///
    /// # Failures
    ///
    /// This function will return an error if the data does not contain a nul to terminate the
    /// string. The returned error will contain the consumed `Vec<u32>`.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements.
    ///
    /// # Panics
    ///
    /// Panics if `len` is greater than 0 but `p` is a null pointer.
    pub unsafe fn from_char_ptr_with_nul(
        p: *const u32,
        len: usize,
    ) -> Result<U32CString, MissingU32NulError> {
        U32CString::from_ptr_with_nul(mem::transmute(p), len)
    }

    /// Constructs a new `U32String` copied from a `char` pointer and a length.
    ///
    /// The `len` argument is the number of `char` elements, **not** the number of bytes.
    ///
    /// The data should end with a nul terminator, but no checking is done on whether the data
    /// actually ends with a nul terminator, or if the data contains any interior nul values.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements. In addition, no checking for nul values is performed, so if there data does not
    /// end with a nul terminator, or if there are any interior nul values, the resulting
    /// `U32CString` will be invalid.
    ///
    /// # Panics
    ///
    /// Panics if `len` is greater than 0 but `p` is a null pointer.
    pub unsafe fn from_char_ptr_with_nul_unchecked(p: *const u32, len: usize) -> U32CString {
        U32CString::from_ptr_with_nul_unchecked(mem::transmute(p), len)
    }

    /// Converts to a `U32CStr` reference.
    pub fn as_u32_c_str(&self) -> &U32CStr {
        self
    }

    /// Converts the wide string into a `Vec<u32>` without a nul terminator, consuming the string in
    /// the process.
    ///
    /// The resulting vector will **not** contain a nul-terminator, and will contain no other nul
    /// values.
    pub fn into_vec(self) -> Vec<u32> {
        let mut v = self.into_inner().into_vec();
        v.pop();
        v
    }

    /// Converts the wide string into a `Vec<u32>`, consuming the string in the process.
    ///
    /// The resulting vector will contain a nul-terminator and no interior nul values.
    pub fn into_vec_with_nul(self) -> Vec<u32> {
        self.into_inner().into_vec()
    }

    /// Transfers ownership of the wide string to a C caller.
    ///
    /// # Safety
    ///
    /// The pointer must be returned to Rust and reconstituted using `from_raw` to be properly
    /// deallocated. Specifically, one should _not_ use the standard C `free` function to deallocate
    /// this string.
    ///
    /// Failure to call `from_raw` will lead to a memory leak.
    pub fn into_raw(self) -> *mut u32 {
        Box::into_raw(self.into_inner()) as *mut u32
    }

    /// Retakes ownership of a `U32CString` that was transferred to C.
    ///
    /// # Safety
    ///
    /// This should only ever be called with a pointer that was earlier obtained by calling
    /// `into_raw` on a `U32CString`. Additionally, the length of the string will be recalculated
    /// from the pointer.
    pub unsafe fn from_raw(p: *mut u32) -> U32CString {
        assert!(!p.is_null());
        let mut i: isize = 0;
        while *p.offset(i) != 0 {
            i += 1;
        }
        let slice = std::slice::from_raw_parts_mut(p, i as usize + 1);
        U32CString {
            inner: mem::transmute(slice),
        }
    }

    /// Converts this `U32CString` into a boxed `U32CStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// use widestring::{U32CString, U32CStr};
    ///
    /// let mut v = vec![102u32, 111u32, 111u32]; // "foo"
    /// let c_string = U32CString::new(v.clone()).unwrap();
    /// let boxed = c_string.into_boxed_u32_c_str();
    /// v.push(0);
    /// assert_eq!(&*boxed, U32CStr::from_slice_with_nul(&v).unwrap());
    /// ```
    pub fn into_boxed_u32_c_str(self) -> Box<U32CStr> {
        unsafe { Box::from_raw(Box::into_raw(self.into_inner()) as *mut U32CStr) }
    }

    /// Bypass "move out of struct which implements [`Drop`] trait" restriction.
    ///
    /// [`Drop`]: ../ops/trait.Drop.html
    fn into_inner(self) -> Box<[u32]> {
        unsafe {
            let result = std::ptr::read(&self.inner);
            mem::forget(self);
            result
        }
    }
}

impl Into<Vec<u32>> for U32CString {
    fn into(self) -> Vec<u32> {
        self.into_vec()
    }
}

impl<'a> From<U32CString> for std::borrow::Cow<'a, U32CStr> {
    fn from(s: U32CString) -> std::borrow::Cow<'a, U32CStr> {
        std::borrow::Cow::Owned(s)
    }
}
impl From<U32CString> for OsString {
    fn from(s: U32CString) -> OsString {
        s.to_os_string()
    }
}

impl From<U32CString> for U32String {
    fn from(s: U32CString) -> U32String {
        s.to_u32_string()
    }
}

impl<'a, T: ?Sized + AsRef<U32CStr>> From<&'a T> for U32CString {
    fn from(s: &'a T) -> U32CString {
        s.as_ref().to_u32_c_string()
    }
}

impl std::ops::Index<std::ops::RangeFull> for U32CString {
    type Output = U32CStr;

    #[inline]
    fn index(&self, _index: std::ops::RangeFull) -> &U32CStr {
        U32CStr::from_inner(&self.inner)
    }
}

impl std::ops::Deref for U32CString {
    type Target = U32CStr;

    #[inline]
    fn deref(&self) -> &U32CStr {
        &self[..]
    }
}

impl<'a> Default for &'a U32CStr {
    fn default() -> &'a U32CStr {
        const SLICE: &'static [u32] = &[0];
        unsafe { U32CStr::from_slice_with_nul_unchecked(SLICE) }
    }
}

impl Default for U32CString {
    fn default() -> U32CString {
        let def: &U32CStr = Default::default();
        def.to_u32_c_string()
    }
}

// Turns this `U32CString` into an empty string to prevent
// memory unsafe code from working by accident. Inline
// to prevent LLVM from optimizing it away in debug builds.
impl Drop for U32CString {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            *self.inner.get_unchecked_mut(0) = 0;
        }
    }
}

impl U32CStr {
    /// Coerces a value into a `U32CStr`.
    pub fn new<S: AsRef<U32CStr> + ?Sized>(s: &S) -> &U32CStr {
        s.as_ref()
    }

    fn from_inner(slice: &[u32]) -> &U32CStr {
        unsafe { mem::transmute(slice) }
    }

    /// Constructs a `U32Str` from a `u32` nul-terminated string pointer.
    ///
    /// This will scan for nul values beginning with `p`. The first nul value will be used as the
    /// nul terminator for the string, similar to how libc string functions such as `strlen` work.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid or has a
    /// nul terminator, and the function could scan past the underlying buffer.
    ///
    /// `p` must be non-null.
    ///
    /// # Panics
    ///
    /// This function panics if `p` is null.
    ///
    /// # Caveat
    ///
    /// The lifetime for the returned string is inferred from its usage. To prevent accidental
    /// misuse, it's suggested to tie the lifetime to whichever source lifetime is safe in the
    /// context, such as by providing a helper function taking the lifetime of a host value for the
    /// string, or by explicit annotation.
    pub unsafe fn from_ptr_str<'a>(p: *const u32) -> &'a U32CStr {
        assert!(!p.is_null());
        let mut i: isize = 0;
        while *p.offset(i) != 0 {
            i = i + 1;
        }
        mem::transmute(std::slice::from_raw_parts(p, i as usize + 1))
    }

    /// Constructs a `U32Str` from a `char` nul-terminated string pointer.
    ///
    /// This will scan for nul values beginning with `p`. The first nul value will be used as the
    /// nul terminator for the string, similar to how libc string functions such as `strlen` work.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid or has a
    /// nul terminator, and the function could scan past the underlying buffer.
    ///
    /// `p` must be non-null.
    ///
    /// # Panics
    ///
    /// This function panics if `p` is null.
    ///
    /// # Caveat
    ///
    /// The lifetime for the returned string is inferred from its usage. To prevent accidental
    /// misuse, it's suggested to tie the lifetime to whichever source lifetime is safe in the
    /// context, such as by providing a helper function taking the lifetime of a host value for the
    /// string, or by explicit annotation.
    pub unsafe fn from_char_ptr_str<'a>(p: *const char) -> &'a U32CStr {
        U32CStr::from_ptr_str(p as *const u32)
    }

    /// Constructs a `U32Str` from a `u32` pointer and a length.
    ///
    /// The `len` argument is the number of `u32` elements, **not** the number of bytes, and does
    /// **not** include the nul terminator of the string. Thus, a `len` of 0 is valid and means that
    /// `p` is a pointer directly to the nul terminator of the string.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements.
    ///
    /// `p` must be non-null, even for zero `len`.
    ///
    /// The interior values of the pointer are not scanned for nul. Any interior nul values will
    /// result in an invalid `U32CStr`.
    ///
    /// # Panics
    ///
    /// This function panics if `p` is null or if a nul value is not found at offset `len` of `p`.
    /// Only pointers with a nul terminator are valid.
    ///
    /// # Caveat
    ///
    /// The lifetime for the returned string is inferred from its usage. To prevent accidental
    /// misuse, it's suggested to tie the lifetime to whichever source lifetime is safe in the
    /// context, such as by providing a helper function taking the lifetime of a host value for the
    /// string, or by explicit annotation.
    pub unsafe fn from_ptr_with_nul<'a>(p: *const u32, len: usize) -> &'a U32CStr {
        assert!(*p.offset(len as isize) == 0);
        mem::transmute(std::slice::from_raw_parts(p, len + 1))
    }

    /// Constructs a `U32Str` from a `char` pointer and a length.
    ///
    /// The `len` argument is the number of `char` elements, **not** the number of bytes, and does
    /// **not** include the nul terminator of the string. Thus, a `len` of 0 is valid and means that
    /// `p` is a pointer directly to the nul terminator of the string.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements.
    ///
    /// `p` must be non-null, even for zero `len`.
    ///
    /// The interior values of the pointer are not scanned for nul. Any interior nul values will
    /// result in an invalid `U32CStr`.
    ///
    /// # Panics
    ///
    /// This function panics if `p` is null or if a nul value is not found at offset `len` of `p`.
    /// Only pointers with a nul terminator are valid.
    ///
    /// # Caveat
    ///
    /// The lifetime for the returned string is inferred from its usage. To prevent accidental
    /// misuse, it's suggested to tie the lifetime to whichever source lifetime is safe in the
    /// context, such as by providing a helper function taking the lifetime of a host value for the
    /// string, or by explicit annotation.
    pub unsafe fn from_char_ptr_with_nul<'a>(p: *const char, len: usize) -> &'a U32CStr {
        U32CStr::from_ptr_with_nul(p as *const u32, len)
    }

    /// Constructs a `U32CStr` from a slice of `u32` values that has a nul terminator.
    ///
    /// The slice will be scanned for nul values. When a nul value is found, it is treated as the
    /// terminator for the string, and the `U32CStr` slice will be truncated to that nul.
    ///
    /// # Failure
    ///
    /// If there are no no nul values in `slice`, an error is returned.
    pub fn from_slice_with_nul(slice: &[u32]) -> Result<&U32CStr, MissingU32NulError> {
        match slice.iter().position(|x| *x == 0) {
            None => Err(MissingU32NulError(None)),
            Some(i) => Ok(unsafe { U32CStr::from_slice_with_nul_unchecked(&slice[..i + 1]) }),
        }
    }

    /// Constructs a `U32CStr` from a slice of `u32` values that has a nul terminator. No
    /// checking for nul values is performed.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it can lead to invalid `U32CStr` values when `slice`
    /// is missing a terminating nul value or there are non-terminating interior nul values
    /// in the slice.
    pub unsafe fn from_slice_with_nul_unchecked(slice: &[u32]) -> &U32CStr {
        std::mem::transmute(slice)
    }

    /// Constructs a `U32CStr` from a slice of `char` values that has a nul terminator.
    ///
    /// The slice will be scanned for nul values. When a nul value is found, it is treated as the
    /// terminator for the string, and the `U32CStr` slice will be truncated to that nul.
    ///
    /// # Failure
    ///
    /// If there are no no nul values in `slice`, an error is returned.
    pub fn from_char_slice_with_nul(slice: &[char]) -> Result<&U32CStr, MissingU32NulError> {
        U32CStr::from_slice_with_nul(unsafe { mem::transmute(slice) })
    }

    /// Constructs a `U32CStr` from a slice of `char` values that has a nul terminator. No
    /// checking for nul values is performed.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it can lead to invalid `U32CStr` values when `slice`
    /// is missing a terminating nul value or there are non-terminating interior nul values
    /// in the slice.
    pub unsafe fn from_char_slice_with_nul_unchecked(slice: &[char]) -> &U32CStr {
        U32CStr::from_slice_with_nul_unchecked(mem::transmute(slice))
    }

    /// Copies the wide string to an new owned `U32String`.
    pub fn to_u32_c_string(&self) -> U32CString {
        unsafe { U32CString::from_vec_with_nul_unchecked(self.inner.to_owned()) }
    }

    /// Decodes a wide string to an owned `OsString`.
    ///
    /// This makes a string copy of the `U32CStr`. Since `U32CStr` makes no guarantees that it is
    /// valid UTF-32, there is no guarantee that the resulting `OsString` will be valid data. The
    /// `OsString` will **not** have a nul terminator.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// use std::ffi::OsString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wstr = U32CString::from_str(s).unwrap();
    /// // Create an OsString from the wide string
    /// let osstr = wstr.to_os_string();
    ///
    /// assert_eq!(osstr, OsString::from(s));
    /// ```
    pub fn to_os_string(&self) -> OsString {
        self.to_u32_string().to_os_string()
    }

    /// Copies the wide string to a new owned `U32String`.
    ///
    /// The `U32String` will **not** have a nul terminator.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let wcstr = U32CString::from_str("MyString").unwrap();
    /// // Convert U32CString to a U32String
    /// let wstr = wcstr.to_u32_string();
    ///
    /// // U32CString will have a terminating nul
    /// let wcvec = wcstr.into_vec_with_nul();
    /// assert_eq!(wcvec[wcvec.len()-1], 0);
    /// // The resulting U32String will not have the terminating nul
    /// let wvec = wstr.into_vec();
    /// assert_ne!(wvec[wvec.len()-1], 0);
    /// ```
    pub fn to_u32_string(&self) -> U32String {
        U32String::from_vec(self.as_slice())
    }

    /// Copies the wide string to a `String` if it contains valid UTF-32 data.
    ///
    /// # Failures
    ///
    /// Returns an error if the string contains any invalid UTF-32 data.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wstr = U32CString::from_str(s).unwrap();
    /// // Create a regular string from the wide string
    /// let s2 = wstr.to_string().unwrap();
    ///
    /// assert_eq!(s2, s);
    /// ```
    pub fn to_string(&self) -> Result<String, FromUtf32Error> {
        self.to_u32_string().to_string()
    }

    /// Copies the wide string to a `String`.
    ///
    /// Any non-Unicode sequences are replaced with U+FFFD REPLACEMENT CHARACTER.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::U32CString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wstr = U32CString::from_str(s).unwrap();
    /// // Create a regular string from the wide string
    /// let s2 = wstr.to_string_lossy();
    ///
    /// assert_eq!(s2, s);
    /// ```
    pub fn to_string_lossy(&self) -> String {
        self.to_u32_string().to_string_lossy()
    }

    /// Converts to a slice of the wide string.
    ///
    /// The slice will **not** include the nul terminator.
    pub fn as_slice(&self) -> &[u32] {
        &self.inner[..self.len()]
    }

    /// Converts to a slice of the wide string, including the nul terminator.
    pub fn as_slice_with_nul(&self) -> &[u32] {
        &self.inner
    }

    /// Returns a raw pointer to the wide string.
    ///
    /// The pointer is valid only as long as the lifetime of this reference.
    pub fn as_ptr(&self) -> *const u32 {
        self.inner.as_ptr()
    }

    /// Returns the length of the wide string as number of UTF-16 code units (**not** code
    /// points and **not** number of bytes) **not** including nul terminator.
    pub fn len(&self) -> usize {
        self.inner.len() - 1
    }

    /// Returns whether this wide string contains no data (i.e. is only the nul terminator).
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Converts a `Box<U32CStr>` into a `U32CString` without copying or allocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use widestring::U32CString;
    ///
    /// let v = vec![102u32, 111u32, 111u32]; // "foo"
    /// let c_string = U32CString::new(v.clone()).unwrap();
    /// let boxed = c_string.into_boxed_u32_c_str();
    /// assert_eq!(boxed.into_u32_c_string(), U32CString::new(v).unwrap());
    /// ```
    pub fn into_u32_c_string(self: Box<U32CStr>) -> U32CString {
        let raw = Box::into_raw(self) as *mut [u32];
        U32CString {
            inner: unsafe { Box::from_raw(raw) },
        }
    }
}

impl std::borrow::Borrow<U32CStr> for U32CString {
    fn borrow(&self) -> &U32CStr {
        &self[..]
    }
}

impl ToOwned for U32CStr {
    type Owned = U32CString;
    fn to_owned(&self) -> U32CString {
        self.to_u32_c_string()
    }
}

impl<'a> From<&'a U32CStr> for std::borrow::Cow<'a, U32CStr> {
    fn from(s: &'a U32CStr) -> std::borrow::Cow<'a, U32CStr> {
        std::borrow::Cow::Borrowed(s)
    }
}

impl AsRef<U32CStr> for U32CStr {
    fn as_ref(&self) -> &U32CStr {
        self
    }
}

impl AsRef<U32CStr> for U32CString {
    fn as_ref(&self) -> &U32CStr {
        self
    }
}

impl AsRef<[u32]> for U32CStr {
    fn as_ref(&self) -> &[u32] {
        self.as_slice()
    }
}

impl AsRef<[u32]> for U32CString {
    fn as_ref(&self) -> &[u32] {
        self.as_slice()
    }
}

impl<'a> From<&'a U32CStr> for Box<U32CStr> {
    fn from(s: &'a U32CStr) -> Box<U32CStr> {
        let boxed: Box<[u32]> = Box::from(s.as_slice_with_nul());
        unsafe { Box::from_raw(Box::into_raw(boxed) as *mut U32CStr) }
    }
}

impl From<Box<U32CStr>> for U32CString {
    #[inline]
    fn from(s: Box<U32CStr>) -> U32CString {
        s.into_u32_c_string()
    }
}

impl From<U32CString> for Box<U32CStr> {
    #[inline]
    fn from(s: U32CString) -> Box<U32CStr> {
        s.into_boxed_u32_c_str()
    }
}

impl Default for Box<U32CStr> {
    fn default() -> Box<U32CStr> {
        let boxed: Box<[u32]> = Box::from([0]);
        unsafe { Box::from_raw(Box::into_raw(boxed) as *mut U32CStr) }
    }
}

impl U32NulError {
    /// Returns the position of the nul value in the slice that was provided to `U32CString`.
    pub fn nul_position(&self) -> usize {
        self.0
    }

    /// Consumes this error, returning the underlying vector of u16 values which generated the error
    /// in the first place.
    pub fn into_vec(self) -> Vec<u32> {
        self.1
    }
}

impl Into<Vec<u32>> for U32NulError {
    fn into(self) -> Vec<u32> {
        self.into_vec()
    }
}

impl std::fmt::Display for U32NulError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "nul value found at position {}", self.0)
    }
}

impl std::error::Error for U32NulError {
    fn description(&self) -> &str {
        "nul value found"
    }
}

impl MissingU32NulError {
    /// Consumes this error, returning the underlying vector of `u16` values which generated the
    /// error in the first place.
    pub fn into_vec(self) -> Option<Vec<u32>> {
        self.0
    }
}

impl std::fmt::Display for MissingU32NulError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "missing terminating nul value")
    }
}

impl std::error::Error for MissingU32NulError {
    fn description(&self) -> &str {
        "missing terminating nul value"
    }
}
