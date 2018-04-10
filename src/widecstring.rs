use std;
use std::mem;
use super::{WideStr, WideString};
use std::ffi::{OsStr, OsString};
use super::platform;

/// An owned, mutable C-style "wide" string for FFI that is nul-aware and nul-terminated.
///
/// `WideCString` is aware of nul values. Unless unchecked conversions are used, all `WideCString`
/// strings end with a nul-terminator in the underlying buffer and contain no internal nul values.
/// The strings may still contain invalid or ill-formed UTF-16 data. These strings are intended to
/// be used with FFI functions such as Windows API that may require nul-terminated strings.
///
/// `WideCString` can be converted to and from many other string types, including `WideString`,
/// `OsString`, and `String`, making proper Unicode Windows FFI safe and easy.
///
/// # Examples
///
/// The following example constructs a `WideCString` and shows how to convert a `WideCString` to a
/// regular Rust `String`.
///
/// ```rust
/// use widestring::WideCString;
/// let v = vec![84u16, 104u16, 101u16]; // 'T' 'h' 'e'
/// // Create a wide string from the vector
/// let wstr = WideCString::new(v).unwrap();
/// // Convert to a rust string!
/// let rust_str = wstr.to_string_lossy();
/// assert_eq!(rust_str, "The");
/// ```
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct WideCString {
    inner: Box<[u16]>,
}

/// C-style wide string reference for `WideCString`.
///
/// `WideCStr` is aware of nul values. Unless unchecked conversions are used, all `WideCStr`
/// strings end with a nul-terminator in the underlying buffer and contain no internal nul values.
/// The strings may still contain invalid or ill-formed UTF-16 data. These strings are intended to
/// be used with FFI functions such as Windows API that may require nul-terminated strings.
///
/// `WideCStr` can be converted to and from many other string types, including `WideString`,
/// `OsString`, and `String`, making proper Unicode Windows FFI safe and easy.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct WideCStr {
    inner: [u16],
}

/// An error returned from `WideCString` to indicate that an invalid nul value was found.
///
/// The error indicates the position in the vector where the nul value was found, as well as
/// returning the ownership of the invalid vector.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NulError(usize, Vec<u16>);

/// An error returned from `WideCString` and `WideCStr` to indicate that a terminating nul value
/// was missing.
///
/// The error optionally returns the ownership of the invalid vector whenever a vector was owned.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MissingNulError(Option<Vec<u16>>);

impl WideCString {
    /// Constructs a `WideCString` from a container of wide character data.
    ///
    /// This method will consume the provided data and use the underlying elements to construct a
    /// new string. The data will be scanned for invalid nul values.
    ///
    /// # Failures
    ///
    /// This function will return an error if the data contains a nul value.
    /// The returned error will contain the `Vec<u16>` as well as the position of the nul value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::WideCString;
    /// let v = vec![84u16, 104u16, 101u16]; // 'T' 'h' 'e'
    /// # let cloned = v.clone();
    /// // Create a wide string from the vector
    /// let wcstr = WideCString::new(v).unwrap();
    /// # assert_eq!(wcstr.into_vec(), cloned);
    /// ```
    ///
    /// The following example demonstrates errors from nul values in a vector.
    ///
    /// ```rust
    /// use widestring::WideCString;
    /// let v = vec![84u16, 0u16, 104u16, 101u16]; // 'T' NUL 'h' 'e'
    /// // Create a wide string from the vector
    /// let res = WideCString::new(v);
    /// assert!(res.is_err());
    /// assert_eq!(res.err().unwrap().nul_position(), 1);
    /// ```
    pub fn new<T: Into<Vec<u16>>>(v: T) -> Result<WideCString, NulError> {
        let v = v.into();
        // Check for nul vals
        match v.iter().position(|&val| val == 0) {
            None => Ok(unsafe { WideCString::from_vec_unchecked(v) }),
            Some(pos) => Err(NulError(pos, v)),
        }
    }

    /// Constructs a `WideCString` from a nul-terminated container of UTF-16 data.
    ///
    /// This method will consume the provided data and use the underlying elements to construct a
    /// new string. The string will be truncated at the first nul value in the string.
    ///
    /// # Failures
    ///
    /// This function will return an error if the data does not contain a nul to terminate the
    /// string. The returned error will contain the consumed `Vec<u16>`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::WideCString;
    /// let v = vec![84u16, 104u16, 101u16, 0u16]; // 'T' 'h' 'e' NUL
    /// # let cloned = v[..3].to_owned();
    /// // Create a wide string from the vector
    /// let wcstr = WideCString::from_vec_with_nul(v).unwrap();
    /// # assert_eq!(wcstr.into_vec(), cloned);
    /// ```
    ///
    /// The following example demonstrates errors from missing nul values in a vector.
    ///
    /// ```rust
    /// use widestring::WideCString;
    /// let v = vec![84u16, 104u16, 101u16]; // 'T' 'h' 'e'
    /// // Create a wide string from the vector
    /// let res = WideCString::from_vec_with_nul(v);
    /// assert!(res.is_err());
    /// ```
    pub fn from_vec_with_nul<T: Into<Vec<u16>>>(v: T) -> Result<WideCString, MissingNulError> {
        let mut v = v.into();
        // Check for nul vals
        match v.iter().position(|&val| val == 0) {
            None => Err(MissingNulError(Some(v))),
            Some(pos) => {
                v.truncate(pos + 1);
                Ok(unsafe { WideCString::from_vec_with_nul_unchecked(v) })
            }
        }
    }

    /// Creates a `WideCString` from a vector without checking for interior nul values.
    ///
    /// A terminating nul value will be appended if the vector does not already have a terminating
    /// nul.
    ///
    /// # Safety
    ///
    /// This method is equivalent to `new` except that no runtime assertion is made that `v`
    /// contains no nul values. Providing a vector with nul values will result in an invalid
    /// `WideCString`.
    pub unsafe fn from_vec_unchecked<T: Into<Vec<u16>>>(v: T) -> WideCString {
        let mut v = v.into();
        match v.last() {
            None => v.push(0),
            Some(&c) if c != 0 => v.push(0),
            Some(_) => (),
        }
        WideCString::from_vec_with_nul_unchecked(v)
    }

    /// Creates a `WideCString` from a vector that should have a nul terminator, without checking
    /// for any nul values.
    ///
    /// # Safety
    ///
    /// This method is equivalent to `from_vec_with_nul` except that no runtime assertion is made
    /// that `v` contains no nul values. Providing a vector with interior nul values or without a
    /// terminating nul value will result in an invalid `WideCString`.
    pub unsafe fn from_vec_with_nul_unchecked<T: Into<Vec<u16>>>(v: T) -> WideCString {
        WideCString {
            inner: v.into().into_boxed_slice(),
        }
    }

    /// Constructs a `WideCString` from anything that can be converted to an `OsStr`.
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
    /// use widestring::WideCString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wcstr = WideCString::from_str(s).unwrap();
    /// # assert_eq!(wcstr.to_string_lossy(), s);
    /// ```
    ///
    /// The following example demonstrates errors from nul values in a vector.
    ///
    /// ```rust
    /// use widestring::WideCString;
    /// let s = "My\u{0}String";
    /// // Create a wide string from the string
    /// let res = WideCString::from_str(s);
    /// assert!(res.is_err());
    /// assert_eq!(res.err().unwrap().nul_position(), 2);
    /// ```
    pub fn from_str<T: AsRef<OsStr>>(s: T) -> Result<WideCString, NulError> {
        let v = platform::os_to_wide(s.as_ref());
        WideCString::new(v)
    }

    /// Constructs a `WideCString` from anything that can be converted to an `OsStr`, without
    /// checking for interior nul values.
    ///
    /// # Safety
    ///
    /// This method is equivalent to `from_str` except that no runtime assertion is made that `s`
    /// contains no nul values. Providing a string with nul values will result in an invalid
    /// `WideCString`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::WideCString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wcstr = unsafe { WideCString::from_str_unchecked(s) };
    /// # assert_eq!(wcstr.to_string_lossy(), s);
    /// ```
    pub unsafe fn from_str_unchecked<T: AsRef<OsStr>>(s: T) -> WideCString {
        let v = platform::os_to_wide(s.as_ref());
        WideCString::from_vec_unchecked(v)
    }

    /// Constructs a `WideCString` from anything that can be converted to an `OsStr` with a nul
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
    /// use widestring::WideCString;
    /// let s = "My\u{0}String";
    /// // Create a wide string from the string
    /// let wcstr = WideCString::from_str_with_nul(s).unwrap();
    /// assert_eq!(wcstr.to_string_lossy(), "My");
    /// ```
    ///
    /// The following example demonstrates errors from missing nul values in a vector.
    ///
    /// ```rust
    /// use widestring::WideCString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let res = WideCString::from_str_with_nul(s);
    /// assert!(res.is_err());
    /// ```
    pub fn from_str_with_nul<T: AsRef<OsStr>>(s: T) -> Result<WideCString, MissingNulError> {
        let v = platform::os_to_wide(s.as_ref());
        WideCString::from_vec_with_nul(v)
    }

    /// Constructs a `WideCString` from anything that can be converted to an `OsStr` that should
    /// have a terminating nul, but without checking for any nul values.
    ///
    /// # Safety
    ///
    /// This method is equivalent to `from_str_with_nul` except that no runtime assertion is made
    /// that `s` contains no nul values. Providing a vector with interior nul values or without a
    /// terminating nul value will result in an invalid `WideCString`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::WideCString;
    /// let s = "My String\u{0}";
    /// // Create a wide string from the string
    /// let wcstr = unsafe { WideCString::from_str_with_nul_unchecked(s) };
    /// assert_eq!(wcstr.to_string_lossy(), "My String");
    /// ```
    pub unsafe fn from_str_with_nul_unchecked<T: AsRef<OsStr>>(s: T) -> WideCString {
        let v = platform::os_to_wide(s.as_ref());
        WideCString::from_vec_with_nul_unchecked(v)
    }

    /// Constructs a `WideCString` from anything that can be converted to a `WideStr`.
    ///
    /// The string will be scanned for invalid nul values.
    ///
    /// # Failures
    ///
    /// This function will return an error if the data contains a nul value.
    /// The returned error will contain a `Vec<u16>` as well as the position of the nul value.
    pub fn from_wide_str<T: AsRef<WideStr>>(s: T) -> Result<WideCString, NulError> {
        WideCString::new(s.as_ref().as_slice())
    }

    /// Constructs a `WideCString` from anything that can be converted to a `WideStr`, without
    /// scanning for invalid nul values.
    ///
    /// # Safety
    ///
    /// This method is equivalent to `from_wide_str` except that no runtime assertion is made that
    /// `s` contains no nul values. Providing a string with nul values will result in an invalid
    /// `WideCString`.
    pub unsafe fn from_wide_str_unchecked<T: AsRef<WideStr>>(s: T) -> WideCString {
        WideCString::from_vec_unchecked(s.as_ref().as_slice())
    }

    /// Constructs a `WideCString` from anything that can be converted to a `WideStr` with a nul
    /// terminator.
    ///
    /// The string will be truncated at the first nul value in the string.
    ///
    /// # Failures
    ///
    /// This function will return an error if the data does not contain a nul to terminate the
    /// string. The returned error will contain the consumed `Vec<u16>`.
    pub fn from_wide_str_with_nul<T: AsRef<WideStr>>(s: T) -> Result<WideCString, MissingNulError> {
        WideCString::from_vec_with_nul(s.as_ref().as_slice())
    }

    /// Constructs a `WideCString` from anything that can be converted to a `WideStr` with a nul
    /// terminator, without checking the string for any invalid interior nul values.
    ///
    /// # Safety
    ///
    /// This method is equivalent to `from_wide_str_with_nul` except that no runtime assertion is
    /// made that `s` contains no nul values. Providing a vector with interior nul values or
    /// without a terminating nul value will result in an invalid `WideCString`.
    pub unsafe fn from_wide_str_with_nul_unchecked<T: AsRef<WideStr>>(s: T) -> WideCString {
        WideCString::from_vec_with_nul_unchecked(s.as_ref().as_slice())
    }

    /// Constructs a new `WideCString` copied from a `u16` nul-terminated string pointer.
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
    pub unsafe fn from_ptr_str(p: *const u16) -> WideCString {
        assert!(!p.is_null());
        let mut i: isize = 0;
        while *p.offset(i) != 0 {
            i = i + 1;
        }
        let slice = std::slice::from_raw_parts(p, i as usize + 1);
        WideCString::from_vec_with_nul_unchecked(slice)
    }

    /// Constructs a new `WideCString` copied from a `u16` pointer and a length.
    ///
    /// The `len` argument is the number of `u16` elements, **not** the number of bytes.
    ///
    /// The string will be scanned for invalid nul values.
    ///
    /// # Failures
    ///
    /// This function will return an error if the data contains a nul value.
    /// The returned error will contain a `Vec<u16>` as well as the position of the nul value.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements.
    ///
    /// # Panics
    ///
    /// Panics if `len` is greater than 0 but `p` is a null pointer.
    pub unsafe fn from_ptr(p: *const u16, len: usize) -> Result<WideCString, NulError> {
        if len == 0 {
            return Ok(WideCString::default());
        }
        assert!(!p.is_null());
        let slice = std::slice::from_raw_parts(p, len);
        WideCString::new(slice)
    }

    /// Constructs a new `WideCString` copied from a `u16` pointer and a length.
    ///
    /// The `len` argument is the number of `u16` elements, **not** the number of bytes.
    ///
    /// The string will **not** be checked for invalid nul values.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements. In addition, no checking for invalid nul values is performed, so if any elements
    /// of `p` are a nul value, the resulting `WideCString` will be invalid.
    ///
    /// # Panics
    ///
    /// Panics if `len` is greater than 0 but `p` is a null pointer.
    pub unsafe fn from_ptr_unchecked(p: *const u16, len: usize) -> WideCString {
        if len == 0 {
            return WideCString::default();
        }
        assert!(!p.is_null());
        let slice = std::slice::from_raw_parts(p, len);
        WideCString::from_vec_unchecked(slice)
    }

    /// Constructs a new `WideString` copied from a `u16` pointer and a length.
    ///
    /// The `len` argument is the number of `u16` elements, **not** the number of bytes.
    ///
    /// The string will be truncated at the first nul value in the string.
    ///
    /// # Failures
    ///
    /// This function will return an error if the data does not contain a nul to terminate the
    /// string. The returned error will contain the consumed `Vec<u16>`.
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
        p: *const u16,
        len: usize,
    ) -> Result<WideCString, MissingNulError> {
        if len == 0 {
            return Ok(WideCString::default());
        }
        assert!(!p.is_null());
        let slice = std::slice::from_raw_parts(p, len);
        WideCString::from_vec_with_nul(slice)
    }

    /// Constructs a new `WideString` copied from a `u16` pointer and a length.
    ///
    /// The `len` argument is the number of `u16` elements, **not** the number of bytes.
    ///
    /// The data should end with a nul terminator, but no checking is done on whether the data
    /// actually ends with a nul terminator, or if the data contains any interior nul values.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer is valid for `len`
    /// elements. In addition, no checking for nul values is performed, so if there data does not
    /// end with a nul terminator, or if there are any interior nul values, the resulting
    /// `WideCString` will be invalid.
    ///
    /// # Panics
    ///
    /// Panics if `len` is greater than 0 but `p` is a null pointer.
    pub unsafe fn from_ptr_with_nul_unchecked(p: *const u16, len: usize) -> WideCString {
        if len == 0 {
            return WideCString::default();
        }
        assert!(!p.is_null());
        let slice = std::slice::from_raw_parts(p, len);
        WideCString::from_vec_with_nul_unchecked(slice)
    }

    /// Converts to a `WideCStr` reference.
    pub fn as_wide_c_str(&self) -> &WideCStr {
        self
    }

    /// Converts the wide string into a `Vec<u16>` without a nul terminator, consuming the string in
    /// the process.
    ///
    /// The resulting vector will **not** contain a nul-terminator, and will contain no other nul
    /// values.
    pub fn into_vec(self) -> Vec<u16> {
        let mut v = self.into_inner().into_vec();
        v.pop();
        v
    }

    /// Converts the wide string into a `Vec<u16>`, consuming the string in the process.
    ///
    /// The resulting vector will contain a nul-terminator and no interior nul values.
    pub fn into_vec_with_nul(self) -> Vec<u16> {
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
    pub fn into_raw(self) -> *mut u16 {
        Box::into_raw(self.into_inner()) as *mut u16
    }

    /// Retakes ownership of a `WideCString` that was transferred to C.
    ///
    /// # Safety
    ///
    /// This should only ever be called with a pointer that was earlier obtained by calling
    /// `into_raw` on a `WideCString`. Additionally, the length of the string will be recalculated
    /// from the pointer.
    pub unsafe fn from_raw(p: *mut u16) -> WideCString {
        assert!(!p.is_null());
        let mut i: isize = 0;
        while *p.offset(i) != 0 {
            i += 1;
        }
        let slice = std::slice::from_raw_parts_mut(p, i as usize + 1);
        WideCString {
            inner: mem::transmute(slice),
        }
    }

    /// Converts this `WideCString` into a boxed `WideCStr`.
    ///
    /// # Examples
    ///
    /// ```
    /// use widestring::{WideCString, WideCStr};
    ///
    /// let mut v = vec![102u16, 111u16, 111u16]; // "foo"
    /// let c_string = WideCString::new(v.clone()).unwrap();
    /// let boxed = c_string.into_boxed_wide_c_str();
    /// v.push(0);
    /// assert_eq!(&*boxed, WideCStr::from_slice_with_nul(&v).unwrap());
    /// ```
    pub fn into_boxed_wide_c_str(self) -> Box<WideCStr> {
        unsafe { Box::from_raw(Box::into_raw(self.into_inner()) as *mut WideCStr) }
    }

    /// Bypass "move out of struct which implements [`Drop`] trait" restriction.
    ///
    /// [`Drop`]: ../ops/trait.Drop.html
    fn into_inner(self) -> Box<[u16]> {
        unsafe {
            let result = std::ptr::read(&self.inner);
            mem::forget(self);
            result
        }
    }
}

impl Into<Vec<u16>> for WideCString {
    fn into(self) -> Vec<u16> {
        self.into_vec()
    }
}

impl<'a> From<WideCString> for std::borrow::Cow<'a, WideCStr> {
    fn from(s: WideCString) -> std::borrow::Cow<'a, WideCStr> {
        std::borrow::Cow::Owned(s)
    }
}
impl From<WideCString> for OsString {
    fn from(s: WideCString) -> OsString {
        s.to_os_string()
    }
}

impl From<WideCString> for WideString {
    fn from(s: WideCString) -> WideString {
        s.to_wide_string()
    }
}

impl<'a, T: ?Sized + AsRef<WideCStr>> From<&'a T> for WideCString {
    fn from(s: &'a T) -> WideCString {
        s.as_ref().to_wide_c_string()
    }
}

impl std::ops::Index<std::ops::RangeFull> for WideCString {
    type Output = WideCStr;

    #[inline]
    fn index(&self, _index: std::ops::RangeFull) -> &WideCStr {
        WideCStr::from_inner(&self.inner)
    }
}

impl std::ops::Deref for WideCString {
    type Target = WideCStr;

    #[inline]
    fn deref(&self) -> &WideCStr {
        &self[..]
    }
}

impl<'a> Default for &'a WideCStr {
    fn default() -> &'a WideCStr {
        const SLICE: &'static [u16] = &[0u16];
        unsafe { WideCStr::from_slice_with_nul_unchecked(SLICE) }
    }
}

impl Default for WideCString {
    fn default() -> WideCString {
        let def: &WideCStr = Default::default();
        def.to_wide_c_string()
    }
}

// Turns this `WideCString` into an empty string to prevent
// memory unsafe code from working by accident. Inline
// to prevent LLVM from optimizing it away in debug builds.
impl Drop for WideCString {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            *self.inner.get_unchecked_mut(0) = 0;
        }
    }
}

impl WideCStr {
    /// Coerces a value into a `WideCStr`.
    pub fn new<'a, S: AsRef<WideCStr> + ?Sized>(s: &'a S) -> &'a WideCStr {
        s.as_ref()
    }

    fn from_inner(slice: &[u16]) -> &WideCStr {
        unsafe { mem::transmute(slice) }
    }

    /// Constructs a `WideStr` from a `u16` nul-terminated string pointer.
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
    pub unsafe fn from_ptr_str<'a>(p: *const u16) -> &'a WideCStr {
        assert!(!p.is_null());
        let mut i: isize = 0;
        while *p.offset(i) != 0 {
            i = i + 1;
        }
        mem::transmute(std::slice::from_raw_parts(p, i as usize + 1))
    }

    /// Constructs a `WideStr` from a `u16` pointer and a length.
    ///
    /// The `len` argument is the number of `u16` elements, **not** the number of bytes, and does
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
    /// result in an invalid `WideCStr`.
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
    pub unsafe fn from_ptr_with_nul<'a>(p: *const u16, len: usize) -> &'a WideCStr {
        assert!(*p.offset(len as isize) == 0);
        mem::transmute(std::slice::from_raw_parts(p, len + 1))
    }

    /// Constructs a `WideCStr` from a slice of `u16` values that has a nul terminator.
    ///
    /// The slice will be scanned for nul values. When a nul value is found, it is treated as the
    /// terminator for the string, and the `WideCStr` slice will be truncated to that nul.
    ///
    /// # Failure
    ///
    /// If there are no no nul values in `slice`, an error is returned.
    pub fn from_slice_with_nul<'a>(slice: &'a [u16]) -> Result<&'a WideCStr, MissingNulError> {
        match slice.iter().position(|x| *x == 0) {
            None => Err(MissingNulError(None)),
            Some(i) => Ok(unsafe { WideCStr::from_slice_with_nul_unchecked(&slice[..i + 1]) }),
        }
    }

    /// Constructs a `WideCStr` from a slice of `u16` values that has a nul terminator. No
    /// checking for nul values is performed.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it can lead to invalid `WideCStr` values when `slice`
    /// is missing a terminating nul value or there are non-terminating interior nul values
    /// in the slice.
    pub unsafe fn from_slice_with_nul_unchecked<'a>(slice: &'a [u16]) -> &'a WideCStr {
        std::mem::transmute(slice)
    }

    /// Copies the wide string to an new owned `WideString`.
    pub fn to_wide_c_string(&self) -> WideCString {
        unsafe { WideCString::from_vec_with_nul_unchecked(self.inner.to_owned()) }
    }

    /// Decodes a wide string to an owned `OsString`.
    ///
    /// This makes a string copy of the `WideCStr`. Since `WideCStr` makes no guarantees that it is
    /// valid UTF-16, there is no guarantee that the resulting `OsString` will be valid data. The
    /// `OsString` will **not** have a nul terminator.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::WideCString;
    /// use std::ffi::OsString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wstr = WideCString::from_str(s).unwrap();
    /// // Create an OsString from the wide string
    /// let osstr = wstr.to_os_string();
    ///
    /// assert_eq!(osstr, OsString::from(s));
    /// ```
    pub fn to_os_string(&self) -> OsString {
        platform::os_from_wide(self.as_slice())
    }

    /// Copies the wide string to a new owned `WideString`.
    ///
    /// The `WideString` will **not** have a nul terminator.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::WideCString;
    /// let wcstr = WideCString::from_str("MyString").unwrap();
    /// // Convert WideCString to a WideString
    /// let wstr = wcstr.to_wide_string();
    ///
    /// // WideCString will have a terminating nul
    /// let wcvec = wcstr.into_vec_with_nul();
    /// assert_eq!(wcvec[wcvec.len()-1], 0);
    /// // The resulting WideString will not have the terminating nul
    /// let wvec = wstr.into_vec();
    /// assert_ne!(wvec[wvec.len()-1], 0);
    /// ```
    pub fn to_wide_string(&self) -> WideString {
        WideString::from_vec(self.as_slice())
    }

    /// Copies the wide string to a `String` if it contains valid UTF-16 data.
    ///
    /// # Failures
    ///
    /// Returns an error if the string contains any invalid UTF-16 data.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::WideCString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wstr = WideCString::from_str(s).unwrap();
    /// // Create a regular string from the wide string
    /// let s2 = wstr.to_string().unwrap();
    ///
    /// assert_eq!(s2, s);
    /// ```
    pub fn to_string(&self) -> Result<String, std::string::FromUtf16Error> {
        String::from_utf16(self.as_slice())
    }

    /// Copies the wide string to a `String`.
    ///
    /// Any non-Unicode sequences are replaced with U+FFFD REPLACEMENT CHARACTER.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use widestring::WideCString;
    /// let s = "MyString";
    /// // Create a wide string from the string
    /// let wstr = WideCString::from_str(s).unwrap();
    /// // Create a regular string from the wide string
    /// let s2 = wstr.to_string_lossy();
    ///
    /// assert_eq!(s2, s);
    /// ```
    pub fn to_string_lossy(&self) -> String {
        String::from_utf16_lossy(self.as_slice())
    }

    /// Converts to a slice of the wide string.
    ///
    /// The slice will **not** include the nul terminator.
    pub fn as_slice(&self) -> &[u16] {
        &self.inner[..self.len()]
    }

    /// Converts to a slice of the wide string, including the nul terminator.
    pub fn as_slice_with_nul(&self) -> &[u16] {
        &self.inner
    }

    /// Returns a raw pointer to the wide string.
    ///
    /// The pointer is valid only as long as the lifetime of this reference.
    pub fn as_ptr(&self) -> *const u16 {
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

    /// Converts a `Box<WideCStr>` into a `WideCString` without copying or allocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use widestring::WideCString;
    ///
    /// let v = vec![102u16, 111u16, 111u16]; // "foo"
    /// let c_string = WideCString::new(v.clone()).unwrap();
    /// let boxed = c_string.into_boxed_wide_c_str();
    /// assert_eq!(boxed.into_wide_c_string(), WideCString::new(v).unwrap());
    /// ```
    pub fn into_wide_c_string(self: Box<WideCStr>) -> WideCString {
        let raw = Box::into_raw(self) as *mut [u16];
        WideCString {
            inner: unsafe { Box::from_raw(raw) },
        }
    }
}

impl std::borrow::Borrow<WideCStr> for WideCString {
    fn borrow(&self) -> &WideCStr {
        &self[..]
    }
}

impl ToOwned for WideCStr {
    type Owned = WideCString;
    fn to_owned(&self) -> WideCString {
        self.to_wide_c_string()
    }
}

impl<'a> From<&'a WideCStr> for std::borrow::Cow<'a, WideCStr> {
    fn from(s: &'a WideCStr) -> std::borrow::Cow<'a, WideCStr> {
        std::borrow::Cow::Borrowed(s)
    }
}

impl AsRef<WideCStr> for WideCStr {
    fn as_ref(&self) -> &WideCStr {
        self
    }
}

impl AsRef<WideCStr> for WideCString {
    fn as_ref(&self) -> &WideCStr {
        self
    }
}

impl AsRef<[u16]> for WideCStr {
    fn as_ref(&self) -> &[u16] {
        self.as_slice()
    }
}

impl AsRef<[u16]> for WideCString {
    fn as_ref(&self) -> &[u16] {
        self.as_slice()
    }
}

impl<'a> From<&'a WideCStr> for Box<WideCStr> {
    fn from(s: &'a WideCStr) -> Box<WideCStr> {
        let boxed: Box<[u16]> = Box::from(s.as_slice_with_nul());
        unsafe { Box::from_raw(Box::into_raw(boxed) as *mut WideCStr) }
    }
}

impl From<Box<WideCStr>> for WideCString {
    #[inline]
    fn from(s: Box<WideCStr>) -> WideCString {
        s.into_wide_c_string()
    }
}

impl From<WideCString> for Box<WideCStr> {
    #[inline]
    fn from(s: WideCString) -> Box<WideCStr> {
        s.into_boxed_wide_c_str()
    }
}

impl Default for Box<WideCStr> {
    fn default() -> Box<WideCStr> {
        let boxed: Box<[u16]> = Box::from([0]);
        unsafe { Box::from_raw(Box::into_raw(boxed) as *mut WideCStr) }
    }
}

impl NulError {
    /// Returns the position of the nul value in the slice that was provided to `WideCString`.
    pub fn nul_position(&self) -> usize {
        self.0
    }

    /// Consumes this error, returning the underlying vector of u16 values which generated the error
    /// in the first place.
    pub fn into_vec(self) -> Vec<u16> {
        self.1
    }
}

impl Into<Vec<u16>> for NulError {
    fn into(self) -> Vec<u16> {
        self.into_vec()
    }
}

impl std::fmt::Display for NulError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "nul value found at position {}", self.0)
    }
}

impl std::error::Error for NulError {
    fn description(&self) -> &str {
        "nul value found"
    }
}

impl MissingNulError {
    /// Consumes this error, returning the underlying vector of `u16` values which generated the
    /// error in the first place.
    pub fn into_vec(self) -> Option<Vec<u16>> {
        self.0
    }
}

impl std::fmt::Display for MissingNulError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "missing terminating nul value")
    }
}

impl std::error::Error for MissingNulError {
    fn description(&self) -> &str {
        "missing terminating nul value"
    }
}
