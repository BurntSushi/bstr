use std::borrow::Cow;
use std::error;
use std::ffi::{OsStr, OsString};
use std::fmt;
use std::iter;
use std::ops;
use std::path::{Path, PathBuf};
use std::ptr;
use std::str;
use std::vec;

use bstr::BStr;
use utf8::{self, Utf8Error};

/// Concatenate the elements given by the iterator together into a single
/// `BString`.
///
/// The elements may be any type that can be cheaply converted into an `&[u8]`.
/// This includes, but is not limited to, `&str`, `&BStr` and `&[u8]` itself.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use bstr;
///
/// let s = bstr::concat(&["foo", "bar", "baz"]);
/// assert_eq!(s, "foobarbaz");
/// ```
#[inline]
pub fn concat<T, I>(
    elements: I,
) -> BString
where T: AsRef<[u8]>,
      I: IntoIterator<Item=T>
{
    let mut dest = BString::new();
    for element in elements {
        dest.push(element);
    }
    dest
}

/// Join the elements given by the iterator with the given separator into a
/// single `BString`.
///
/// Both the separator and the elements may be any type that can be cheaply
/// converted into an `&[u8]`. This includes, but is not limited to,
/// `&str`, `&BStr` and `&[u8]` itself.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use bstr;
///
/// let s = bstr::join(",", &["foo", "bar", "baz"]);
/// assert_eq!(s, "foo,bar,baz");
/// ```
#[inline]
pub fn join<B, T, I>(
    separator: B,
    elements: I,
) -> BString
where B: AsRef<[u8]>,
      T: AsRef<[u8]>,
      I: IntoIterator<Item=T>
{
    let mut it = elements.into_iter();
    let mut dest = BString::new();
    match it.next() {
        None => return dest,
        Some(first) => {
            dest.push(first);
        }
    }
    for element in it {
        dest.push(&separator);
        dest.push(element);
    }
    dest
}

/// A growable byte string that is conventionally UTF-8.
///
/// A `BString` has ownership over its contents and corresponds to
/// a growable or shrinkable buffer. Its borrowed counterpart is a
/// [`BStr`](struct.BStr.html), called a byte string slice.
///
/// # Examples
///
/// You can create a new `BString` from a literal Unicode string or a literal
/// byte string with `BString::from`:
///
/// ```
/// use bstr::BString;
///
/// let s = BString::from("Hello, world!");
/// ```
///
/// You can append bytes, characters or other strings to a `BString`:
///
/// ```
/// use bstr::BString;
///
/// let mut s = BString::from("Hello, ");
/// s.push_byte(b'w');
/// s.push_char('o');
/// s.push("rl");
/// s.push(b"d!");
/// assert_eq!(s, "Hello, world!");
/// ```
///
/// If you have a `String` or a `Vec<u8>`, then you can create a `BString`
/// from it with zero cost:
///
/// ```
/// use bstr::BString;
///
/// let s = BString::from(vec![b'f', b'o', b'o']);
/// let s = BString::from("foo".to_string());
/// ```
///
/// A `BString` can be freely converted back to a `Vec<u8>`:
///
/// ```
/// use bstr::BString;
///
/// let s = BString::from("foo");
/// let vector = s.into_vec();
/// assert_eq!(vector, vec![b'f', b'o', b'o']);
/// ```
///
/// However, converting from a `BString` to a `String` requires UTF-8
/// validation:
///
/// ```
/// use bstr::BString;
///
/// # fn example() -> Result<(), ::bstr::FromUtf8Error> {
/// let bytes = BString::from("hello");
/// let string = bytes.into_string()?;
///
/// assert_eq!("hello", string);
/// # Ok(()) }; example().unwrap()
/// ```
///
/// # UTF-8
///
/// Like byte string slices (`BStr`), a `BString` is only conventionally
/// UTF-8. This is in constrast to the standard library's `String` type, which
/// is guaranteed to be valid UTF-8.
///
/// Because of this relaxation, types such as `Vec<u8>`, `&[u8]`, `String` and
/// `&str` can all be converted to a `BString` (or `BStr`) at zero cost without
/// any validation step.
///
/// Moreover, this relaxation implies that many of the restrictions around
/// mutating a `String` do not apply to `BString`. Namely, if your `BString`
/// is valid UTF-8, then the various methods that mutate the `BString` do not
/// necessarily prevent you from causing the bytes to become invalid UTF-8.
/// For example:
///
/// ```
/// use bstr::{B, BString};
///
/// let mut s = BString::from("hello");
/// s[1] = b'\xFF';
/// // `s` was valid UTF-8, but now it's now.
/// assert_eq!(s, B(b"h\xFFllo"));
/// ```
///
/// # Deref
///
/// The `BString` type implements `Deref` and `DerefMut`, where the target
/// types are `&BStr` and `&mut BStr`, respectively. `Deref` permits all of the
/// methods defined on `BStr` to be implicitly callable on any `BString`.
/// For example, the `contains` method is defined on `BStr` and not `BString`,
/// but values of type `BString` can still use it directly:
///
/// ```
/// use bstr::BString;
///
/// let s = BString::from("foobarbaz");
/// assert!(s.contains("bar"));
/// ```
///
/// For more information about how deref works, see the documentation for the
/// [`std::ops::Deref`](https://doc.rust-lang.org/std/ops/trait.Deref.html)
/// trait.
///
/// # Representation
///
/// A `BString` has the same representation as a `Vec<u8>` and a `String`.
/// That is, it is made up of three word sized components: a pointer to a
/// region of memory containing the bytes, a length and a capacity.
#[derive(Clone, Hash)]
pub struct BString {
    bytes: Vec<u8>,
}

impl BString {
    /// Creates a new empty `BString`.
    ///
    /// Given that the `BString` is empty, this will not allocate any initial
    /// buffer. While that means that this initial operation is very
    /// inexpensive, it may cause excessive allocation later when you add
    /// data. If you have an idea of how much data the `String` will hold,
    /// consider the [`with_capacity`] method to prevent excessive
    /// re-allocation.
    ///
    /// [`with_capacity`]: #method.with_capacity
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let s = BString::new();
    /// ```
    #[inline]
    pub fn new() -> BString {
        BString { bytes: vec![] }
    }

    /// Creates a new empty `BString` with a particular capacity.
    ///
    /// `BString`s have an internal buffer to hold their data. The capacity is
    /// the length of that buffer, and can be queried with the [`capacity`]
    /// method. This method creates an empty `BString`, but one with an initial
    /// buffer that can hold `capacity` bytes. This is useful when you may be
    /// appending a bunch of data to the `BString`, reducing the number of
    /// reallocations it needs to do.
    ///
    /// [`capacity`]: #method.capacity
    ///
    /// If the given capacity is `0`, no allocation will occur, and this method
    /// is identical to the [`new`] method.
    ///
    /// [`new`]: #method.new
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::with_capacity(10);
    ///
    /// // The String contains no chars, even though it has capacity for more
    /// assert_eq!(s.len(), 0);
    ///
    /// // These are all done without reallocating...
    /// let cap = s.capacity();
    /// for i in 0..10 {
    ///     s.push_char('a');
    /// }
    ///
    /// assert_eq!(s.capacity(), cap);
    ///
    /// // ...but this may make the vector reallocate
    /// s.push_char('a');
    /// ```
    #[inline]
    pub fn with_capacity(capacity: usize) -> BString {
        BString { bytes: Vec::with_capacity(capacity) }
    }

    /// Create a new byte string from the given bytes.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let bytes = vec![b'a', b'b', b'c'];
    /// let s = BString::from_vec(bytes);
    /// assert_eq!("abc", s);
    /// ```
    #[inline]
    pub fn from_vec(bytes: Vec<u8>) -> BString {
        BString { bytes }
    }

    /// Create a new byte string by copying the given slice.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let s = BString::from_slice(b"abc");
    /// assert_eq!("abc", s);
    /// ```
    #[inline]
    pub fn from_slice<B: AsRef<[u8]>>(slice: B) -> BString {
        BString::from_vec(slice.as_ref().to_vec())
    }

    /// Create a new byte string from an owned OS string.
    ///
    /// On Unix, this always succeeds and is zero cost. On non-Unix systems,
    /// this returns the original OS string if it is not valid UTF-8.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::ffi::OsString;
    ///
    /// use bstr::BString;
    ///
    /// let os_str = OsString::from("foo");
    /// let bs = BString::from_os_string(os_str).expect("must be valid UTF-8");
    /// assert_eq!(bs, "foo");
    /// ```
    #[inline]
    pub fn from_os_string(os_str: OsString) -> Result<BString, OsString> {
        BString::from_os_string_imp(os_str)
    }

    #[cfg(unix)]
    #[inline]
    fn from_os_string_imp(os_str: OsString) -> Result<BString, OsString> {
        use std::os::unix::ffi::OsStringExt;

        Ok(BString::from(os_str.into_vec()))
    }

    #[cfg(not(unix))]
    #[inline]
    fn from_os_string_imp(os_str: OsString) -> Result<BString, OsString> {
        os_str.into_string().map(BString::from)
    }

    /// Lossily create a new byte string from an OS string slice.
    ///
    /// On Unix, this always succeeds, is zero cost and always returns a slice.
    /// On non-Unix systems, this does a UTF-8 check. If the given OS string
    /// slice is not valid UTF-8, then it is lossily decoded into valid UTF-8
    /// (with invalid bytes replaced by the Unicode replacement codepoint).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::ffi::OsStr;
    ///
    /// use bstr::{B, BString};
    ///
    /// let os_str = OsStr::new("foo");
    /// let bs = BString::from_os_str_lossy(os_str);
    /// assert_eq!(bs, B("foo"));
    /// ```
    #[inline]
    pub fn from_os_str_lossy<'a>(os_str: &'a OsStr) -> Cow<'a, BStr> {
        BString::from_os_str_lossy_imp(os_str)
    }

    #[cfg(unix)]
    #[inline]
    fn from_os_str_lossy_imp<'a>(os_str: &'a OsStr) -> Cow<'a, BStr> {
        use std::os::unix::ffi::OsStrExt;

        Cow::Borrowed(BStr::new(os_str.as_bytes()))
    }

    #[cfg(not(unix))]
    #[inline]
    fn from_os_str_lossy_imp<'a>(os_str: &'a OsStr) -> Cow<'a, BStr> {
        match os_str.to_string_lossy() {
            Cow::Borrowed(x) => Cow::Borrowed(BStr::new(x)),
            Cow::Owned(x) => Cow::Owned(BString::from(x)),
        }
    }

    /// Create a new byte string from an owned file path.
    ///
    /// On Unix, this always succeeds and is zero cost. On non-Unix systems,
    /// this returns the original path if it is not valid UTF-8.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::path::PathBuf;
    ///
    /// use bstr::BString;
    ///
    /// let path = PathBuf::from("foo");
    /// let bs = BString::from_path_buf(path).expect("must be valid UTF-8");
    /// assert_eq!(bs, "foo");
    /// ```
    #[inline]
    pub fn from_path_buf(path: PathBuf) -> Result<BString, PathBuf> {
        BString::from_os_string(path.into_os_string())
            .map_err(PathBuf::from)
    }

    /// Lossily create a new byte string from a file path.
    ///
    /// On Unix, this always succeeds, is zero cost and always returns a slice.
    /// On non-Unix systems, this does a UTF-8 check. If the given path is not
    /// valid UTF-8, then it is lossily decoded into valid UTF-8 (with invalid
    /// bytes replaced by the Unicode replacement codepoint).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::path::Path;
    ///
    /// use bstr::{B, BString};
    ///
    /// let path = Path::new("foo");
    /// let bs = BString::from_path_lossy(path);
    /// assert_eq!(bs, B("foo"));
    /// ```
    #[inline]
    pub fn from_path_lossy<'a>(path: &'a Path) -> Cow<'a, BStr> {
        BString::from_os_str_lossy(path.as_os_str())
    }

    /// Appends the given byte to the end of this byte string.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("abc");
    /// s.push_byte(b'\xE2');
    /// s.push_byte(b'\x98');
    /// s.push_byte(b'\x83');
    /// assert_eq!("abc☃", s);
    /// ```
    #[inline]
    pub fn push_byte(&mut self, byte: u8) {
        self.bytes.push(byte);
    }

    /// Appends the given `char` to the end of this byte string.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("abc");
    /// s.push_char('1');
    /// s.push_char('2');
    /// s.push_char('3');
    /// assert_eq!("abc123", s);
    /// ```
    #[inline]
    pub fn push_char(&mut self, ch: char) {
        if ch.len_utf8() == 1 {
            self.bytes.push(ch as u8);
            return;
        }
        self.bytes.extend_from_slice(ch.encode_utf8(&mut [0; 4]).as_bytes());
    }

    /// Appends the given slice to the end of this byte string. This accepts
    /// any type that be converted to a `&[u8]`. This includes, but is not
    /// limited to, `&str`, `&BStr`, and of course, `&[u8]` itself.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("abc");
    /// s.push(b"123");
    /// assert_eq!("abc123", s);
    /// ```
    #[inline]
    pub fn push<B: AsRef<[u8]>>(&mut self, bytes: B) {
        self.bytes.extend_from_slice(bytes.as_ref());
    }

    /// Extracts a byte string slice containing the entire `BString`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{BStr, BString};
    ///
    /// let s = BString::from("foo");
    ///
    /// assert_eq!(BStr::new("foo"), s.as_bstr());
    /// ```
    #[inline]
    pub fn as_bstr(&self) -> &BStr {
        BStr::from_bytes(&self.bytes)
    }

    /// Returns this `BString` as a borrowed byte vector.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let bs = BString::from("ab");
    /// assert!(bs.as_vec().capacity() >= 2);
    /// ```
    #[inline]
    pub fn as_vec(&self) -> &Vec<u8> {
        &self.bytes
    }

    /// Converts a `BString` into a mutable string slice.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("foobar");
    /// let s_mut_str = s.as_mut_bstr();
    ///
    /// s_mut_str[0] = b'F';
    ///
    /// assert_eq!("Foobar", s_mut_str);
    /// ```
    #[inline]
    pub fn as_mut_bstr(&mut self) -> &mut BStr {
        BStr::from_bytes_mut(&mut self.bytes)
    }

    /// Returns this `BString` as a mutable byte vector.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut bs = BString::from("ab");
    /// bs.as_mut_vec().push(b'c');
    /// assert_eq!("abc", bs);
    /// ```
    #[inline]
    pub fn as_mut_vec(&mut self) -> &mut Vec<u8> {
        &mut self.bytes
    }

    /// Converts a `BString` into a byte vector.
    ///
    /// This consumes the `BString`, and thus the contents are not copied.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let s = BString::from("hello");
    /// let bytes = s.into_vec();
    ///
    /// assert_eq!(vec![104, 101, 108, 108, 111], &bytes[..]);
    /// ```
    #[inline]
    pub fn into_vec(self) -> Vec<u8> {
        self.bytes
    }

    /// Converts a `BString` into a `String` if and only if this byte string is
    /// valid UTF-8.
    ///
    /// If it is not valid UTF-8, then the error `std::string::FromUtf8Error`
    /// is returned. (This error can be used to examine why UTF-8 validation
    /// failed, or to regain the original byte string.)
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// # fn example() -> Result<(), ::bstr::FromUtf8Error> {
    /// let bytes = BString::from("hello");
    /// let string = bytes.into_string()?;
    ///
    /// assert_eq!("hello", string);
    /// # Ok(()) }; example().unwrap()
    /// ```
    ///
    /// If this byte string is not valid UTF-8, then an error will be returned.
    /// That error can then be used to inspect the location at which invalid
    /// UTF-8 was found, or to regain the original byte string:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let bytes = BString::from_slice(b"foo\xFFbar");
    /// let err = bytes.into_string().unwrap_err();
    ///
    /// assert_eq!(err.utf8_error().valid_up_to(), 3);
    /// assert_eq!(err.utf8_error().error_len(), Some(1));
    ///
    /// // At no point in this example is an allocation performed.
    /// let bytes = BString::from(err.into_bstring());
    /// assert_eq!(bytes, B(b"foo\xFFbar"));
    /// ```
    #[inline]
    pub fn into_string(self) -> Result<String, FromUtf8Error> {
        match utf8::validate(self.as_bytes()) {
            Err(err) => {
                Err(FromUtf8Error { original: self, err: err })
            }
            Ok(()) => {
                // SAFETY: This is safe because of the guarantees provided by
                // utf8::validate.
                unsafe { Ok(self.into_string_unchecked()) }
            }
        }
    }

    /// Lossily converts a `BString` into a `String`. If this byte string
    /// contains invalid UTF-8, then the invalid bytes are replaced with the
    /// Unicode replacement codepoint.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let bytes = BString::from_slice(b"foo\xFFbar");
    /// let string = bytes.into_string_lossy();
    /// assert_eq!(string, "foo\u{FFFD}bar");
    /// ```
    #[inline]
    pub fn into_string_lossy(self) -> String {
        self.to_string()
    }

    /// Unsafely convert this byte string into a `String`, without checking for
    /// valid UTF-8.
    ///
    /// # Safety
    ///
    /// Callers *must* ensure that this byte string is valid UTF-8 before
    /// calling this method. Converting a byte string into a `String` that is
    /// not valid UTF-8 is considered undefined behavior.
    ///
    /// This routine is useful in performance sensitive contexts where the
    /// UTF-8 validity of the byte string is already known and it is
    /// undesirable to pay the cost of an additional UTF-8 validation check
    /// that [`into_string`](#method.into_string) performs.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// // SAFETY: This is safe because string literals are guaranteed to be
    /// // valid UTF-8 by the Rust compiler.
    /// let s = unsafe { BString::from("☃βツ").into_string_unchecked() };
    /// assert_eq!("☃βツ", s);
    /// ```
    pub unsafe fn into_string_unchecked(self) -> String {
        String::from_utf8_unchecked(self.into_vec())
    }

    /// Converts this byte string into an OS string, in place.
    ///
    /// On Unix, this always succeeds and is zero cost. On non-Unix systems,
    /// this returns the original byte string if it is not valid UTF-8.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::ffi::OsStr;
    ///
    /// use bstr::BString;
    ///
    /// let bs = BString::from("foo");
    /// let os_str = bs.into_os_string().expect("should be valid UTF-8");
    /// assert_eq!(os_str, OsStr::new("foo"));
    /// ```
    #[inline]
    pub fn into_os_string(self) -> Result<OsString, BString> {
        self.into_os_string_imp()
    }

    #[cfg(unix)]
    #[inline]
    fn into_os_string_imp(self) -> Result<OsString, BString> {
        use std::os::unix::ffi::OsStringExt;

        Ok(OsString::from_vec(self.into_vec()))
    }

    #[cfg(not(unix))]
    #[inline]
    fn into_os_string_imp(self) -> Result<OsString, BString> {
        match self.into_string() {
            Ok(s) => Ok(OsString::from(s)),
            Err(err) => Err(err.into_bstring()),
        }
    }

    /// Lossily converts this byte string into an OS string, in place.
    ///
    /// On Unix, this always succeeds and is zero cost. On non-Unix systems,
    /// this will perform a UTF-8 check and lossily convert this byte string
    /// into valid UTF-8 using the Unicode replacement codepoint.
    ///
    /// Note that this can prevent the correct roundtripping of file paths on
    /// non-Unix systems such as Windows, where file paths are an arbitrary
    /// sequence of 16-bit integers.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let bs = BString::from_slice(b"foo\xFFbar");
    /// let os_str = bs.into_os_string_lossy();
    /// assert_eq!(os_str.to_string_lossy(), "foo\u{FFFD}bar");
    /// ```
    #[inline]
    pub fn into_os_string_lossy(self) -> OsString {
        self.into_os_string_lossy_imp()
    }

    #[cfg(unix)]
    #[inline]
    fn into_os_string_lossy_imp(self) -> OsString {
        use std::os::unix::ffi::OsStringExt;

        OsString::from_vec(self.into_vec())
    }

    #[cfg(not(unix))]
    #[inline]
    fn into_os_string_lossy_imp(self) -> OsString {
        OsString::from(self.into_string_lossy())
    }

    /// Converts this byte string into an owned file path, in place.
    ///
    /// On Unix, this always succeeds and is zero cost. On non-Unix systems,
    /// this returns the original byte string if it is not valid UTF-8.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let bs = BString::from("foo");
    /// let path = bs.into_path_buf().expect("should be valid UTF-8");
    /// assert_eq!(path.as_os_str(), "foo");
    /// ```
    #[inline]
    pub fn into_path_buf(self) -> Result<PathBuf, BString> {
        self.into_os_string().map(PathBuf::from)
    }

    /// Lossily converts this byte string into an owned file path, in place.
    ///
    /// On Unix, this always succeeds and is zero cost. On non-Unix systems,
    /// this will perform a UTF-8 check and lossily convert this byte string
    /// into valid UTF-8 using the Unicode replacement codepoint.
    ///
    /// Note that this can prevent the correct roundtripping of file paths on
    /// non-Unix systems such as Windows, where file paths are an arbitrary
    /// sequence of 16-bit integers.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let bs = BString::from_slice(b"foo\xFFbar");
    /// let path = bs.into_path_buf_lossy();
    /// assert_eq!(path.to_string_lossy(), "foo\u{FFFD}bar");
    /// ```
    #[inline]
    pub fn into_path_buf_lossy(self) -> PathBuf {
        PathBuf::from(self.into_os_string_lossy())
    }

    /// Converts this `BString` into a `Box<BStr>`.
    ///
    /// This will drop any excess capacity.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let s = BString::from("foobar");
    /// let b = s.into_boxed_bstr();
    /// assert_eq!(6, b.len());
    /// ```
    #[inline]
    pub fn into_boxed_bstr(self) -> Box<BStr> {
        unsafe {
            let slice = self.bytes.into_boxed_slice();
            Box::from_raw(Box::into_raw(slice) as *mut BStr)
        }
    }

    /// Returns this byte string's capacity, in bytes.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let s = BString::with_capacity(10);
    /// assert_eq!(10, s.capacity());
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.bytes.capacity()
    }

    /// Truncates this byte string, removing all contents.
    ///
    /// The resulting byte string will always have length `0`, but its capacity
    /// remains unchanged.
    #[inline]
    pub fn clear(&mut self) {
        self.bytes.clear();
    }

    /// Ensures that this `BString`'s capacity is at least `additional`
    /// bytes larger than its length.
    ///
    /// The capacity may be increased by more than `additional` bytes if it
    /// chooses, to prevent frequent reallocations.
    ///
    /// If you do not want this "at least" behavior, use the
    /// [`reserve_exact`](#method.reserve_exact) method instead.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::new();
    /// s.reserve(10);
    /// assert!(s.capacity() >= 10);
    /// ```
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.bytes.reserve(additional);
    }

    /// Ensures that this `BString`'s capacity is exactly `additional`
    /// bytes larger than its length.
    ///
    /// Consider using the [`reserve`](#method.reserve) method unless you
    /// absolutely know better than the allocator.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::new();
    /// s.reserve_exact(10);
    /// assert!(s.capacity() >= 10);
    /// ```
    #[inline]
    pub fn reserve_exact(&mut self, additional: usize) {
        self.bytes.reserve_exact(additional);
    }

    /// Shrinks the capacity of this `BString` to match its length.
    ///
    /// Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("foo");
    /// s.reserve(10);
    /// assert!(s.capacity() >= 10);
    /// s.shrink_to_fit();
    /// assert_eq!(3, s.capacity());
    /// ```
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.bytes.shrink_to_fit();
    }

    /// Shortens this `BString` to the specified length, in bytes.
    ///
    /// If `new_len` is greater than or equal to this byte string's current
    /// length, then this has no effect.
    ///
    /// Note that this does _not_ panic if the result is not on a valid
    /// `char` boundary.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("foobar");
    /// s.truncate(3);
    /// assert_eq!("foo", s);
    /// ```
    #[inline]
    pub fn truncate(&mut self, new_len: usize) {
        if new_len < self.len() {
            self.bytes.truncate(new_len);
        }
    }

    /// Resizes this byte string in place so that the length of this byte
    /// string is equivalent to `new_len`.
    ///
    /// If `new_len` is greater than the length of this byte string, then
    /// the byte string is extended by the difference, which each additional
    /// byte filled with the given value. If `new_len` is less than the length
    /// of this byte string, then it is simply truncated.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("f");
    /// s.resize(3, b'o');
    /// assert_eq!(s, "foo");
    /// s.resize(1, b'o');
    /// assert_eq!(s, "f");
    /// ```
    #[inline]
    pub fn resize(&mut self, new_len: usize, value: u8) {
        self.bytes.resize(new_len, value);
    }

    /// Removes the last codepoint from this `BString` and returns it.
    ///
    /// If this byte string is empty, then `None` is returned. If the last
    /// bytes of this byte string do not correspond to a valid UTF-8 code unit
    /// sequence, then the Unicode replacement codepoint is yielded instead in
    /// accordance with the
    /// [replacement codepoint substitution policy](index.html#handling-of-invalid-utf8-8).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("foo");
    /// assert_eq!(s.pop_char(), Some('o'));
    /// assert_eq!(s.pop_char(), Some('o'));
    /// assert_eq!(s.pop_char(), Some('f'));
    /// assert_eq!(s.pop_char(), None);
    /// ```
    ///
    /// This shows the replacement codepoint substitution policy. Note that
    /// the first pop yields a replacement codepoint but actually removes two
    /// bytes. This is in contrast with subsequent pops when encountering
    /// `\xFF` since `\xFF` is never a valid prefix for any valid UTF-8
    /// code unit sequence.
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from_slice(b"f\xFF\xFF\xFFoo\xE2\x98");
    /// assert_eq!(s.pop_char(), Some('\u{FFFD}'));
    /// assert_eq!(s.pop_char(), Some('o'));
    /// assert_eq!(s.pop_char(), Some('o'));
    /// assert_eq!(s.pop_char(), Some('\u{FFFD}'));
    /// assert_eq!(s.pop_char(), Some('\u{FFFD}'));
    /// assert_eq!(s.pop_char(), Some('\u{FFFD}'));
    /// assert_eq!(s.pop_char(), Some('f'));
    /// assert_eq!(s.pop_char(), None);
    /// ```
    #[inline]
    pub fn pop_char(&mut self) -> Option<char> {
        let (ch, size) = utf8::decode_last_lossy(self.as_bytes());
        if size == 0 {
            return None;
        }
        let new_len = self.len() - size;
        self.truncate(new_len);
        Some(ch)
    }

    /// Removes the last byte from this `BString` and returns it.
    ///
    /// If this byte string is empty, then `None` is returned.
    ///
    /// Note that if the last codepoint in this byte string is not ASCII, then
    /// removing the last byte could make this byte string contain invalid
    /// UTF-8.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("foo");
    /// assert_eq!(s.pop_byte(), Some(b'o'));
    /// assert_eq!(s.pop_byte(), Some(b'o'));
    /// assert_eq!(s.pop_byte(), Some(b'f'));
    /// assert_eq!(s.pop_byte(), None);
    /// ```
    #[inline]
    pub fn pop_byte(&mut self) -> Option<u8> {
        self.bytes.pop()
    }

    /// **DEPRECATED**: Use
    /// [`pop_char`](struct.BString.html#method.pop_char)
    /// or
    /// [`pop_byte`](struct.BString.html#method.pop_byte)
    /// instead.
    ///
    /// Removes the last codepoint from this `BString` and returns it.
    ///
    /// If this byte string is empty, then `None` is returned. If the last
    /// bytes of this byte string do not correspond to a valid UTF-8 code unit
    /// sequence, then the Unicode replacement codepoint is yielded instead in
    /// accordance with the
    /// [replacement codepoint substitution policy](index.html#handling-of-invalid-utf8-8).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("foo");
    /// assert_eq!(s.pop(), Some('o'));
    /// assert_eq!(s.pop(), Some('o'));
    /// assert_eq!(s.pop(), Some('f'));
    /// assert_eq!(s.pop(), None);
    /// ```
    ///
    /// This shows the replacement codepoint substitution policy. Note that
    /// the first pop yields a replacement codepoint but actually removes two
    /// bytes. This is in contrast with subsequent pops when encountering
    /// `\xFF` since `\xFF` is never a valid prefix for any valid UTF-8
    /// code unit sequence.
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from_slice(b"f\xFF\xFF\xFFoo\xE2\x98");
    /// assert_eq!(s.pop(), Some('\u{FFFD}'));
    /// assert_eq!(s.pop(), Some('o'));
    /// assert_eq!(s.pop(), Some('o'));
    /// assert_eq!(s.pop(), Some('\u{FFFD}'));
    /// assert_eq!(s.pop(), Some('\u{FFFD}'));
    /// assert_eq!(s.pop(), Some('\u{FFFD}'));
    /// assert_eq!(s.pop(), Some('f'));
    /// assert_eq!(s.pop(), None);
    /// ```
    #[deprecated(since = "0.1.1", note = "use pop_char or pop_byte instead")]
    #[inline]
    pub fn pop(&mut self) -> Option<char> {
        self.pop_char()
    }

    /// Removes a `char` from this `BString` at the given byte position and
    /// returns it.
    ///
    /// If the bytes at the given position do not lead to a valid UTF-8 code
    /// unit sequence, then a
    /// [replacement codepoint is returned instead](index.html#handling-of-invalid-utf8-8).
    ///
    /// # Panics
    ///
    /// Panics if `at` is larger than or equal to this byte string's length.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("foo☃bar");
    /// assert_eq!('☃', s.remove(3));
    /// assert_eq!("foobar", s);
    /// ```
    ///
    /// This example shows how the Unicode replacement codepoint policy is
    /// used:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from_slice(b"foo\xFFbar");
    /// assert_eq!('\u{FFFD}', s.remove(3));
    /// assert_eq!("foobar", s);
    /// ```
    #[inline]
    pub fn remove(&mut self, at: usize) -> char {
        let (ch, size) = utf8::decode_lossy(self[at..].as_bytes());
        assert!(size > 0, "expected {} to be less than {}", at, self.len());
        self.bytes.drain(at..at + size);
        ch
    }

    /// Inserts the given codepoint into this `BString` at a particular byte
    /// position.
    ///
    /// This is an `O(n)` operation as it may copy a number of elements in this
    /// byte string proportional to its length.
    ///
    /// # Panics
    ///
    /// Panics if `at` is larger than the byte string's length.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("foobar");
    /// s.insert_char(3, '☃');
    /// assert_eq!("foo☃bar", s);
    /// ```
    #[inline]
    pub fn insert_char(&mut self, at: usize, ch: char) {
        self.insert(at, ch.encode_utf8(&mut [0; 4]).as_bytes());
    }

    /// Inserts the given byte string into this byte string at a particular
    /// byte position.
    ///
    /// This is an `O(n)` operation as it may copy a number of elements in this
    /// byte string proportional to its length.
    ///
    /// Note that the type parameter `B` on this method means that it can
    /// accept anything that can be cheaply converted to a `&[u8]`. This
    /// includes, but is not limited to, `&str`, `&BStr` and `&[u8]` itself.
    ///
    /// # Panics
    ///
    /// Panics if `at` is larger than the byte string's length.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("foobar");
    /// s.insert(3, "☃☃☃");
    /// assert_eq!("foo☃☃☃bar", s);
    /// ```
    #[inline]
    pub fn insert<B: AsRef<[u8]>>(&mut self, at: usize, bytes: B) {
        assert!(at <= self.len(), "expected {} to be <= {}", at, self.len());

        let bytes = bytes.as_ref();
        let len = self.len();

        // SAFETY: We'd like to efficiently splice in the given bytes into
        // this byte string. Since we are only working with `u8` elements here,
        // we only need to consider whether our bounds are correct and whether
        // our byte string has enough space.
        self.reserve(bytes.len());
        unsafe {
            // Shift bytes after `at` over by the length of `bytes` to make
            // room for it. This requires referencing two regions of memory
            // that may overlap, so we use ptr::copy.
            ptr::copy(
                self.bytes.as_ptr().add(at),
                self.bytes.as_mut_ptr().add(at + bytes.len()),
                len - at,
            );
            // Now copy the bytes given into the room we made above. In this
            // case, we know that the given bytes cannot possibly overlap
            // with this byte string since we have a mutable borrow of the
            // latter. Thus, we can use a nonoverlapping copy.
            ptr::copy_nonoverlapping(
                bytes.as_ptr(),
                self.bytes.as_mut_ptr().add(at),
                bytes.len(),
            );
            self.bytes.set_len(len + bytes.len());
        }
    }

    /// Splits this `BString` into two separate byte strings at the given
    /// index.
    ///
    /// This returns a newly allocated `BString`, while `self` retans bytes
    /// `[0, at)` and the returned `BString` contains bytes `[at, len)`.
    ///
    /// The capacity of `self` does not change.
    ///
    /// # Panics
    ///
    /// Panics if `at` is beyond the end of this byte string.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("foobar");
    /// let bar = s.split_off(3);
    /// assert_eq!(s, "foo");
    /// assert_eq!(bar, "bar");
    /// ```
    #[inline]
    pub fn split_off(&mut self, at: usize) -> BString {
        BString::from(self.bytes.split_off(at))
    }

    /// Removes the specified range in this byte string and replaces it with
    /// the given bytes. The given bytes do not need to have the same length
    /// as the range provided.
    ///
    /// # Panics
    ///
    /// Panics if the given range is invalid.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("foobar");
    /// s.replace_range(2..4, "xxxxx");
    /// assert_eq!(s, "foxxxxxar");
    /// ```
    #[inline]
    pub fn replace_range<R, B>(
        &mut self,
        range: R,
        replace_with: B,
    ) where R: ops::RangeBounds<usize>,
            B: AsRef<[u8]>
    {
        self.bytes.splice(range, replace_with.as_ref().iter().cloned());
    }

    /// Creates a draining iterator that removes the specified range in this
    /// `BString` and yields each of the removed bytes.
    ///
    /// Note that the elements specified by the given range are removed
    /// regardless of whether the returned iterator is fully exhausted.
    ///
    /// Also note that is is unspecified how many bytes are removed from the
    /// `BString` if the `DrainBytes` iterator is leaked.
    ///
    /// # Panics
    ///
    /// Panics if the given range is not valid.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("foobar");
    /// {
    ///     let mut drainer = s.drain_bytes(2..4);
    ///     assert_eq!(drainer.next(), Some(b'o'));
    ///     assert_eq!(drainer.next(), Some(b'b'));
    ///     assert_eq!(drainer.next(), None);
    /// }
    /// assert_eq!(s, "foar");
    /// ```
    #[inline]
    pub fn drain_bytes<R>(
        &mut self,
        range: R,
    ) -> DrainBytes
    where R: ops::RangeBounds<usize>
    {
        DrainBytes { it: self.bytes.drain(range) }
    }
}

/// A draining byte oriented iterator for `BString`.
///
/// This iterator is created by
/// [`BString::drain`](struct.BString.html#method.drain).
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use bstr::BString;
///
/// let mut s = BString::from("foobar");
/// {
///     let mut drainer = s.drain_bytes(2..4);
///     assert_eq!(drainer.next(), Some(b'o'));
///     assert_eq!(drainer.next(), Some(b'b'));
///     assert_eq!(drainer.next(), None);
/// }
/// assert_eq!(s, "foar");
/// ```
#[derive(Debug)]
pub struct DrainBytes<'a> {
    it: vec::Drain<'a, u8>,
}

impl<'a> iter::FusedIterator for DrainBytes<'a> {}

impl<'a> Iterator for DrainBytes<'a> {
    type Item = u8;

    #[inline]
    fn next(&mut self) -> Option<u8> {
        self.it.next()
    }
}

impl<'a> DoubleEndedIterator for DrainBytes<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<u8> {
        self.it.next_back()
    }
}

impl<'a> ExactSizeIterator for DrainBytes<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.it.len()
    }
}

/// An error that may occur when converting a `BString` to a `String`.
///
/// This error includes the original `BString` that failed to convert to a
/// `String`. This permits callers to recover the allocation used even if it
/// it not valid UTF-8.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use bstr::{B, BString};
///
/// let bytes = BString::from_slice(b"foo\xFFbar");
/// let err = bytes.into_string().unwrap_err();
///
/// assert_eq!(err.utf8_error().valid_up_to(), 3);
/// assert_eq!(err.utf8_error().error_len(), Some(1));
///
/// // At no point in this example is an allocation performed.
/// let bytes = BString::from(err.into_bstring());
/// assert_eq!(bytes, B(b"foo\xFFbar"));
/// ```
#[derive(Debug, Eq, PartialEq)]
pub struct FromUtf8Error {
    original: BString,
    err: Utf8Error,
}

impl FromUtf8Error {
    /// Return the original bytes as a slice that failed to convert to a
    /// `String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let bytes = BString::from_slice(b"foo\xFFbar");
    /// let err = bytes.into_string().unwrap_err();
    ///
    /// // At no point in this example is an allocation performed.
    /// assert_eq!(err.as_bstr(), B(b"foo\xFFbar"));
    /// ```
    #[inline]
    pub fn as_bstr(&self) -> &BStr {
        &self.original
    }

    /// Consume this error and return the original byte string that failed to
    /// convert to a `String`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let bytes = BString::from_slice(b"foo\xFFbar");
    /// let err = bytes.into_string().unwrap_err();
    /// let original = err.into_bstring();
    ///
    /// // At no point in this example is an allocation performed.
    /// assert_eq!(original, B(b"foo\xFFbar"));
    /// ```
    #[inline]
    pub fn into_bstring(self) -> BString {
        self.original
    }

    /// Return the underlying UTF-8 error that occurred. This error provides
    /// information on the nature and location of the invalid UTF-8 detected.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let bytes = BString::from_slice(b"foo\xFFbar");
    /// let err = bytes.into_string().unwrap_err();
    ///
    /// assert_eq!(err.utf8_error().valid_up_to(), 3);
    /// assert_eq!(err.utf8_error().error_len(), Some(1));
    /// ```
    #[inline]
    pub fn utf8_error(&self) -> &Utf8Error {
        &self.err
    }
}

impl error::Error for FromUtf8Error {
    #[inline]
    fn description(&self) -> &str { "invalid UTF-8 vector" }
}

impl fmt::Display for FromUtf8Error {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.err)
    }
}

#[cfg(test)]
mod tests {
    use bstr::B;
    use super::*;

    #[test]
    fn insert() {
        let mut s = BString::new();
        s.insert(0, "foo");
        assert_eq!("foo", s);

        let mut s = BString::from("a");
        s.insert(0, "foo");
        assert_eq!("fooa", s);

        let mut s = BString::from("a");
        s.insert(1, "foo");
        assert_eq!("afoo", s);

        let mut s = BString::from("foobar");
        s.insert(3, "quux");
        assert_eq!("fooquuxbar", s);

        let mut s = BString::from("foobar");
        s.insert(3, "x");
        assert_eq!("fooxbar", s);

        let mut s = BString::from("foobar");
        s.insert(0, "x");
        assert_eq!("xfoobar", s);

        let mut s = BString::from("foobar");
        s.insert(6, "x");
        assert_eq!("foobarx", s);

        let mut s = BString::from("foobar");
        s.insert(3, "quuxbazquux");
        assert_eq!("fooquuxbazquuxbar", s);
    }

    #[test]
    #[should_panic]
    fn insert_fail1() {
        let mut s = BString::new();
        s.insert(1, "foo");
    }

    #[test]
    #[should_panic]
    fn insert_fail2() {
        let mut s = BString::from("a");
        s.insert(2, "foo");
    }

    #[test]
    #[should_panic]
    fn insert_fail3() {
        let mut s = BString::from("foobar");
        s.insert(7, "foo");
    }

    #[test]
    fn collect() {
        let s: BString = vec!['a', 'b', 'c'].into_iter().collect();
        assert_eq!(s, "abc");

        let s: BString = vec!["a", "b", "c"].into_iter().collect();
        assert_eq!(s, "abc");

        let s: BString = vec![B("a"), B("b"), B("c")].into_iter().collect();
        assert_eq!(s, "abc");
    }
}
