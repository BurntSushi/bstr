#[cfg(feature = "std")]
use std::borrow::Cow;
#[cfg(feature = "std")]
use std::ffi::OsStr;
#[cfg(feature = "std")]
use std::iter;
#[cfg(feature = "std")]
use std::path::Path;

use core::cmp;
use core::mem;
use core::ops;
use core::ptr;
use core::slice;
use core::str;

use memchr::{memchr, memrchr};

use ascii;
#[cfg(feature = "std")]
use bstring::BString;
use search::{PrefilterState, TwoWay};
use slice_index::SliceIndex;
#[cfg(feature = "unicode")]
use unicode::{
    Graphemes, GraphemeIndices,
    Sentences, SentenceIndices,
    Words, WordIndices, WordsWithBreaks, WordsWithBreakIndices,
    whitespace_len_fwd, whitespace_len_rev,
};
use utf8::{self, Chars, CharIndices, Utf8Error};

/// A short-hand constructor for building a `&BStr`.
///
/// This idiosyncratic constructor is useful for concisely building byte string
/// slices. Its primary utility is in conveniently writing byte string literals
/// in a uniform way. For example, consider this code that does not compile:
///
/// ```ignore
/// let strs = vec![b"a", b"xy"];
/// ```
///
/// The above code doesn't compile because the type of the byte string literal
/// `b"a"` is `&'static [u8; 1]`, and the type of `b"xy"` is
/// `&'static [u8; 2]`. Since their types aren't the same, they can't be stored
/// in the same `Vec`. (This is dissimilar from normal Unicode string slices,
/// where both `"a"` and `"xy"` have the same type of `&'static str`.)
///
/// One way of getting the above code to compile is to convert byte strings to
/// slices. You might try this:
///
/// ```ignore
/// let strs = vec![&b"a", &b"xy"];
/// ```
///
/// But this just creates values with type `& &'static [u8; 1]` and
/// `& &'static [u8; 2]`. Instead, you need to force the issue like so:
///
/// ```
/// let strs = vec![&b"a"[..], &b"xy"[..]];
/// // or
/// let strs = vec![b"a".as_ref(), b"xy".as_ref()];
/// ```
///
/// But neither of these are particularly convenient to type, especially when
/// it's something as common as a string literal. Thus, this constructor
/// permits writing the following instead:
///
/// ```
/// use bstr::B;
///
/// let strs = vec![B("a"), B(b"xy")];
/// ```
///
/// Notice that this also lets you mix and match both string literals and byte
/// string literals. This can be quite convenient!
#[allow(non_snake_case)]
#[inline]
pub fn B<'a, B: ?Sized + AsRef<[u8]>>(bytes: &'a B) -> &'a BStr {
    BStr::new(bytes.as_ref())
}

/// A byte string slice that is conventionally UTF-8.
///
/// A byte string slice is the core string type in this library, and is usually
/// seen in its borrowed form, `&BStr`. The principle difference between a
/// `&BStr` and a `&str` (Rust's standard Unicode string slice) is that a
/// `&BStr` is only *conventionally* UTF-8, where as a `&str` is guaranteed to
/// always be valid UTF-8.
///
/// If you need ownership or a growable byte string buffer, then use
/// [`BString`](struct.BString.html).
///
/// # Literals
///
/// A byte string literal has type `&'static BStr`. The most convenient way to
/// write a byte string literal is by using the short-hand [`B`](fn.B.html)
/// constructor function:
///
/// ```
/// use bstr::{B, BStr};
///
/// // A byte string literal can be constructed from a normal Unicode string.
/// let s = B("a byte string literal");
/// // A byte string literal can also be constructed from a Rust byte string.
/// let s = B(b"another byte string literal");
///
/// // BStr::new can also be used:
/// let s = BStr::new("a byte string literal");
/// let s = BStr::new(b"another byte string literal");
/// ```
///
/// # Representation
///
/// A `&BStr` has the same representation as a `&str`. That is, a `&BStr` is
/// a fat pointer which consists of a pointer to some bytes and a length.
///
/// # Trait implementations
///
/// The `BStr` type has a number of trait implementations, and in particular,
/// defines equality and ordinal comparisons between `&BStr`, `&str` and
/// `&[u8]` for convenience.
///
/// The `Debug` implementation for `BStr` shows its bytes as a normal string.
/// For invalid UTF-8, hex escape sequences are used.
///
/// The `Display` implementation behaves as if `BStr` were first lossily
/// converted to a `str`. Invalid UTF-8 bytes are substituted with the Unicode
/// replacement codepoint, which looks like this: �.
///
/// # Indexing and slicing
///
/// A `BStr` implements indexing and slicing using `[..]` notation. Unlike
/// the standard `str` type, the `BStr` type permits callers to index
/// individual bytes. For example:
///
/// ```
/// use bstr::B;
///
/// let s = B("foo☃bar");
/// assert_eq!(&s[0..3], "foo");
/// assert_eq!(s[2], b'o');
/// assert_eq!(&s[3..6], "☃");
///
/// // Nothing stops you from indexing or slicing invalid UTF-8.
/// assert_eq!(s[3], b'\xE2');
/// assert_eq!(&s[3..5], B(b"\xE2\x98"));
/// ```
#[derive(Hash)]
pub struct BStr {
    bytes: [u8],
}

impl BStr {
    /// Create a byte string slice from anything that can be borrowed as a
    /// sequence of bytes. This includes, but is not limited to, `&Vec<u8>`,
    /// `&[u8]`, `&String` and `&str`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BStr;
    ///
    /// assert_eq!("abc", BStr::new("abc"));
    /// assert_eq!("abc", BStr::new(b"abc"));
    /// ```
    #[inline]
    pub fn new<B: ?Sized + AsRef<[u8]>>(bytes: &B) -> &BStr {
        BStr::from_bytes(bytes.as_ref())
    }

    /// Create a mutable byte string slice from anything that can be borrowed
    /// as a sequence of bytes. This includes, but is not limited to, `&mut
    /// Vec<u8>` and `&mut [u8]`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BStr;
    ///
    /// assert_eq!("abc", BStr::new("abc"));
    /// assert_eq!("abc", BStr::new(b"abc"));
    /// ```
    #[inline]
    pub fn new_mut<B: ?Sized + AsMut<[u8]>>(bytes: &mut B) -> &mut BStr {
        BStr::from_bytes_mut(bytes.as_mut())
    }

    /// Create an immutable byte string slice from an immutable byte slice.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BStr;
    ///
    /// let bytes = &[b'a'];
    /// let bs = BStr::from_bytes(bytes);
    /// assert_eq!("a", bs);
    /// ```
    #[inline]
    pub fn from_bytes(slice: &[u8]) -> &BStr {
        unsafe { mem::transmute(slice) }
    }

    /// Create a mutable byte string slice from a mutable byte slice.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BStr;
    ///
    /// let bytes = &mut [b'a'];
    /// {
    ///     let bs = BStr::from_bytes_mut(bytes);
    ///     bs[0] = b'b';
    /// }
    /// assert_eq!(b"b", bytes);
    /// ```
    #[inline]
    pub fn from_bytes_mut(slice: &mut [u8]) -> &mut BStr {
        unsafe { mem::transmute(slice) }
    }

    /// Create a byte string from its constituent pointer and length, where
    /// the length is the number of bytes in the byte string.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer
    /// is valid for `len` elements, nor whether the lifetime inferred is a
    /// suitable lifetime for the returned slice.
    ///
    /// `data` must be a non-null pointer, even for a zero length slice. A
    /// pointer that is usable for zero-length slices can be obtaining from
    /// the standard library's `NonNull::dangling()` constructor.
    ///
    /// The total size of the given slice must be no larger than `isize::MAX`
    /// bytes in memory.
    ///
    /// # Caveat
    ///
    /// The lifetime for the returned slice is inferred from its usage. To
    /// prevent accidental misuse, it's suggested to tie the lifetime to
    /// whichever source lifetime is safe in the context, such as by providing
    /// a helper function taking the lifetime of a host value for the slice, or
    /// by explicit annotation.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BStr;
    ///
    /// // manifest a byte string from a single byte
    /// let x = b'Z';
    /// let ptr = &x as *const u8;
    /// let s = unsafe { BStr::from_raw_parts(ptr, 1) };
    /// assert_eq!(s, "Z");
    /// ```
    pub unsafe fn from_raw_parts<'a>(data: *const u8, len: usize) -> &'a BStr {
        BStr::new(slice::from_raw_parts(data, len))
    }

    /// Create a mutable byte string from its constituent pointer and length,
    /// where the length is the number of bytes in the byte string.
    ///
    /// # Safety
    ///
    /// This function is unsafe as there is no guarantee that the given pointer
    /// is valid for `len` elements, nor whether the lifetime inferred is a
    /// suitable lifetime for the returned slice.
    ///
    /// `data` must be a non-null pointer, even for a zero length slice. A
    /// pointer that is usable for zero-length slices can be obtaining from
    /// the standard library's `NonNull::dangling()` constructor.
    ///
    /// The total size of the given slice must be no larger than `isize::MAX`
    /// bytes in memory.
    ///
    /// The above reasons are the same as for
    /// [`from_raw_parts`](#method.from_raw_parts). In addition, for this
    /// constructor, callers must guarantee that the mutable slice returned
    /// is not aliased with any other reference.
    ///
    /// # Caveat
    ///
    /// The lifetime for the returned slice is inferred from its usage. To
    /// prevent accidental misuse, it's suggested to tie the lifetime to
    /// whichever source lifetime is safe in the context, such as by providing
    /// a helper function taking the lifetime of a host value for the slice, or
    /// by explicit annotation.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::mem;
    /// use bstr::{BStr, BString};
    ///
    /// // For demonstration purposes, get a mutable pointer to a byte string.
    /// let mut buf = BString::from("bar");
    /// let ptr = buf.as_mut_ptr();
    /// // Drop buf without deallocating, to avoid &mut aliasing.
    /// mem::forget(buf);
    ///
    /// // Now convert it to a mutable byte string from the raw pointer.
    /// let mut s = unsafe { BStr::from_raw_parts_mut(ptr, 3) };
    /// s.make_ascii_uppercase();
    /// assert_eq!(s, "BAR");
    /// ```
    pub unsafe fn from_raw_parts_mut<'a>(
        data: *mut u8,
        len: usize,
    ) -> &'a mut BStr {
        BStr::new_mut(slice::from_raw_parts_mut(data, len))
    }

    /// Create an immutable byte string from an OS string slice.
    ///
    /// On Unix, this always succeeds and is zero cost. On non-Unix systems,
    /// this returns `None` if the given OS string is not valid UTF-8. (For
    /// example, on Windows, file paths are allowed to be a sequence of
    /// arbitrary 16-bit integers. Not all such sequences can be transcoded to
    /// valid UTF-8.)
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::ffi::OsStr;
    ///
    /// use bstr::BStr;
    ///
    /// let os_str = OsStr::new("foo");
    /// let bs = BStr::from_os_str(os_str).expect("should be valid UTF-8");
    /// assert_eq!(bs, "foo");
    /// ```
    #[cfg(feature = "std")]
    #[inline]
    pub fn from_os_str(os_str: &OsStr) -> Option<&BStr> {
        BStr::from_os_str_imp(os_str)
    }

    #[cfg(feature = "std")]
    #[cfg(unix)]
    #[inline]
    fn from_os_str_imp(os_str: &OsStr) -> Option<&BStr> {
        use std::os::unix::ffi::OsStrExt;

        Some(BStr::new(os_str.as_bytes()))
    }

    #[cfg(feature = "std")]
    #[cfg(not(unix))]
    #[inline]
    fn from_os_str_imp(os_str: &OsStr) -> Option<&BStr> {
        os_str.to_str().map(BStr::new)
    }

    /// Create an immutable byte string from a file path.
    ///
    /// On Unix, this always succeeds and is zero cost. On non-Unix systems,
    /// this returns `None` if the given path is not valid UTF-8. (For example,
    /// on Windows, file paths are allowed to be a sequence of arbitrary 16-bit
    /// integers. Not all such sequences can be transcoded to valid UTF-8.)
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::path::Path;
    ///
    /// use bstr::BStr;
    ///
    /// let path = Path::new("foo");
    /// let bs = BStr::from_path(path).expect("should be valid UTF-8");
    /// assert_eq!(bs, "foo");
    /// ```
    #[cfg(feature = "std")]
    #[inline]
    pub fn from_path(path: &Path) -> Option<&BStr> {
        BStr::from_os_str(path.as_os_str())
    }

    /// Returns the length, in bytes, of this byte string.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BStr;
    ///
    /// assert_eq!(0, BStr::new("").len());
    /// assert_eq!(3, BStr::new("abc").len());
    /// assert_eq!(8, BStr::new("☃βツ").len());
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.bytes.len()
    }

    /// Returns true if and only if the length of this byte string is zero.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BStr;
    ///
    /// assert!(BStr::new("").is_empty());
    /// assert!(!BStr::new("abc").is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }

    /// Returns an immutable byte slice of this `BStr`'s contents.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let s = B("hello");
    ///
    /// assert_eq!(&[104, 101, 108, 108, 111], s.as_bytes());
    /// ```
    #[inline]
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Returns a mutable byte slice of this `BStr`'s contents.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("hello");
    /// s.as_bytes_mut()[1] = b'a';
    ///
    /// assert_eq!(&[104, 97, 108, 108, 111], s.as_bytes());
    /// ```
    #[inline]
    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        &mut self.bytes
    }

    /// Create a new owned byte string from this byte string slice.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BStr;
    ///
    /// let s = BStr::new("abc");
    /// let mut owned = s.to_bstring();
    /// owned.push_char('d');
    /// assert_eq!("abcd", owned);
    /// ```
    #[cfg(feature = "std")]
    #[inline]
    pub fn to_bstring(&self) -> BString {
        BString::from_vec(self.as_bytes().to_vec())
    }

    /// Safely convert this byte string into a `&str` if it's valid UTF-8.
    ///
    /// If this byte string is not valid UTF-8, then an error is returned. The
    /// error returned indicates the first invalid byte found and the length
    /// of the error.
    ///
    /// In cases where a lossy conversion to `&str` is acceptable, then use one
    /// of the [`to_str_lossy`](#method.to_str_lossy)
    /// or [`to_str_lossy_into`](#method.to_str_lossy_into) methods.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// # fn example() -> Result<(), bstr::Utf8Error> {
    /// let s = B("☃βツ").to_str()?;
    /// assert_eq!("☃βツ", s);
    ///
    /// let mut bstring = BString::from("☃βツ");
    /// bstring.push_byte(b'\xFF');
    /// let err = bstring.to_str().unwrap_err();
    /// assert_eq!(8, err.valid_up_to());
    /// # Ok(()) }; example().unwrap()
    /// ```
    #[inline]
    pub fn to_str(&self) -> Result<&str, Utf8Error> {
        utf8::validate(self.as_bytes()).map(|_| {
            // SAFETY: This is safe because of the guarantees provided by
            // utf8::validate.
            unsafe {
                str::from_utf8_unchecked(self.as_bytes())
            }
        })
    }

    /// Unsafely convert this byte string into a `&str`, without checking for
    /// valid UTF-8.
    ///
    /// # Safety
    ///
    /// Callers *must* ensure that this byte string is valid UTF-8 before
    /// calling this method. Converting a byte string into a `&str` that is
    /// not valid UTF-8 is considered undefined behavior.
    ///
    /// This routine is useful in performance sensitive contexts where the
    /// UTF-8 validity of the byte string is already known and it is
    /// undesirable to pay the cost of an additional UTF-8 validation check
    /// that [`to_str`](#method.to_str) performs.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// // SAFETY: This is safe because string literals are guaranteed to be
    /// // valid UTF-8 by the Rust compiler.
    /// let s = unsafe { B("☃βツ").to_str_unchecked() };
    /// assert_eq!("☃βツ", s);
    /// ```
    pub unsafe fn to_str_unchecked(&self) -> &str {
        str::from_utf8_unchecked(self.as_bytes())
    }

    /// Convert this byte string to a valid UTF-8 string by replacing invalid
    /// UTF-8 bytes with the Unicode replacement codepoint (`U+FFFD`).
    ///
    /// If the byte string is already valid UTF-8, then no copying or
    /// allocation is performed and a borrrowed string slice is returned. If
    /// the byte string is not valid UTF-8, then an owned string buffer is
    /// returned with invalid bytes replaced by the replacement codepoint.
    ///
    /// This method uses the "substitution of maximal subparts" (Unicode
    /// Standard, Chapter 3, Section 9) strategy for inserting the replacement
    /// codepoint. Specifically, a replacement codepoint is inserted whenever a
    /// byte is found that cannot possibly lead to a valid code unit sequence.
    /// If there were previous bytes that represented a prefix of a well-formed
    /// code unit sequence, then all of those bytes are substituted with a
    /// single replacement codepoint. The "substitution of maximal subparts"
    /// strategy is the same strategy used by
    /// [W3C's Encoding standard](https://www.w3.org/TR/encoding/).
    /// For a more precise description of the maximal subpart strategy, see
    /// the Unicode Standard, Chapter 3, Section 9. See also
    /// [Public Review Issue #121](http://www.unicode.org/review/pr-121.html).
    ///
    /// N.B. Rust's standard library also appears to use the same strategy,
    /// but it does not appear to be an API guarantee.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::borrow::Cow;
    /// use bstr::BString;
    ///
    /// let mut bstring = BString::from("☃βツ");
    /// assert_eq!(Cow::Borrowed("☃βツ"), bstring.to_str_lossy());
    ///
    /// // Add a byte that makes the sequence invalid.
    /// bstring.push_byte(b'\xFF');
    /// assert_eq!(Cow::Borrowed("☃βツ\u{FFFD}"), bstring.to_str_lossy());
    /// ```
    ///
    /// This demonstrates the "maximal subpart" substitution logic.
    ///
    /// ```
    /// use bstr::B;
    ///
    /// // \x61 is the ASCII codepoint for 'a'.
    /// // \xF1\x80\x80 is a valid 3-byte code unit prefix.
    /// // \xE1\x80 is a valid 2-byte code unit prefix.
    /// // \xC2 is a valid 1-byte code unit prefix.
    /// // \x62 is the ASCII codepoint for 'b'.
    /// //
    /// // In sum, each of the prefixes is replaced by a single replacement
    /// // codepoint since none of the prefixes are properly completed. This
    /// // is in contrast to other strategies that might insert a replacement
    /// // codepoint for every single byte.
    /// let bs = B(b"\x61\xF1\x80\x80\xE1\x80\xC2\x62");
    /// assert_eq!("a\u{FFFD}\u{FFFD}\u{FFFD}b", bs.to_str_lossy());
    /// ```
    #[cfg(feature = "std")]
    #[inline]
    pub fn to_str_lossy(&self) -> Cow<str> {
        match utf8::validate(self.as_bytes()) {
            Ok(()) => {
                // SAFETY: This is safe because of the guarantees provided by
                // utf8::validate.
                unsafe {
                    Cow::Borrowed(str::from_utf8_unchecked(self.as_bytes()))
                }
            }
            Err(err) => {
                let mut lossy = String::with_capacity(self.len());
                let (valid, after) = self
                    .as_bytes()
                    .split_at(err.valid_up_to());
                // SAFETY: This is safe because utf8::validate guarantees
                // that all of `valid` is valid UTF-8.
                lossy.push_str(unsafe { str::from_utf8_unchecked(valid) });
                lossy.push_str("\u{FFFD}");
                if let Some(len) = err.error_len() {
                    B(&after[len..]).to_str_lossy_into(&mut lossy);
                }
                Cow::Owned(lossy)
            }
        }
    }

    /// Copy the contents of this byte string into the given owned string
    /// buffer, while replacing invalid UTF-8 code unit sequences with the
    /// Unicode replacement codepoint (`U+FFFD`).
    ///
    /// This method uses the same "substitution of maximal subparts" strategy
    /// for inserting the replacement codepoint as the
    /// [`to_str_lossy`](#method.to_str_lossy) method.
    ///
    /// This routine is useful for amortizing allocation. However, unlike
    /// `to_str_lossy`, this routine will _always_ copy the contents of this
    /// byte string into the destination buffer, even if this byte string is
    /// valid UTF-8.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::borrow::Cow;
    /// use bstr::BString;
    ///
    /// let mut bstring = BString::from("☃βツ");
    /// // Add a byte that makes the sequence invalid.
    /// bstring.push_byte(b'\xFF');
    ///
    /// let mut dest = String::new();
    /// bstring.to_str_lossy_into(&mut dest);
    /// assert_eq!("☃βツ\u{FFFD}", dest);
    /// ```
    #[cfg(feature = "std")]
    #[inline]
    pub fn to_str_lossy_into(&self, dest: &mut String) {
        dest.reserve(self.len());
        let mut bytes = self.as_bytes();
        loop {
            match utf8::validate(bytes) {
                Ok(()) => {
                    // SAFETY: This is safe because utf8::validate guarantees
                    // that all of `bytes` is valid UTF-8.
                    dest.push_str(unsafe { str::from_utf8_unchecked(bytes) });
                    break;
                }
                Err(err) => {
                    let (valid, after) = bytes.split_at(err.valid_up_to());
                    // SAFETY: This is safe because utf8::validate guarantees
                    // that all of `valid` is valid UTF-8.
                    dest.push_str(unsafe { str::from_utf8_unchecked(valid) });
                    dest.push_str("\u{FFFD}");
                    match err.error_len() {
                        None => break,
                        Some(len) => bytes = &after[len..],
                    }
                }
            }
        }
    }

    /// Create an OS string slice from this byte string.
    ///
    /// On Unix, this always succeeds and is zero cost. On non-Unix systems,
    /// this returns a UTF-8 decoding error if this byte string is not valid
    /// UTF-8. (For example, on Windows, file paths are allowed to be a
    /// sequence of arbitrary 16-bit integers. There is no obvious mapping from
    /// an arbitrary sequence of 8-bit integers to an arbitrary sequence of
    /// 16-bit integers.)
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let bs = B("foo");
    /// let os_str = bs.to_os_str().expect("should be valid UTF-8");
    /// assert_eq!(os_str, "foo");
    /// ```
    #[cfg(feature = "std")]
    #[inline]
    pub fn to_os_str(&self) -> Result<&OsStr, Utf8Error> {
        self.to_os_str_imp()
    }

    #[cfg(feature = "std")]
    #[cfg(unix)]
    #[inline]
    fn to_os_str_imp(&self) -> Result<&OsStr, Utf8Error> {
        use std::os::unix::ffi::OsStrExt;

        Ok(OsStr::from_bytes(self.as_bytes()))
    }

    #[cfg(feature = "std")]
    #[cfg(not(unix))]
    #[inline]
    fn to_os_str_imp(&self) -> Result<&OsStr, Utf8Error> {
        self.to_str().map(OsStr::new)
    }

    /// Lossily create an OS string slice from this byte string.
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
    /// use bstr::B;
    ///
    /// let bs = B(b"foo\xFFbar");
    /// let os_str = bs.to_os_str_lossy();
    /// assert_eq!(os_str.to_string_lossy(), "foo\u{FFFD}bar");
    /// ```
    #[cfg(feature = "std")]
    #[inline]
    pub fn to_os_str_lossy(&self) -> Cow<OsStr> {
        self.to_os_str_lossy_imp()
    }

    #[cfg(feature = "std")]
    #[cfg(unix)]
    #[inline]
    fn to_os_str_lossy_imp(&self) -> Cow<OsStr> {
        use std::os::unix::ffi::OsStrExt;

        Cow::Borrowed(OsStr::from_bytes(self.as_bytes()))
    }

    #[cfg(feature = "std")]
    #[cfg(not(unix))]
    #[inline]
    fn to_os_str_lossy_imp(&self) -> Cow<OsStr> {
        use std::ffi::OsString;

        match self.to_str_lossy() {
            Cow::Borrowed(x) => Cow::Borrowed(OsStr::new(x)),
            Cow::Owned(x) => Cow::Owned(OsString::from(x)),
        }
    }

    /// Create a path slice from this byte string.
    ///
    /// On Unix, this always succeeds and is zero cost. On non-Unix systems,
    /// this returns a UTF-8 decoding error if this byte string is not valid
    /// UTF-8. (For example, on Windows, file paths are allowed to be a
    /// sequence of arbitrary 16-bit integers. There is no obvious mapping from
    /// an arbitrary sequence of 8-bit integers to an arbitrary sequence of
    /// 16-bit integers.)
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let bs = B("foo");
    /// let path = bs.to_path().expect("should be valid UTF-8");
    /// assert_eq!(path.as_os_str(), "foo");
    /// ```
    #[cfg(feature = "std")]
    #[inline]
    pub fn to_path(&self) -> Result<&Path, Utf8Error> {
        self.to_os_str().map(Path::new)
    }

    /// Lossily create a path slice from this byte string.
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
    /// use bstr::B;
    ///
    /// let bs = B(b"foo\xFFbar");
    /// let path = bs.to_path_lossy();
    /// assert_eq!(path.to_string_lossy(), "foo\u{FFFD}bar");
    /// ```
    #[cfg(feature = "std")]
    #[inline]
    pub fn to_path_lossy(&self) -> Cow<Path> {
        use std::path::PathBuf;

        match self.to_os_str_lossy() {
            Cow::Borrowed(x) => Cow::Borrowed(Path::new(x)),
            Cow::Owned(x) => Cow::Owned(PathBuf::from(x)),
        }
    }

    /// Create a new `BString` by repeating this byte string `n` times.
    ///
    /// # Panics
    ///
    /// This function panics if the capacity of the new `BString` would
    /// overflow.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// assert_eq!("foofoofoofoo", B("foo").repeat(4));
    /// assert_eq!("", B("foo").repeat(0));
    /// ```
    #[cfg(feature = "std")]
    #[inline]
    pub fn repeat(&self, n: usize) -> BString {
        iter::repeat(self).take(n).collect()
    }

    /// Returns true if and only if this byte string contains the given needle.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// assert!(B("foo bar").contains("foo"));
    /// assert!(B("foo bar").contains("bar"));
    /// assert!(!B("foo").contains("foobar"));
    /// ```
    #[inline]
    pub fn contains<B: AsRef<[u8]>>(&self, needle: B) -> bool {
        self.find(needle).is_some()
    }

    /// Returns true if and only if this byte string has the given prefix.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// assert!(B("foo bar").starts_with("foo"));
    /// assert!(!B("foo bar").starts_with("bar"));
    /// assert!(!B("foo").starts_with("foobar"));
    /// ```
    #[inline]
    pub fn starts_with<B: AsRef<[u8]>>(&self, prefix: B) -> bool {
        let prefix = prefix.as_ref();
        self.get(..prefix.len()).map_or(false, |x| x == prefix)
    }

    /// Returns true if and only if this byte string has the given suffix.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// assert!(B("foo bar").ends_with("bar"));
    /// assert!(!B("foo bar").ends_with("foo"));
    /// assert!(!B("bar").ends_with("foobar"));
    /// ```
    #[inline]
    pub fn ends_with<B: AsRef<[u8]>>(&self, suffix: B) -> bool {
        let suffix = suffix.as_ref();
        self.len()
            .checked_sub(suffix.len())
            .map_or(false, |s| &self[s..] == suffix)
    }

    /// Returns the index of the first occurrence of the given needle.
    ///
    /// The needle may be any type that can be cheaply converted into a
    /// `&[u8]`. This includes, but is not limited to, `&str`, `&BStr`, and of
    /// course, `&[u8]` itself.
    ///
    /// Note that if you're are searching for the same needle in many
    /// different small haystacks, it may be faster to initialize a
    /// [`Finder`](struct.Finder.html) once, and reuse it for each search.
    ///
    /// # Complexity
    ///
    /// This routine is guaranteed to have worst case linear time complexity
    /// with respect to both the needle and the haystack. That is, this runs
    /// in `O(needle.len() + haystack.len())` time.
    ///
    /// This routine is also guaranteed to have worst case constant space
    /// complexity.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let s = B("foo bar baz");
    /// assert_eq!(Some(0), s.find("foo"));
    /// assert_eq!(Some(4), s.find("bar"));
    /// assert_eq!(None, s.find("quux"));
    /// ```
    #[inline]
    pub fn find<B: AsRef<[u8]>>(&self, needle: B) -> Option<usize> {
        Finder::new(needle.as_ref()).find(self)
    }

    /// Returns the index of the last occurrence of the given needle.
    ///
    /// The needle may be any type that can be cheaply converted into a
    /// `&[u8]`. This includes, but is not limited to, `&str`, `&BStr`, and of
    /// course, `&[u8]` itself.
    ///
    /// Note that if you're are searching for the same needle in many
    /// different small haystacks, it may be faster to initialize a
    /// [`FinderReverse`](struct.FinderReverse.html) once, and reuse it for
    /// each search.
    ///
    /// # Complexity
    ///
    /// This routine is guaranteed to have worst case linear time complexity
    /// with respect to both the needle and the haystack. That is, this runs
    /// in `O(needle.len() + haystack.len())` time.
    ///
    /// This routine is also guaranteed to have worst case constant space
    /// complexity.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let s = B("foo bar baz");
    /// assert_eq!(Some(0), s.rfind("foo"));
    /// assert_eq!(Some(4), s.rfind("bar"));
    /// assert_eq!(Some(8), s.rfind("ba"));
    /// assert_eq!(None, s.rfind("quux"));
    /// ```
    #[inline]
    pub fn rfind<B: AsRef<[u8]>>(&self, needle: B) -> Option<usize> {
        FinderReverse::new(needle.as_ref()).rfind(self)
    }

    /// Returns an iterator of the non-overlapping occurrences of the given
    /// needle. The iterator yields byte offset positions indicating the start
    /// of each match.
    ///
    /// # Complexity
    ///
    /// This routine is guaranteed to have worst case linear time complexity
    /// with respect to both the needle and the haystack. That is, this runs
    /// in `O(needle.len() + haystack.len())` time.
    ///
    /// This routine is also guaranteed to have worst case constant space
    /// complexity.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let s = B("foo bar foo foo quux foo");
    /// let matches: Vec<usize> = s.find_iter("foo").collect();
    /// assert_eq!(matches, vec![0, 8, 12, 21]);
    /// ```
    ///
    /// An empty string matches at every position, including the position
    /// immediately following the last byte:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let matches: Vec<usize> = B("foo").find_iter("").collect();
    /// assert_eq!(matches, vec![0, 1, 2, 3]);
    ///
    /// let matches: Vec<usize> = B("").find_iter("").collect();
    /// assert_eq!(matches, vec![0]);
    /// ```
    #[inline]
    pub fn find_iter<'a, B: ?Sized + AsRef<[u8]>>(
        &'a self,
        needle: &'a B,
    ) -> Find<'a> {
        Find::new(self, BStr::new(needle.as_ref()))
    }

    /// Returns an iterator of the non-overlapping occurrences of the given
    /// needle in reverse. The iterator yields byte offset positions indicating
    /// the start of each match.
    ///
    /// # Complexity
    ///
    /// This routine is guaranteed to have worst case linear time complexity
    /// with respect to both the needle and the haystack. That is, this runs
    /// in `O(needle.len() + haystack.len())` time.
    ///
    /// This routine is also guaranteed to have worst case constant space
    /// complexity.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let s = B("foo bar foo foo quux foo");
    /// let matches: Vec<usize> = s.rfind_iter("foo").collect();
    /// assert_eq!(matches, vec![21, 12, 8, 0]);
    /// ```
    ///
    /// An empty string matches at every position, including the position
    /// immediately following the last byte:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let matches: Vec<usize> = B("foo").rfind_iter("").collect();
    /// assert_eq!(matches, vec![3, 2, 1, 0]);
    ///
    /// let matches: Vec<usize> = B("").rfind_iter("").collect();
    /// assert_eq!(matches, vec![0]);
    /// ```
    #[inline]
    pub fn rfind_iter<'a, B: ?Sized + AsRef<[u8]>>(
        &'a self,
        needle: &'a B,
    ) -> FindReverse<'a> {
        FindReverse::new(self, BStr::new(needle.as_ref()))
    }

    /// Returns the index of the first occurrence of the given byte. If the
    /// byte does not occur in this byte string, then `None` is returned.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// assert_eq!(Some(10), B("foo bar baz").find_byte(b'z'));
    /// assert_eq!(None, B("foo bar baz").find_byte(b'y'));
    /// ```
    #[inline]
    pub fn find_byte(&self, byte: u8) -> Option<usize> {
        memchr(byte, self.as_bytes())
    }

    /// Returns the index of the last occurrence of the given byte. If the
    /// byte does not occur in this byte string, then `None` is returned.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// assert_eq!(Some(10), B("foo bar baz").rfind_byte(b'z'));
    /// assert_eq!(None, B("foo bar baz").rfind_byte(b'y'));
    /// ```
    #[inline]
    pub fn rfind_byte(&self, byte: u8) -> Option<usize> {
        memrchr(byte, self.as_bytes())
    }

    /// Returns the index of the first occurrence of the given codepoint.
    /// If the codepoint does not occur in this byte string, then `None` is
    /// returned.
    ///
    /// Note that if one searches for the replacement codepoint, `\u{FFFD}`,
    /// then only explicit occurrences of that encoding will be found. Invalid
    /// UTF-8 sequences will not be matched.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// assert_eq!(Some(10), B("foo bar baz").find_char('z'));
    /// assert_eq!(Some(4), B("αβγγδ").find_char('γ'));
    /// assert_eq!(None, B("foo bar baz").find_char('y'));
    /// ```
    #[inline]
    pub fn find_char(&self, ch: char) -> Option<usize> {
        self.find(ch.encode_utf8(&mut [0; 4]))
    }

    /// Returns the index of the last occurrence of the given codepoint.
    /// If the codepoint does not occur in this byte string, then `None` is
    /// returned.
    ///
    /// Note that if one searches for the replacement codepoint, `\u{FFFD}`,
    /// then only explicit occurrences of that encoding will be found. Invalid
    /// UTF-8 sequences will not be matched.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// assert_eq!(Some(10), B("foo bar baz").rfind_char('z'));
    /// assert_eq!(Some(6), B("αβγγδ").rfind_char('γ'));
    /// assert_eq!(None, B("foo bar baz").rfind_char('y'));
    /// ```
    #[inline]
    pub fn rfind_char(&self, ch: char) -> Option<usize> {
        self.rfind(ch.encode_utf8(&mut [0; 4]))
    }

    /// Returns an iterator over the fields in a byte string, separated by
    /// contiguous whitespace.
    ///
    /// # Example
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{B, BStr};
    ///
    /// let s = B("  foo\tbar\t\u{2003}\nquux   \n");
    /// let fields: Vec<&BStr> = s.fields().collect();
    /// assert_eq!(fields, vec!["foo", "bar", "quux"]);
    /// ```
    ///
    /// A byte string consisting of just whitespace yields no elements:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// assert_eq!(0, B("  \n\t\u{2003}\n  \t").fields().count());
    /// ```
    #[inline]
    pub fn fields(&self) -> Fields {
        Fields::new(self)
    }

    /// Returns an iterator over the fields in a byte string, separated by
    /// contiguous codepoints satisfying the given predicate.
    ///
    /// If this byte
    ///
    /// # Example
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{B, BStr};
    ///
    /// let s = B("123foo999999bar1quux123456");
    /// let fields: Vec<&BStr> = s.fields_with(|c| c.is_numeric()).collect();
    /// assert_eq!(fields, vec!["foo", "bar", "quux"]);
    /// ```
    ///
    /// A byte string consisting of all codepoints satisfying the predicate
    /// yields no elements:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// assert_eq!(0, B("1911354563").fields_with(|c| c.is_numeric()).count());
    /// ```
    #[inline]
    pub fn fields_with<F: FnMut(char) -> bool>(&self, f: F) -> FieldsWith<F> {
        FieldsWith::new(self, f)
    }

    /// Returns an iterator over substrings of this byte string, separated
    /// by the given byte string. Each element yielded is guaranteed not to
    /// include the splitter substring.
    ///
    /// The splitter may be any type that can be cheaply converted into a
    /// `&[u8]`. This includes, but is not limited to, `&str`, `&BStr`, and of
    /// course, `&[u8]` itself.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{B, BStr};
    ///
    /// let x: Vec<&BStr> = B("Mary had a little lamb").split(" ").collect();
    /// assert_eq!(x, vec!["Mary", "had", "a", "little", "lamb"]);
    ///
    /// let x: Vec<&BStr> = B("").split("X").collect();
    /// assert_eq!(x, vec![""]);
    ///
    /// let x: Vec<&BStr> = B("lionXXtigerXleopard").split("X").collect();
    /// assert_eq!(x, vec!["lion", "", "tiger", "leopard"]);
    ///
    /// let x: Vec<&BStr> = B("lion::tiger::leopard").split("::").collect();
    /// assert_eq!(x, vec!["lion", "tiger", "leopard"]);
    /// ```
    ///
    /// If a string contains multiple contiguous separators, you will end up
    /// with empty strings yielded by the iterator:
    ///
    /// ```
    /// use bstr::{B, BStr};
    ///
    /// let x: Vec<&BStr> = B("||||a||b|c").split("|").collect();
    /// assert_eq!(x, vec!["", "", "", "", "a", "", "b", "c"]);
    ///
    /// let x: Vec<&BStr> = B("(///)").split("/").collect();
    /// assert_eq!(x, vec!["(", "", "", ")"]);
    /// ```
    ///
    /// Separators at the start or end of a string are neighbored by empty
    /// strings.
    ///
    /// ```
    /// use bstr::{B, BStr};
    ///
    /// let x: Vec<&BStr> = B("010").split("0").collect();
    /// assert_eq!(x, vec!["", "1", ""]);
    /// ```
    ///
    /// When the empty string is used as a separator, it splits every **byte**
    /// in the byte string, along with the beginning and end of the byte
    /// string.
    ///
    /// ```
    /// use bstr::{B, BStr};
    ///
    /// let x: Vec<&BStr> = B("rust").split("").collect();
    /// assert_eq!(x, vec!["", "r", "u", "s", "t", ""]);
    ///
    /// // Splitting by an empty string is not UTF-8 aware. Elements yielded
    /// // may not be valid UTF-8!
    /// let x: Vec<&BStr> = B("☃").split("").collect();
    /// assert_eq!(x, vec![B(""), B(b"\xE2"), B(b"\x98"), B(b"\x83"), B("")]);
    /// ```
    ///
    /// Contiguous separators, especially whitespace, can lead to possibly
    /// surprising behavior. For example, this code is correct:
    ///
    /// ```
    /// use bstr::{B, BStr};
    ///
    /// let x: Vec<&BStr> = B("    a  b c").split(" ").collect();
    /// assert_eq!(x, vec!["", "", "", "", "a", "", "b", "c"]);
    /// ```
    ///
    /// It does *not* give you `["a", "b", "c"]`. For that behavior, use
    /// [`fields`](#method.fields) instead.
    #[inline]
    pub fn split<'a, B: ?Sized + AsRef<[u8]>>(
        &'a self,
        splitter: &'a B,
    ) -> Split<'a> {
        Split::new(self, BStr::new(splitter.as_ref()))
    }

    /// Returns an iterator over substrings of this byte string, separated by
    /// the given byte string, in reverse. Each element yielded is guaranteed
    /// not to include the splitter substring.
    ///
    /// The splitter may be any type that can be cheaply converted into a
    /// `&[u8]`. This includes, but is not limited to, `&str`, `&BStr`, and of
    /// course, `&[u8]` itself.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{B, BStr};
    ///
    /// let x: Vec<&BStr> = B("Mary had a little lamb").rsplit(" ").collect();
    /// assert_eq!(x, vec!["lamb", "little", "a", "had", "Mary"]);
    ///
    /// let x: Vec<&BStr> = B("").rsplit("X").collect();
    /// assert_eq!(x, vec![""]);
    ///
    /// let x: Vec<&BStr> = B("lionXXtigerXleopard").rsplit("X").collect();
    /// assert_eq!(x, vec!["leopard", "tiger", "", "lion"]);
    ///
    /// let x: Vec<&BStr> = B("lion::tiger::leopard").rsplit("::").collect();
    /// assert_eq!(x, vec!["leopard", "tiger", "lion"]);
    /// ```
    ///
    /// If a string contains multiple contiguous separators, you will end up
    /// with empty strings yielded by the iterator:
    ///
    /// ```
    /// use bstr::{B, BStr};
    ///
    /// let x: Vec<&BStr> = B("||||a||b|c").rsplit("|").collect();
    /// assert_eq!(x, vec!["c", "b", "", "a", "", "", "", ""]);
    ///
    /// let x: Vec<&BStr> = B("(///)").rsplit("/").collect();
    /// assert_eq!(x, vec![")", "", "", "("]);
    /// ```
    ///
    /// Separators at the start or end of a string are neighbored by empty
    /// strings.
    ///
    /// ```
    /// use bstr::{B, BStr};
    ///
    /// let x: Vec<&BStr> = B("010").rsplit("0").collect();
    /// assert_eq!(x, vec!["", "1", ""]);
    /// ```
    ///
    /// When the empty string is used as a separator, it splits every **byte**
    /// in the byte string, along with the beginning and end of the byte
    /// string.
    ///
    /// ```
    /// use bstr::{B, BStr};
    ///
    /// let x: Vec<&BStr> = B("rust").rsplit("").collect();
    /// assert_eq!(x, vec!["", "t", "s", "u", "r", ""]);
    ///
    /// // Splitting by an empty string is not UTF-8 aware. Elements yielded
    /// // may not be valid UTF-8!
    /// let x: Vec<&BStr> = B("☃").rsplit("").collect();
    /// assert_eq!(x, vec![B(""), B(b"\x83"), B(b"\x98"), B(b"\xE2"), B("")]);
    /// ```
    ///
    /// Contiguous separators, especially whitespace, can lead to possibly
    /// surprising behavior. For example, this code is correct:
    ///
    /// ```
    /// use bstr::{B, BStr};
    ///
    /// let x: Vec<&BStr> = B("    a  b c").rsplit(" ").collect();
    /// assert_eq!(x, vec!["c", "b", "", "a", "", "", "", ""]);
    /// ```
    ///
    /// It does *not* give you `["a", "b", "c"]`.
    #[inline]
    pub fn rsplit<'a, B: ?Sized + AsRef<[u8]>>(
        &'a self,
        splitter: &'a B,
    ) -> SplitReverse<'a> {
        SplitReverse::new(self, BStr::new(splitter.as_ref()))
    }

    /// Returns an iterator of at most `limit` substrings of this byte string,
    /// separated by the given byte string. If `limit` substrings are yielded,
    /// then the last substring will contain the remainder of this byte string.
    ///
    /// The splitter may be any type that can be cheaply converted into a
    /// `&[u8]`. This includes, but is not limited to, `&str`, `&BStr`, and of
    /// course, `&[u8]` itself.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{B, BStr};
    ///
    /// let x: Vec<_> = B("Mary had a little lamb").splitn(3, " ").collect();
    /// assert_eq!(x, vec!["Mary", "had", "a little lamb"]);
    ///
    /// let x: Vec<_> = B("").splitn(3, "X").collect();
    /// assert_eq!(x, vec![""]);
    ///
    /// let x: Vec<_> = B("lionXXtigerXleopard").splitn(3, "X").collect();
    /// assert_eq!(x, vec!["lion", "", "tigerXleopard"]);
    ///
    /// let x: Vec<_> = B("lion::tiger::leopard").splitn(2, "::").collect();
    /// assert_eq!(x, vec!["lion", "tiger::leopard"]);
    ///
    /// let x: Vec<_> = B("abcXdef").splitn(1, "X").collect();
    /// assert_eq!(x, vec!["abcXdef"]);
    ///
    /// let x: Vec<_> = B("abcXdef").splitn(0, "X").collect();
    /// assert!(x.is_empty());
    /// ```
    #[inline]
    pub fn splitn<'a, B: ?Sized + AsRef<[u8]>>(
        &'a self,
        limit: usize,
        splitter: &'a B,
    ) -> SplitN<'a> {
        SplitN::new(self, BStr::new(splitter.as_ref()), limit)
    }

    /// Returns an iterator of at most `limit` substrings of this byte string,
    /// separated by the given byte string, in reverse. If `limit` substrings
    /// are yielded, then the last substring will contain the remainder of this
    /// byte string.
    ///
    /// The splitter may be any type that can be cheaply converted into a
    /// `&[u8]`. This includes, but is not limited to, `&str`, `&BStr`, and of
    /// course, `&[u8]` itself.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{B, BStr};
    ///
    /// let x: Vec<_> = B("Mary had a little lamb").rsplitn(3, " ").collect();
    /// assert_eq!(x, vec!["lamb", "little", "Mary had a"]);
    ///
    /// let x: Vec<_> = B("").rsplitn(3, "X").collect();
    /// assert_eq!(x, vec![""]);
    ///
    /// let x: Vec<_> = B("lionXXtigerXleopard").rsplitn(3, "X").collect();
    /// assert_eq!(x, vec!["leopard", "tiger", "lionX"]);
    ///
    /// let x: Vec<_> = B("lion::tiger::leopard").rsplitn(2, "::").collect();
    /// assert_eq!(x, vec!["leopard", "lion::tiger"]);
    ///
    /// let x: Vec<_> = B("abcXdef").rsplitn(1, "X").collect();
    /// assert_eq!(x, vec!["abcXdef"]);
    ///
    /// let x: Vec<_> = B("abcXdef").rsplitn(0, "X").collect();
    /// assert!(x.is_empty());
    /// ```
    #[inline]
    pub fn rsplitn<'a, B: ?Sized + AsRef<[u8]>>(
        &'a self,
        limit: usize,
        splitter: &'a B,
    ) -> SplitNReverse<'a> {
        SplitNReverse::new(self, BStr::new(splitter.as_ref()), limit)
    }

    /// Replace all matches of the given needle with the given replacement, and
    /// the result as a new `BString`.
    ///
    /// This routine is useful as a convenience. If you need to reuse an
    /// allocation, use [`replace_into`](#method.replace_into) instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let s = B("this is old").replace("old", "new");
    /// assert_eq!(s, "this is new");
    /// ```
    ///
    /// When the pattern doesn't match:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let s = B("this is old").replace("nada nada", "limonada");
    /// assert_eq!(s, "this is old");
    /// ```
    ///
    /// When the needle is an empty string:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let s = B("foo").replace("", "Z");
    /// assert_eq!(s, "ZfZoZoZ");
    /// ```
    #[cfg(feature = "std")]
    #[inline]
    pub fn replace<N: AsRef<[u8]>, R: AsRef<[u8]>>(
        &self,
        needle: N,
        replacement: R,
    ) -> BString {
        let mut dest = BString::with_capacity(self.len());
        self.replace_into(needle, replacement, &mut dest);
        dest
    }

    /// Replace up to `limit` matches of the given needle with the given
    /// replacement, and the result as a new `BString`.
    ///
    /// This routine is useful as a convenience. If you need to reuse an
    /// allocation, use [`replacen_into`](#method.replacen_into) instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let s = B("foofoo").replacen("o", "z", 2);
    /// assert_eq!(s, "fzzfoo");
    /// ```
    ///
    /// When the pattern doesn't match:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let s = B("foofoo").replacen("a", "z", 2);
    /// assert_eq!(s, "foofoo");
    /// ```
    ///
    /// When the needle is an empty string:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let s = B("foo").replacen("", "Z", 2);
    /// assert_eq!(s, "ZfZoo");
    /// ```
    #[cfg(feature = "std")]
    #[inline]
    pub fn replacen<N: AsRef<[u8]>, R: AsRef<[u8]>>(
        &self,
        needle: N,
        replacement: R,
        limit: usize,
    ) -> BString {
        let mut dest = BString::with_capacity(self.len());
        self.replacen_into(needle, replacement, limit, &mut dest);
        dest
    }

    /// Replace all matches of the given needle with the given replacement,
    /// and write the result into the provided `BString`.
    ///
    /// This does **not** clear `dest` before writing to it.
    ///
    /// This routine is useful for reusing allocation. For a more convenient
    /// API, use [`replace`](#method.replace) instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let s = B("this is old");
    ///
    /// let mut dest = BString::new();
    /// s.replace_into("old", "new", &mut dest);
    /// assert_eq!(dest, "this is new");
    /// ```
    ///
    /// When the pattern doesn't match:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let s = B("this is old");
    ///
    /// let mut dest = BString::new();
    /// s.replace_into("nada nada", "limonada", &mut dest);
    /// assert_eq!(dest, "this is old");
    /// ```
    ///
    /// When the needle is an empty string:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let s = B("foo");
    ///
    /// let mut dest = BString::new();
    /// s.replace_into("", "Z", &mut dest);
    /// assert_eq!(dest, "ZfZoZoZ");
    /// ```
    #[cfg(feature = "std")]
    #[inline]
    pub fn replace_into<N: AsRef<[u8]>, R: AsRef<[u8]>>(
        &self,
        needle: N,
        replacement: R,
        dest: &mut BString,
    ) {
        let (needle, replacement) = (needle.as_ref(), replacement.as_ref());

        let mut last = 0;
        for start in self.find_iter(needle) {
            dest.push(&self[last..start]);
            dest.push(replacement);
            last = start + needle.len();
        }
        dest.push(&self[last..]);
    }

    /// Replace up to `limit` matches of the given needle with the given
    /// replacement, and write the result into the provided `BString`.
    ///
    /// This does **not** clear `dest` before writing to it.
    ///
    /// This routine is useful for reusing allocation. For a more convenient
    /// API, use [`replace`](#method.replacen) instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let s = B("foofoo");
    ///
    /// let mut dest = BString::new();
    /// s.replacen_into("o", "z", 2, &mut dest);
    /// assert_eq!(dest, "fzzfoo");
    /// ```
    ///
    /// When the pattern doesn't match:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let s = B("foofoo");
    ///
    /// let mut dest = BString::new();
    /// s.replacen_into("a", "z", 2, &mut dest);
    /// assert_eq!(dest, "foofoo");
    /// ```
    ///
    /// When the needle is an empty string:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let s = B("foo");
    ///
    /// let mut dest = BString::new();
    /// s.replacen_into("", "Z", 2, &mut dest);
    /// assert_eq!(dest, "ZfZoo");
    /// ```
    #[cfg(feature = "std")]
    #[inline]
    pub fn replacen_into<N: AsRef<[u8]>, R: AsRef<[u8]>>(
        &self,
        needle: N,
        replacement: R,
        limit: usize,
        dest: &mut BString,
    ) {
        let (needle, replacement) = (needle.as_ref(), replacement.as_ref());

        let mut last = 0;
        for start in self.find_iter(needle).take(limit) {
            dest.push(&self[last..start]);
            dest.push(replacement);
            last = start + needle.len();
        }
        dest.push(&self[last..]);
    }

    /// Returns an iterator over the bytes in this byte string.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let bs = B("foobar");
    /// let bytes: Vec<u8> = bs.bytes().collect();
    /// assert_eq!(bytes, bs);
    /// ```
    #[inline]
    pub fn bytes(&self) -> Bytes {
        Bytes { it: self.as_bytes().iter() }
    }

    /// Returns an iterator over the Unicode scalar values in this byte string.
    /// If invalid UTF-8 is encountered, then the Unicode replacement codepoint
    /// is yielded instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let bs = B(b"\xE2\x98\x83\xFF\xF0\x9D\x9E\x83\xE2\x98\x61");
    /// let chars: Vec<char> = bs.chars().collect();
    /// assert_eq!(vec!['☃', '\u{FFFD}', '𝞃', '\u{FFFD}', 'a'], chars);
    /// ```
    ///
    /// Codepoints can also be iterated over in reverse:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let bs = B(b"\xE2\x98\x83\xFF\xF0\x9D\x9E\x83\xE2\x98\x61");
    /// let chars: Vec<char> = bs.chars().rev().collect();
    /// assert_eq!(vec!['a', '\u{FFFD}', '𝞃', '\u{FFFD}', '☃'], chars);
    /// ```
    #[inline]
    pub fn chars(&self) -> Chars {
        Chars::new(self)
    }

    /// Returns an iterator over the Unicode scalar values in this byte string
    /// along with their starting and ending byte index positions. If invalid
    /// UTF-8 is encountered, then the Unicode replacement codepoint is yielded
    /// instead.
    ///
    /// Note that this is slightly different from the `CharIndices` iterator
    /// provided by the standard library. Aside from working on possibly
    /// invalid UTF-8, this iterator provides both the corresponding starting
    /// and ending byte indices of each codepoint yielded. The ending position
    /// is necessary to slice the original byte string when invalid UTF-8 bytes
    /// are converted into a Unicode replacement codepoint, since a single
    /// replacement codepoint can substitute anywhere from 1 to 3 invalid bytes
    /// (inclusive).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let bs = B(b"\xE2\x98\x83\xFF\xF0\x9D\x9E\x83\xE2\x98\x61");
    /// let chars: Vec<(usize, usize, char)> = bs.char_indices().collect();
    /// assert_eq!(chars, vec![
    ///     (0, 3, '☃'),
    ///     (3, 4, '\u{FFFD}'),
    ///     (4, 8, '𝞃'),
    ///     (8, 10, '\u{FFFD}'),
    ///     (10, 11, 'a'),
    /// ]);
    /// ```
    ///
    /// Codepoints can also be iterated over in reverse:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let bs = B(b"\xE2\x98\x83\xFF\xF0\x9D\x9E\x83\xE2\x98\x61");
    /// let chars: Vec<(usize, usize, char)> = bs
    ///     .char_indices()
    ///     .rev()
    ///     .collect();
    /// assert_eq!(chars, vec![
    ///     (10, 11, 'a'),
    ///     (8, 10, '\u{FFFD}'),
    ///     (4, 8, '𝞃'),
    ///     (3, 4, '\u{FFFD}'),
    ///     (0, 3, '☃'),
    /// ]);
    /// ```
    #[inline]
    pub fn char_indices(&self) -> CharIndices {
        CharIndices::new(self)
    }

    /// Returns an iterator over the grapheme clusters in this byte string.
    /// If invalid UTF-8 is encountered, then the Unicode replacement codepoint
    /// is yielded instead.
    ///
    /// # Examples
    ///
    /// This example shows how multiple codepoints can combine to form a
    /// single grapheme cluster:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let bs = B("a\u{0300}\u{0316}\u{1F1FA}\u{1F1F8}");
    /// let graphemes: Vec<&str> = bs.graphemes().collect();
    /// assert_eq!(vec!["à̖", "🇺🇸"], graphemes);
    /// ```
    ///
    /// This shows that graphemes can be iterated over in reverse:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let bs = B("a\u{0300}\u{0316}\u{1F1FA}\u{1F1F8}");
    /// let graphemes: Vec<&str> = bs.graphemes().rev().collect();
    /// assert_eq!(vec!["🇺🇸", "à̖"], graphemes);
    /// ```
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn graphemes(&self) -> Graphemes {
        Graphemes::new(self)
    }

    /// Returns an iterator over the grapheme clusters in this byte string
    /// along with their starting and ending byte index positions. If invalid
    /// UTF-8 is encountered, then the Unicode replacement codepoint is yielded
    /// instead.
    ///
    /// # Examples
    ///
    /// This example shows how to get the byte offsets of each individual
    /// grapheme cluster:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let bs = B("a\u{0300}\u{0316}\u{1F1FA}\u{1F1F8}");
    /// let graphemes: Vec<(usize, usize, &str)> =
    ///     bs.grapheme_indices().collect();
    /// assert_eq!(vec![(0, 5, "à̖"), (5, 13, "🇺🇸")], graphemes);
    /// ```
    ///
    /// This example shows what happens when invalid UTF-8 is enountered. Note
    /// that the offsets are valid indices into the original string, and do
    /// not necessarily correspond to the length of the `&str` returned!
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut bytes = BString::new();
    /// bytes.push("a\u{0300}\u{0316}");
    /// bytes.push_byte(b'\xFF');
    /// bytes.push("\u{1F1FA}\u{1F1F8}");
    ///
    /// let graphemes: Vec<(usize, usize, &str)> =
    ///     bytes.grapheme_indices().collect();
    /// assert_eq!(
    ///     graphemes,
    ///     vec![(0, 5, "à̖"), (5, 6, "\u{FFFD}"), (6, 14, "🇺🇸")]
    /// );
    /// ```
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn grapheme_indices(&self) -> GraphemeIndices {
        GraphemeIndices::new(self)
    }

    /// Returns an iterator over the words in this byte string. If invalid
    /// UTF-8 is encountered, then the Unicode replacement codepoint is yielded
    /// instead.
    ///
    /// This is similar to
    /// [`words_with_breaks`](struct.BStr.html#method.words_with_breaks),
    /// except it only returns elements that contain a "word" character. A word
    /// character is defined by UTS #18 (Annex C) to be the combination of the
    /// `Alphabetic` and `Join_Control` properties, along with the
    /// `Decimal_Number`, `Mark` and `Connector_Punctuation` general
    /// categories.
    ///
    /// Since words are made up of one or more codepoints, this iterator
    /// yields `&str` elements. When invalid UTF-8 is encountered, replacement
    /// codepoints are [substituted](index.html#handling-of-invalid-utf-8).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let bs = B(r#"The quick ("brown") fox can't jump 32.3 feet, right?"#);
    /// let words: Vec<&str> = bs.words().collect();
    /// assert_eq!(words, vec![
    ///     "The", "quick", "brown", "fox", "can't",
    ///     "jump", "32.3", "feet", "right",
    /// ]);
    /// ```
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn words(&self) -> Words {
        Words::new(self)
    }

    /// Returns an iterator over the words in this byte string along with
    /// their starting and ending byte index positions.
    ///
    /// This is similar to
    /// [`words_with_break_indices`](struct.BStr.html#method.words_with_break_indices),
    /// except it only returns elements that contain a "word" character. A word
    /// character is defined by UTS #18 (Annex C) to be the combination of the
    /// `Alphabetic` and `Join_Control` properties, along with the
    /// `Decimal_Number`, `Mark` and `Connector_Punctuation` general
    /// categories.
    ///
    /// Since words are made up of one or more codepoints, this iterator
    /// yields `&str` elements. When invalid UTF-8 is encountered, replacement
    /// codepoints are [substituted](index.html#handling-of-invalid-utf-8).
    ///
    /// # Examples
    ///
    /// This example shows how to get the byte offsets of each individual
    /// word:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let bs = B("can't jump 32.3 feet");
    /// let words: Vec<(usize, usize, &str)> = bs.word_indices().collect();
    /// assert_eq!(words, vec![
    ///     (0, 5, "can't"),
    ///     (6, 10, "jump"),
    ///     (11, 15, "32.3"),
    ///     (16, 20, "feet"),
    /// ]);
    /// ```
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn word_indices(&self) -> WordIndices {
        WordIndices::new(self)
    }

    /// Returns an iterator over the words in this byte string, along with
    /// all breaks between the words. Concatenating all elements yielded by
    /// the iterator results in the original string (modulo Unicode replacement
    /// codepoint substitutions if invalid UTF-8 is encountered).
    ///
    /// Since words are made up of one or more codepoints, this iterator
    /// yields `&str` elements. When invalid UTF-8 is encountered, replacement
    /// codepoints are [substituted](index.html#handling-of-invalid-utf-8).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let bs = B(r#"The quick ("brown") fox can't jump 32.3 feet, right?"#);
    /// let words: Vec<&str> = bs.words_with_breaks().collect();
    /// assert_eq!(words, vec![
    ///     "The", " ", "quick", " ", "(", "\"", "brown", "\"", ")",
    ///     " ", "fox", " ", "can't", " ", "jump", " ", "32.3", " ", "feet",
    ///     ",", " ", "right", "?",
    /// ]);
    /// ```
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn words_with_breaks(&self) -> WordsWithBreaks {
        WordsWithBreaks::new(self)
    }

    /// Returns an iterator over the words and their byte offsets in this
    /// byte string, along with all breaks between the words. Concatenating
    /// all elements yielded by the iterator results in the original string
    /// (modulo Unicode replacement codepoint substitutions if invalid UTF-8 is
    /// encountered).
    ///
    /// Since words are made up of one or more codepoints, this iterator
    /// yields `&str` elements. When invalid UTF-8 is encountered, replacement
    /// codepoints are [substituted](index.html#handling-of-invalid-utf-8).
    ///
    /// # Examples
    ///
    /// This example shows how to get the byte offsets of each individual
    /// word:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let bs = B("can't jump 32.3 feet");
    /// let words: Vec<(usize, usize, &str)> =
    ///     bs.words_with_break_indices().collect();
    /// assert_eq!(words, vec![
    ///     (0, 5, "can't"),
    ///     (5, 6, " "),
    ///     (6, 10, "jump"),
    ///     (10, 11, " "),
    ///     (11, 15, "32.3"),
    ///     (15, 16, " "),
    ///     (16, 20, "feet"),
    /// ]);
    /// ```
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn words_with_break_indices(&self) -> WordsWithBreakIndices {
        WordsWithBreakIndices::new(self)
    }

    /// Returns an iterator over the sentences in this byte string.
    ///
    /// Typically, a sentence will include its trailing punctuation and
    /// whitespace. Concatenating all elements yielded by the iterator
    /// results in the original string (modulo Unicode replacement codepoint
    /// substitutions if invalid UTF-8 is encountered).
    ///
    /// Since sentences are made up of one or more codepoints, this iterator
    /// yields `&str` elements. When invalid UTF-8 is encountered, replacement
    /// codepoints are [substituted](index.html#handling-of-invalid-utf-8).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let bs = B("I want this. Not that. Right now.");
    /// let sentences: Vec<&str> = bs.sentences().collect();
    /// assert_eq!(sentences, vec![
    ///     "I want this. ",
    ///     "Not that. ",
    ///     "Right now.",
    /// ]);
    /// ```
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn sentences(&self) -> Sentences {
        Sentences::new(self)
    }

    /// Returns an iterator over the sentences in this byte string along with
    /// their starting and ending byte index positions.
    ///
    /// Typically, a sentence will include its trailing punctuation and
    /// whitespace. Concatenating all elements yielded by the iterator
    /// results in the original string (modulo Unicode replacement codepoint
    /// substitutions if invalid UTF-8 is encountered).
    ///
    /// Since sentences are made up of one or more codepoints, this iterator
    /// yields `&str` elements. When invalid UTF-8 is encountered, replacement
    /// codepoints are [substituted](index.html#handling-of-invalid-utf-8).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let bs = B("I want this. Not that. Right now.");
    /// let sentences: Vec<(usize, usize, &str)> =
    ///     bs.sentence_indices().collect();
    /// assert_eq!(sentences, vec![
    ///     (0, 13, "I want this. "),
    ///     (13, 23, "Not that. "),
    ///     (23, 33, "Right now."),
    /// ]);
    /// ```
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn sentence_indices(&self) -> SentenceIndices {
        SentenceIndices::new(self)
    }

    /// An iterator over all lines in a byte string, without their
    /// terminators.
    ///
    /// For this iterator, the only line terminators recognized are `\r\n` and
    /// `\n`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{B, BStr};
    ///
    /// let s = B("\
    /// foo
    ///
    /// bar\r
    /// baz
    ///
    ///
    /// quux");
    /// let lines: Vec<&BStr> = s.lines().collect();
    /// assert_eq!(lines, vec![
    ///     "foo", "", "bar", "baz", "", "", "quux",
    /// ]);
    /// ```
    #[inline]
    pub fn lines(&self) -> Lines {
        Lines::new(self)
    }

    /// An iterator over all lines in a byte string, including their
    /// terminators.
    ///
    /// For this iterator, the only line terminator recognized is `\n`. (Since
    /// line terminators are included, this also handles `\r\n` line endings.)
    ///
    /// Line terminators are only included if they are present in the original
    /// byte string. For example, the last line in a byte string may not end
    /// with a line terminator.
    ///
    /// Concatenating all elements yielded by this iterator is guaranteed to
    /// yield the original byte string.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{B, BStr};
    ///
    /// let s = B("\
    /// foo
    ///
    /// bar\r
    /// baz
    ///
    ///
    /// quux");
    /// let lines: Vec<&BStr> = s.lines_with_terminator().collect();
    /// assert_eq!(lines, vec![
    ///     "foo\n", "\n", "bar\r\n", "baz\n", "\n", "\n", "quux",
    /// ]);
    /// ```
    #[inline]
    pub fn lines_with_terminator(&self) -> LinesWithTerminator {
        LinesWithTerminator::new(self)
    }

    /// Return a byte string slice with leading and trailing whitespace
    /// removed.
    ///
    /// Whitespace is defined according to the terms of the `White_Space`
    /// Unicode property.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let s = B(" foo\tbar\t\u{2003}\n");
    /// assert_eq!(s.trim(), "foo\tbar");
    /// ```
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn trim(&self) -> &BStr {
        self.trim_start().trim_end()
    }

    /// Return a byte string slice with leading whitespace removed.
    ///
    /// Whitespace is defined according to the terms of the `White_Space`
    /// Unicode property.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let s = B(" foo\tbar\t\u{2003}\n");
    /// assert_eq!(s.trim_start(), "foo\tbar\t\u{2003}\n");
    /// ```
    #[inline]
    pub fn trim_start(&self) -> &BStr {
        self.trim_start_imp()
    }

    #[cfg(feature = "unicode")]
    #[inline]
    fn trim_start_imp(&self) -> &BStr {
        let start = whitespace_len_fwd(self.as_bytes());
        &self[start..]
    }

    #[cfg(not(feature = "unicode"))]
    #[inline]
    fn trim_start_imp(&self) -> &BStr {
        self.trim_start_with(|c| c.is_whitespace())
    }

    /// Return a byte string slice with trailing whitespace removed.
    ///
    /// Whitespace is defined according to the terms of the `White_Space`
    /// Unicode property.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let s = B(" foo\tbar\t\u{2003}\n");
    /// assert_eq!(s.trim_end(), " foo\tbar");
    /// ```
    #[inline]
    pub fn trim_end(&self) -> &BStr {
        self.trim_end_imp()
    }

    #[cfg(feature = "unicode")]
    #[inline]
    fn trim_end_imp(&self) -> &BStr {
        let end = whitespace_len_rev(self.as_bytes());
        &self[..end]
    }

    #[cfg(not(feature = "unicode"))]
    #[inline]
    fn trim_end_imp(&self) -> &BStr {
        self.trim_end_with(|c| c.is_whitespace())
    }

    /// Return a byte string slice with leading and trailing characters
    /// satisfying the given predicate removed.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let s = B("123foo5bar789");
    /// assert_eq!(s.trim_with(|c| c.is_numeric()), "foo5bar");
    /// ```
    #[inline]
    pub fn trim_with<F: FnMut(char) -> bool>(&self, mut trim: F) -> &BStr {
        self.trim_start_with(&mut trim).trim_end_with(&mut trim)
    }

    /// Return a byte string slice with leading characters satisfying the given
    /// predicate removed.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let s = B("123foo5bar789");
    /// assert_eq!(s.trim_start_with(|c| c.is_numeric()), "foo5bar789");
    /// ```
    #[inline]
    pub fn trim_start_with<F: FnMut(char) -> bool>(
        &self,
        mut trim: F,
    ) -> &BStr {
        for (s, _, ch) in self.char_indices() {
            if !trim(ch) {
                return &self[s..];
            }
        }
        B("")
    }

    /// Return a byte string slice with trailing characters satisfying the
    /// given predicate removed.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let s = B("123foo5bar");
    /// assert_eq!(s.trim_end_with(|c| c.is_numeric()), "123foo5bar");
    /// ```
    #[inline]
    pub fn trim_end_with<F: FnMut(char) -> bool>(
        &self,
        mut trim: F,
    ) -> &BStr {
        for (_, e, ch) in self.char_indices().rev() {
            if !trim(ch) {
                return &self[..e];
            }
        }
        B("")
    }

    /// Returns a new `BString` containing the lowercase equivalent of this
    /// byte string.
    ///
    /// In this case, lowercase is defined according to the `Lowercase` Unicode
    /// property.
    ///
    /// If invalid UTF-8 is seen, or if a character has no lowercase variant,
    /// then it is written to the given buffer unchanged.
    ///
    /// Note that some characters in this byte string may expand into multiple
    /// characters when changing the case, so the number of bytes written to
    /// the given byte string may not be equivalent to the number of bytes in
    /// this byte string.
    ///
    /// If you'd like to reuse an allocation for performance reasons, then use
    /// [`to_lowercase_into`](#method.to_lowercase_into) instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let s = B("HELLO Β");
    /// assert_eq!("hello β", s.to_lowercase());
    /// ```
    ///
    /// Scripts without case are not changed:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let s = B("农历新年");
    /// assert_eq!("农历新年", s.to_lowercase());
    /// ```
    ///
    /// Invalid UTF-8 remains as is:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let s = B(b"FOO\xFFBAR\xE2\x98BAZ");
    /// assert_eq!(B(b"foo\xFFbar\xE2\x98baz"), s.to_lowercase());
    /// ```
    #[cfg(all(feature = "std", feature = "unicode"))]
    #[inline]
    pub fn to_lowercase(&self) -> BString {
        let mut buf = BString::new();
        self.to_lowercase_into(&mut buf);
        buf
    }

    /// Writes the lowercase equivalent of this byte string into the given
    /// buffer. The buffer is not cleared before written to.
    ///
    /// In this case, lowercase is defined according to the `Lowercase`
    /// Unicode property.
    ///
    /// If invalid UTF-8 is seen, or if a character has no lowercase variant,
    /// then it is written to the given buffer unchanged.
    ///
    /// Note that some characters in this byte string may expand into multiple
    /// characters when changing the case, so the number of bytes written to
    /// the given byte string may not be equivalent to the number of bytes in
    /// this byte string.
    ///
    /// If you don't need to amortize allocation and instead prefer
    /// convenience, then use [`to_lowercase`](#method.to_lowercase) instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let s = B("HELLO Β");
    ///
    /// let mut buf = BString::new();
    /// s.to_lowercase_into(&mut buf);
    /// assert_eq!("hello β", buf);
    /// ```
    ///
    /// Scripts without case are not changed:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let s = B("农历新年");
    ///
    /// let mut buf = BString::new();
    /// s.to_lowercase_into(&mut buf);
    /// assert_eq!("农历新年", buf);
    /// ```
    ///
    /// Invalid UTF-8 remains as is:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let s = B(b"FOO\xFFBAR\xE2\x98BAZ");
    ///
    /// let mut buf = BString::new();
    /// s.to_lowercase_into(&mut buf);
    /// assert_eq!(B(b"foo\xFFbar\xE2\x98baz"), buf);
    /// ```
    #[cfg(all(feature = "std", feature = "unicode"))]
    #[inline]
    pub fn to_lowercase_into(&self, buf: &mut BString) {
        // TODO: This is the best we can do given what std exposes I think.
        // If we roll our own case handling, then we might be able to do this
        // a bit faster. We shouldn't roll our own case handling unless we
        // need to, e.g., for doing caseless matching or case folding.

        // TODO(BUG): This doesn't handle any special casing rules.

        buf.reserve(self.len());
        for (s, e, ch) in self.char_indices() {
            if ch == '\u{FFFD}' {
                buf.push(&self[s..e]);
            } else {
                for upper in ch.to_lowercase() {
                    buf.push_char(upper);
                }
            }
        }
    }

    /// Returns a new `BString` containing the ASCII lowercase equivalent of
    /// this byte string.
    ///
    /// In this case, lowercase is only defined in ASCII letters. Namely, the
    /// letters `A-Z` are converted to `a-z`. All other bytes remain unchanged.
    /// In particular, the length of the byte string returned is always
    /// equivalent to the length of this byte string.
    ///
    /// If you'd like to reuse an allocation for performance reasons, then use
    /// [`make_ascii_lowercase`](#method.make_ascii_lowercase) to perform
    /// the conversion in place.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let s = B("HELLO Β");
    /// assert_eq!("hello Β", s.to_ascii_lowercase());
    /// ```
    ///
    /// Invalid UTF-8 remains as is:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let s = B(b"FOO\xFFBAR\xE2\x98BAZ");
    /// assert_eq!(B(b"foo\xFFbar\xE2\x98baz"), s.to_ascii_lowercase());
    /// ```
    #[cfg(feature = "std")]
    #[inline]
    pub fn to_ascii_lowercase(&self) -> BString {
        BString::from(self.as_bytes().to_ascii_lowercase())
    }

    /// Convert this byte string to its lowercase ASCII equivalent in place.
    ///
    /// In this case, lowercase is only defined in ASCII letters. Namely, the
    /// letters `A-Z` are converted to `a-z`. All other bytes remain unchanged.
    ///
    /// If you don't need to do the conversion in
    /// place and instead prefer convenience, then use
    /// [`to_ascii_lowercase`](#method.to_ascii_lowercase) instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("HELLO Β");
    /// s.make_ascii_lowercase();
    /// assert_eq!("hello Β", s);
    /// ```
    ///
    /// Invalid UTF-8 remains as is:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let mut s = BString::from_slice(b"FOO\xFFBAR\xE2\x98BAZ");
    /// s.make_ascii_lowercase();
    /// assert_eq!(B(b"foo\xFFbar\xE2\x98baz"), s);
    /// ```
    #[inline]
    pub fn make_ascii_lowercase(&mut self) {
        self.as_bytes_mut().make_ascii_lowercase();
    }

    /// Returns a new `BString` containing the uppercase equivalent of this
    /// byte string.
    ///
    /// In this case, uppercase is defined according to the `Uppercase`
    /// Unicode property.
    ///
    /// If invalid UTF-8 is seen, or if a character has no uppercase variant,
    /// then it is written to the given buffer unchanged.
    ///
    /// Note that some characters in this byte string may expand into multiple
    /// characters when changing the case, so the number of bytes written to
    /// the given byte string may not be equivalent to the number of bytes in
    /// this byte string.
    ///
    /// If you'd like to reuse an allocation for performance reasons, then use
    /// [`to_uppercase_into`](#method.to_uppercase_into) instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let s = B("hello β");
    /// assert_eq!("HELLO Β", s.to_uppercase());
    /// ```
    ///
    /// Scripts without case are not changed:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let s = B("农历新年");
    /// assert_eq!("农历新年", s.to_uppercase());
    /// ```
    ///
    /// Invalid UTF-8 remains as is:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let s = B(b"foo\xFFbar\xE2\x98baz");
    /// assert_eq!(B(b"FOO\xFFBAR\xE2\x98BAZ"), s.to_uppercase());
    /// ```
    #[cfg(all(feature = "std", feature = "unicode"))]
    #[inline]
    pub fn to_uppercase(&self) -> BString {
        let mut buf = BString::new();
        self.to_uppercase_into(&mut buf);
        buf
    }

    /// Writes the uppercase equivalent of this byte string into the given
    /// buffer. The buffer is not cleared before written to.
    ///
    /// In this case, uppercase is defined according to the `Uppercase`
    /// Unicode property.
    ///
    /// If invalid UTF-8 is seen, or if a character has no uppercase variant,
    /// then it is written to the given buffer unchanged.
    ///
    /// Note that some characters in this byte string may expand into multiple
    /// characters when changing the case, so the number of bytes written to
    /// the given byte string may not be equivalent to the number of bytes in
    /// this byte string.
    ///
    /// If you don't need to amortize allocation and instead prefer
    /// convenience, then use [`to_uppercase`](#method.to_uppercase) instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let s = B("hello β");
    ///
    /// let mut buf = BString::new();
    /// s.to_uppercase_into(&mut buf);
    /// assert_eq!("HELLO Β", buf);
    /// ```
    ///
    /// Scripts without case are not changed:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let s = B("农历新年");
    ///
    /// let mut buf = BString::new();
    /// s.to_uppercase_into(&mut buf);
    /// assert_eq!("农历新年", buf);
    /// ```
    ///
    /// Invalid UTF-8 remains as is:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let s = B(b"foo\xFFbar\xE2\x98baz");
    ///
    /// let mut buf = BString::new();
    /// s.to_uppercase_into(&mut buf);
    /// assert_eq!(B(b"FOO\xFFBAR\xE2\x98BAZ"), buf);
    /// ```
    #[cfg(all(feature = "std", feature = "unicode"))]
    #[inline]
    pub fn to_uppercase_into(&self, buf: &mut BString) {
        // TODO: This is the best we can do given what std exposes I think.
        // If we roll our own case handling, then we might be able to do this
        // a bit faster. We shouldn't roll our own case handling unless we
        // need to, e.g., for doing caseless matching or case folding.
        buf.reserve(self.len());
        for (s, e, ch) in self.char_indices() {
            if ch == '\u{FFFD}' {
                buf.push(&self[s..e]);
            } else if ch.is_ascii() {
                buf.push_char(ch.to_ascii_uppercase());
            } else {
                for upper in ch.to_uppercase() {
                    buf.push_char(upper);
                }
            }
        }
    }

    /// Returns a new `BString` containing the ASCII uppercase equivalent of
    /// this byte string.
    ///
    /// In this case, uppercase is only defined in ASCII letters. Namely, the
    /// letters `a-z` are converted to `A-Z`. All other bytes remain unchanged.
    /// In particular, the length of the byte string returned is always
    /// equivalent to the length of this byte string.
    ///
    /// If you'd like to reuse an allocation for performance reasons, then use
    /// [`make_ascii_uppercase`](#method.make_ascii_uppercase) to perform
    /// the conversion in place.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let s = B("hello β");
    /// assert_eq!("HELLO β", s.to_ascii_uppercase());
    /// ```
    ///
    /// Invalid UTF-8 remains as is:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let s = B(b"foo\xFFbar\xE2\x98baz");
    /// assert_eq!(B(b"FOO\xFFBAR\xE2\x98BAZ"), s.to_ascii_uppercase());
    /// ```
    #[cfg(feature = "std")]
    #[inline]
    pub fn to_ascii_uppercase(&self) -> BString {
        BString::from(self.as_bytes().to_ascii_uppercase())
    }

    /// Convert this byte string to its uppercase ASCII equivalent in place.
    ///
    /// In this case, uppercase is only defined in ASCII letters. Namely, the
    /// letters `a-z` are converted to `A-Z`. All other bytes remain unchanged.
    ///
    /// If you don't need to do the conversion in
    /// place and instead prefer convenience, then use
    /// [`to_ascii_uppercase`](#method.to_ascii_uppercase) instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("hello β");
    /// s.make_ascii_uppercase();
    /// assert_eq!("HELLO β", s);
    /// ```
    ///
    /// Invalid UTF-8 remains as is:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let mut s = BString::from_slice(b"foo\xFFbar\xE2\x98baz");
    /// s.make_ascii_uppercase();
    /// assert_eq!(B(b"FOO\xFFBAR\xE2\x98BAZ"), s);
    /// ```
    #[inline]
    pub fn make_ascii_uppercase(&mut self) {
        self.as_bytes_mut().make_ascii_uppercase();
    }

    /// Reverse the bytes in this string, in place.
    ///
    /// Note that this is not necessarily a well formed operation. For example,
    /// if this byte string contains valid UTF-8 that isn't ASCII, then
    /// reversing the string will likely result in invalid UTF-8 and otherwise
    /// non-sensical content.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("hello");
    /// s.reverse_bytes();
    /// assert_eq!(s, "olleh");
    /// ```
    #[inline]
    pub fn reverse_bytes(&mut self) {
        self.as_bytes_mut().reverse();
    }

    /// Reverse the codepoints in this string, in place.
    ///
    /// If this byte string is valid UTF-8, then its reversal by codepoint
    /// is also guaranteed to be valid UTF-8.
    ///
    /// This operation is equivalent to the following, but without allocating:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("foo☃bar");
    ///
    /// let mut chars: Vec<char> = s.chars().collect();
    /// chars.reverse();
    ///
    /// let reversed: String = chars.into_iter().collect();
    /// assert_eq!(reversed, "rab☃oof");
    /// ```
    ///
    /// Note that this is not necessarily a well formed operation. For example,
    /// if this byte string contains grapheme clusters with more than one
    /// codepoint, then those grapheme clusters will not necessarily be
    /// preserved. If you'd like to preserve grapheme clusters, then use
    /// [`reverse_graphemes`](#method.reverse_graphemes) instead.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("foo☃bar");
    /// s.reverse_chars();
    /// assert_eq!(s, "rab☃oof");
    /// ```
    ///
    /// This example shows that not all reversals lead to a well formed string.
    /// For example, in this case, combining marks are used to put accents over
    /// some letters, and those accent marks must appear after the codepoints
    /// they modify.
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let mut s = BString::from("résumé");
    /// s.reverse_chars();
    /// assert_eq!(s, B(b"\xCC\x81emus\xCC\x81er"));
    /// ```
    ///
    /// A word of warning: the above example relies on the fact that
    /// `résumé` is in decomposed normal form, which means there are separate
    /// codepoints for the accents above `e`. If it is instead in composed
    /// normal form, then the example works:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let mut s = BString::from("résumé");
    /// s.reverse_chars();
    /// assert_eq!(s, "émusér");
    /// ```
    ///
    /// The point here is to be cautious and not assume that just because
    /// `reverse_chars` works in one case, that it therefore works in all
    /// cases.
    #[inline]
    pub fn reverse_chars(&mut self) {
        let mut i = 0;
        loop {
            let (_, size) = utf8::decode(self[i..].as_bytes());
            if size == 0 {
                break;
            }
            if size > 1 {
                self[i..i + size].reverse_bytes();
            }
            i += size;
        }
        self.reverse_bytes();
    }

    /// Reverse the graphemes in this string, in place.
    ///
    /// If this byte string is valid UTF-8, then its reversal by grapheme
    /// is also guaranteed to be valid UTF-8.
    ///
    /// This operation is equivalent to the following, but without allocating:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("foo☃bar");
    ///
    /// let mut graphemes: Vec<&str> = s.graphemes().collect();
    /// graphemes.reverse();
    ///
    /// let reversed = graphemes.concat();
    /// assert_eq!(reversed, "rab☃oof");
    /// ```
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("foo☃bar");
    /// s.reverse_graphemes();
    /// assert_eq!(s, "rab☃oof");
    /// ```
    ///
    /// This example shows how this correctly handles grapheme clusters,
    /// unlike `reverse_chars`.
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("résumé");
    /// s.reverse_graphemes();
    /// assert_eq!(s, "émusér");
    /// ```
    #[cfg(feature = "unicode")]
    #[inline]
    pub fn reverse_graphemes(&mut self) {
        use unicode::decode_grapheme;

        let mut i = 0;
        loop {
            let (_, size) = decode_grapheme(&self[i..]);
            if size == 0 {
                break;
            }
            if size > 1 {
                self[i..i + size].reverse_bytes();
            }
            i += size;
        }
        self.reverse_bytes();
    }

    /// Returns true if and only if every byte in this byte string is ASCII.
    ///
    /// ASCII is an encoding that defines 128 codepoints. A byte corresponds to
    /// an ASCII codepoint if and only if it is in the inclusive range
    /// `[0, 127]`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// assert!(B("abc").is_ascii());
    /// assert!(!B("☃βツ").is_ascii());
    /// assert!(!B(b"\xFF").is_ascii());
    /// ```
    #[inline]
    pub fn is_ascii(&self) -> bool {
        ascii::first_non_ascii_byte(&self.bytes) == self.len()
    }

    /// Returns true if and only if the entire byte string is valid UTF-8.
    ///
    /// If you need location information about where a byte string's first
    /// invalid UTF-8 byte is, then use the [`to_str`](#method.to_str) method.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// assert!(B("abc").is_utf8());
    /// assert!(B("☃βツ").is_utf8());
    /// // invalid bytes
    /// assert!(!B(b"abc\xFF").is_utf8());
    /// // surrogate encoding
    /// assert!(!B(b"\xED\xA0\x80").is_utf8());
    /// // incomplete sequence
    /// assert!(!B(b"\xF0\x9D\x9Ca").is_utf8());
    /// // overlong sequence
    /// assert!(!B(b"\xF0\x82\x82\xAC").is_utf8());
    /// ```
    #[inline]
    pub fn is_utf8(&self) -> bool {
        utf8::validate(self.as_bytes()).is_ok()
    }

    /// Divides this byte string into two at an index.
    ///
    /// The first byte string will contain all bytes at indices `[0, at)`, and
    /// the second byte string will contain all bytes at indices `[at, len)`.
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// assert_eq!(B("foobar").split_at(3), (B("foo"), B("bar")));
    /// assert_eq!(B("foobar").split_at(0), (B(""), B("foobar")));
    /// assert_eq!(B("foobar").split_at(6), (B("foobar"), B("")));
    /// ```
    #[inline]
    pub fn split_at(&self, at: usize) -> (&BStr, &BStr) {
        let (left, right) = self.as_bytes().split_at(at);
        (BStr::new(left), BStr::new(right))
    }

    /// Divides this mutable byte string into two at an index.
    ///
    /// The first byte string will contain all bytes at indices `[0, at)`, and
    /// the second byte string will contain all bytes at indices `[at, len)`.
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::{B, BString};
    ///
    /// let mut b = BString::from("foobar");
    /// {
    ///     let (left, right) = b.split_at_mut(3);
    ///     left[2] = b'z';
    ///     right[2] = b'z';
    /// }
    /// assert_eq!(b, B("fozbaz"));
    /// ```
    #[inline]
    pub fn split_at_mut(&mut self, at: usize) -> (&mut BStr, &mut BStr) {
        let (left, right) = self.as_bytes_mut().split_at_mut(at);
        (BStr::new_mut(left), BStr::new_mut(right))
    }

    /// Retrieve a reference to a byte or a subslice, depending on the type of
    /// the index given.
    ///
    /// If given a position, this returns a reference to the byte at that
    /// position, if it exists.
    ///
    /// If given a range, this returns the slice of bytes corresponding to that
    /// range in this byte string.
    ///
    /// In the case of invalid indices, this returns `None`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let s = B("baz");
    /// assert_eq!(s.get(1), Some(&b'a'));
    /// assert_eq!(s.get(0..2), Some(B("ba")));
    /// assert_eq!(s.get(2..), Some(B("z")));
    /// assert_eq!(s.get(1..=2), Some(B("az")));
    /// ```
    #[inline]
    pub fn get<I: SliceIndex>(&self, at: I) -> Option<&I::Output> {
        at.get(self)
    }

    /// Retrieve a mutable reference to a byte or a subslice, depending on the
    /// type of the index given.
    ///
    /// If given a position, this returns a reference to the byte at that
    /// position, if it exists.
    ///
    /// If given a range, this returns the slice of bytes corresponding to that
    /// range in this byte string.
    ///
    /// In the case of invalid indices, this returns `None`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("baz");
    /// if let Some(mut slice) = s.get_mut(1..) {
    ///     slice[0] = b'o';
    ///     slice[1] = b'p';
    /// }
    /// assert_eq!(s, "bop");
    /// ```
    #[inline]
    pub fn get_mut<I: SliceIndex>(&mut self, at: I) -> Option<&mut I::Output> {
        at.get_mut(self)
    }

    /// Retrieve a reference to a byte or a subslice, depending on the type of
    /// the index given, while explicitly eliding bounds checks.
    ///
    /// If given a position, this returns a reference to the byte at that
    /// position, if it exists.
    ///
    /// If given a range, this returns the slice of bytes corresponding to that
    /// range in this byte string.
    ///
    /// In the case of invalid indices, this returns `None`.
    ///
    /// # Safety
    ///
    /// Callers must ensure that the supplied bounds are correct. If they
    /// are out of bounds, then this results in undefined behavior. For a
    /// safe alternative, use [`get`](#method.get).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let s = B("baz");
    /// unsafe {
    ///     assert_eq!(s.get_unchecked(1), &b'a');
    ///     assert_eq!(s.get_unchecked(0..2), "ba");
    ///     assert_eq!(s.get_unchecked(2..), "z");
    ///     assert_eq!(s.get_unchecked(1..=2), "az");
    /// }
    /// ```
    pub unsafe fn get_unchecked<I: SliceIndex>(&self, at: I) -> &I::Output {
        at.get_unchecked(self)
    }

    /// Retrieve a mutable reference to a byte or a subslice, depending on the
    /// type of the index given, while explicitly eliding bounds checks.
    ///
    /// If given a position, this returns a reference to the byte at that
    /// position, if it exists.
    ///
    /// If given a range, this returns the slice of bytes corresponding to that
    /// range in this byte string.
    ///
    /// In the case of invalid indices, this returns `None`.
    ///
    /// # Safety
    ///
    /// Callers must ensure that the supplied bounds are correct. If they
    /// are out of bounds, then this results in undefined behavior. For a
    /// safe alternative, use [`get_mut`](#method.get_mut).
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BString;
    ///
    /// let mut s = BString::from("baz");
    /// {
    ///     let mut slice = unsafe { s.get_unchecked_mut(1..) };
    ///     slice[0] = b'o';
    ///     slice[1] = b'p';
    /// }
    /// assert_eq!(s, "bop");
    /// ```
    pub unsafe fn get_unchecked_mut<I: SliceIndex>(
        &mut self,
        at: I,
    ) -> &mut I::Output {
        at.get_unchecked_mut(self)
    }

    /// Returns the last byte in this byte string, if it's non-empty. If this
    /// byte string is empty, this returns `None`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// assert_eq!(Some(b'z'), B("baz").last());
    /// assert_eq!(None, B("").last());
    /// ```
    #[inline]
    pub fn last(&self) -> Option<u8> {
        self.get(self.len().saturating_sub(1)).map(|&b| b)
    }

    /// Copies elements from one part of the slice to another part of itself,
    /// where the parts may be overlapping.
    ///
    /// `src` is the range within this byte string to copy from, while `dest`
    /// is the starting index of the range within this byte string to copy to.
    /// The length indicated by `src` must be less than or equal to the number
    /// of bytes from `dest` to the end of the byte string.
    ///
    /// # Panics
    ///
    /// Panics if either range is out of bounds, or if `src` is too big to fit
    /// into `dest`, or if the end of `src` is before the start.
    ///
    /// # Examples
    ///
    /// Copying four bytes within a byte string:
    ///
    /// ```
    /// use bstr::BStr;
    ///
    /// let mut buf = *b"Hello, World!";
    /// let s = BStr::new_mut(&mut buf);
    /// s.copy_within(1..5, 8);
    /// assert_eq!(s, "Hello, Wello!");
    /// ```
    #[inline]
    pub fn copy_within<R>(
        &mut self,
        src: R,
        dest: usize,
    ) where R: ops::RangeBounds<usize>
    {
        let src_start = match src.start_bound() {
            ops::Bound::Included(&n) => n,
            ops::Bound::Excluded(&n) => {
                n.checked_add(1).expect("attempted to index slice beyond max")
            }
            ops::Bound::Unbounded => 0,
        };
        let src_end = match src.end_bound() {
            ops::Bound::Included(&n) => {
                n.checked_add(1).expect("attempted to index slice beyond max")
            }
            ops::Bound::Excluded(&n) => n,
            ops::Bound::Unbounded => self.len(),
        };
        assert!(src_start <= src_end, "src end is before src start");
        assert!(src_end <= self.len(), "src is out of bounds");
        let count = src_end - src_start;
        assert!(dest <= self.len() - count, "dest is out of bounds");

        // SAFETY: This is safe because we use ptr::copy to handle overlapping
        // copies, and is also safe because we've checked all the bounds above.
        // Finally, we are only dealing with u8 data, which is Copy, which
        // means we can copy without worrying about ownership/destructors.
        unsafe {
            ptr::copy(
                self.get_unchecked(src_start),
                self.get_unchecked_mut(dest),
                count,
            );
        }
    }

    /// Returns a raw pointer to this byte string's underlying bytes.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the byte string outlives the pointer this
    /// function returns, or else it will end up pointing to garbage.
    ///
    /// Modifying the container (like a `BString`) referenced by this byte
    /// string may cause its buffer to be reallocated, which would also make
    /// any pointers to it invalid.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::B;
    ///
    /// let s = B("hello");
    /// let p = s.as_ptr();
    ///
    /// unsafe {
    ///     assert_eq!(*p.add(2), b'l');
    /// }
    /// ```
    #[inline]
    pub fn as_ptr(&self) -> *const u8 {
        self.as_bytes().as_ptr()
    }

    /// Returns a raw mutable pointer to this byte string's underlying bytes.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the byte string outlives the pointer this
    /// function returns, or else it will end up pointing to garbage.
    ///
    /// Modifying the container (like a `BString`) referenced by this byte
    /// string may cause its buffer to be reallocated, which would also make
    /// any pointers to it invalid.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::BStr;
    ///
    /// let mut buf = &mut [b'h', b'e', b'l', b'l', b'o'];
    /// let mut s = BStr::new_mut(buf);
    /// let p = s.as_mut_ptr();
    ///
    /// unsafe {
    ///     *p.add(2) = b'Z';
    /// }
    /// assert_eq!("heZlo", s);
    /// ```
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.as_bytes_mut().as_mut_ptr()
    }
}

/// A single substring searcher fixed to a particular needle.
///
/// The purpose of this type is to permit callers to construct a substring
/// searcher that can be used to search haystacks without the overhead of
/// constructing the searcher in the first place. This is a somewhat niche
/// concern when it's necessary to re-use the same needle to search multiple
/// different haystacks with as little overhead as possible. In general, using
/// [`BStr::find`](struct.BStr.html#method.find)
/// or
/// [`BStr::find_iter`](struct.BStr.html#method.find_iter)
/// is good enough, but `Finder` is useful when you can meaningfully observe
/// searcher construction time in a profile.
///
/// When the `std` feature is enabled, then this type has an `into_owned`
/// version which permits building a `Finder` that is not connected to the
/// lifetime of its needle.
#[derive(Clone, Debug)]
pub struct Finder<'a> {
    searcher: TwoWay<'a>,
}

impl<'a> Finder<'a> {
    /// Create a new finder for the given needle.
    #[inline]
    pub fn new<B: ?Sized + AsRef<[u8]>>(needle: &'a B) -> Finder<'a> {
        Finder { searcher: TwoWay::forward(BStr::new(needle)) }
    }

    /// Convert this finder into its owned variant, such that it no longer
    /// borrows the needle.
    ///
    /// If this is already an owned finder, then this is a no-op. Otherwise,
    /// this copies the needle.
    ///
    /// This is only available when the `std` feature is enabled.
    #[cfg(feature = "std")]
    #[inline]
    pub fn into_owned(self) -> Finder<'static> {
        Finder { searcher: self.searcher.into_owned() }
    }

    /// Returns the needle that this finder searches for.
    ///
    /// Note that the lifetime of the needle returned is tied to the lifetime
    /// of the finder, and may be shorter than the `'a` lifetime. Namely, a
    /// finder's needle can be either borrowed or owned, so the lifetime of the
    /// needle returned must necessarily be the shorter of the two.
    #[inline]
    pub fn needle(&self) -> &BStr {
        self.searcher.needle()
    }

    /// Returns the index of the first occurrence of this needle in the given
    /// haystack.
    ///
    /// The haystack may be any type that can be cheaply converted into a
    /// `&[u8]`. This includes, but is not limited to, `&str`, `&BStr`, and of
    /// course, `&[u8]` itself.
    ///
    /// # Complexity
    ///
    /// This routine is guaranteed to have worst case linear time complexity
    /// with respect to both the needle and the haystack. That is, this runs
    /// in `O(needle.len() + haystack.len())` time.
    ///
    /// This routine is also guaranteed to have worst case constant space
    /// complexity.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::Finder;
    ///
    /// let haystack = "foo bar baz";
    /// assert_eq!(Some(0), Finder::new("foo").find(haystack));
    /// assert_eq!(Some(4), Finder::new("bar").find(haystack));
    /// assert_eq!(None, Finder::new("quux").find(haystack));
    /// ```
    #[inline]
    pub fn find<B: AsRef<[u8]>>(&self, haystack: B) -> Option<usize> {
        self.searcher.find(BStr::new(haystack.as_ref()))
    }
}

/// A single substring reverse searcher fixed to a particular needle.
///
/// The purpose of this type is to permit callers to construct a substring
/// searcher that can be used to search haystacks without the overhead of
/// constructing the searcher in the first place. This is a somewhat niche
/// concern when it's necessary to re-use the same needle to search multiple
/// different haystacks with as little overhead as possible. In general, using
/// [`BStr::rfind`](struct.BStr.html#method.rfind)
/// or
/// [`BStr::rfind_iter`](struct.BStr.html#method.rfind_iter)
/// is good enough, but `FinderReverse` is useful when you can meaningfully
/// observe searcher construction time in a profile.
///
/// When the `std` feature is enabled, then this type has an `into_owned`
/// version which permits building a `FinderReverse` that is not connected to
/// the lifetime of its needle.
#[derive(Clone, Debug)]
pub struct FinderReverse<'a> {
    searcher: TwoWay<'a>,
}

impl<'a> FinderReverse<'a> {
    /// Create a new reverse finder for the given needle.
    #[inline]
    pub fn new<B: ?Sized + AsRef<[u8]>>(needle: &'a B) -> FinderReverse<'a> {
        FinderReverse { searcher: TwoWay::reverse(BStr::new(needle)) }
    }

    /// Convert this finder into its owned variant, such that it no longer
    /// borrows the needle.
    ///
    /// If this is already an owned finder, then this is a no-op. Otherwise,
    /// this copies the needle.
    ///
    /// This is only available when the `std` feature is enabled.
    #[cfg(feature = "std")]
    #[inline]
    pub fn into_owned(self) -> FinderReverse<'static> {
        FinderReverse { searcher: self.searcher.into_owned() }
    }

    /// Returns the needle that this finder searches for.
    ///
    /// Note that the lifetime of the needle returned is tied to the lifetime
    /// of this finder, and may be shorter than the `'a` lifetime. Namely,
    /// a finder's needle can be either borrowed or owned, so the lifetime of
    /// the needle returned must necessarily be the shorter of the two.
    #[inline]
    pub fn needle(&self) -> &BStr {
        self.searcher.needle()
    }

    /// Returns the index of the last occurrence of this needle in the given
    /// haystack.
    ///
    /// The haystack may be any type that can be cheaply converted into a
    /// `&[u8]`. This includes, but is not limited to, `&str`, `&BStr`, and of
    /// course, `&[u8]` itself.
    ///
    /// # Complexity
    ///
    /// This routine is guaranteed to have worst case linear time complexity
    /// with respect to both the needle and the haystack. That is, this runs
    /// in `O(needle.len() + haystack.len())` time.
    ///
    /// This routine is also guaranteed to have worst case constant space
    /// complexity.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use bstr::FinderReverse;
    ///
    /// let haystack = "foo bar baz";
    /// assert_eq!(Some(0), FinderReverse::new("foo").rfind(haystack));
    /// assert_eq!(Some(4), FinderReverse::new("bar").rfind(haystack));
    /// assert_eq!(None, FinderReverse::new("quux").rfind(haystack));
    /// ```
    #[inline]
    pub fn rfind<B: AsRef<[u8]>>(&self, haystack: B) -> Option<usize> {
        self.searcher.rfind(BStr::new(haystack.as_ref()))
    }
}

/// An iterator over non-overlapping substring matches.
///
/// Matches are reported by the byte offset at which they begin.
///
/// `'a` is the shorter of two lifetimes: the byte string being searched or the
/// byte string being looked for.
#[derive(Debug)]
pub struct Find<'a> {
    haystack: &'a BStr,
    prestate: PrefilterState,
    searcher: TwoWay<'a>,
    pos: usize,
}

impl<'a> Find<'a> {
    fn new(haystack: &'a BStr, needle: &'a BStr) -> Find<'a> {
        let searcher = TwoWay::forward(needle);
        let prestate = searcher.prefilter_state();
        Find { haystack, prestate, searcher, pos: 0 }
    }
}

impl<'a> Iterator for Find<'a> {
    type Item = usize;

    #[inline]
    fn next(&mut self) -> Option<usize> {
        if self.pos > self.haystack.len() {
            return None;
        }
        let result = self.searcher.find_with(
            &mut self.prestate,
            &self.haystack[self.pos..],
        );
        match result {
            None => None,
            Some(i) => {
                let pos = self.pos + i;
                self.pos = pos + cmp::max(1, self.searcher.needle().len());
                Some(pos)
            }
        }
    }
}

/// An iterator over non-overlapping substring matches in reverse.
///
/// Matches are reported by the byte offset at which they begin.
///
/// `'a` is the shorter of two lifetimes: the byte string being searched or the
/// byte string being looked for.
#[derive(Debug)]
pub struct FindReverse<'a> {
    haystack: &'a BStr,
    prestate: PrefilterState,
    searcher: TwoWay<'a>,
    /// When searching with an empty needle, this gets set to `None` after
    /// we've yielded the last element at `0`.
    pos: Option<usize>,
}

impl<'a> FindReverse<'a> {
    fn new(haystack: &'a BStr, needle: &'a BStr) -> FindReverse<'a> {
        let searcher = TwoWay::reverse(needle);
        let prestate = searcher.prefilter_state();
        let pos = Some(haystack.len());
        FindReverse { haystack, prestate, searcher, pos }
    }

    fn haystack(&self) -> &'a BStr {
        self.haystack
    }

    fn needle(&self) -> &BStr {
        self.searcher.needle()
    }
}

impl<'a> Iterator for FindReverse<'a> {
    type Item = usize;

    #[inline]
    fn next(&mut self) -> Option<usize> {
        let pos = match self.pos {
            None => return None,
            Some(pos) => pos,
        };
        let result = self.searcher.rfind_with(
            &mut self.prestate,
            &self.haystack[..pos],
        );
        match result {
            None => None,
            Some(i) => {
                if pos == i {
                    self.pos = pos.checked_sub(1);
                } else {
                    self.pos = Some(i);
                }
                Some(i)
            }
        }
    }
}

/// An iterator over the bytes in a byte string.
///
/// `'a` is the lifetime of the byte string being traversed.
#[derive(Debug)]
pub struct Bytes<'a> {
    it: slice::Iter<'a, u8>,
}

impl<'a> Iterator for Bytes<'a> {
    type Item = u8;

    #[inline]
    fn next(&mut self) -> Option<u8> {
        self.it.next().map(|&b| b)
    }
}

impl<'a> DoubleEndedIterator for Bytes<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<u8> {
        self.it.next_back().map(|&b| b)
    }
}

impl<'a> ExactSizeIterator for Bytes<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.it.len()
    }
}

/// An iterator over the fields in a byte string, separated by whitespace.
///
/// This iterator splits on contiguous runs of whitespace, such that the fields
/// in `foo\t\t\n  \nbar` are `foo` and `bar`.
///
/// `'a` is the lifetime of the byte string being split.
#[derive(Debug)]
pub struct Fields<'a> {
    it: FieldsWith<'a, fn(char) -> bool>,
}

impl<'a> Fields<'a> {
    fn new(bytes: &'a BStr) -> Fields<'a> {
        Fields { it: bytes.fields_with(|ch| ch.is_whitespace()) }
    }
}

impl<'a> Iterator for Fields<'a> {
    type Item = &'a BStr;

    #[inline]
    fn next(&mut self) -> Option<&'a BStr> {
        self.it.next()
    }
}

/// An iterator over fields in the byte string, separated by a predicate over
/// codepoints.
///
/// This iterator splits a byte string based on its predicate function such
/// that the elements returned are separated by contiguous runs of codepoints
/// for which the predicate returns true.
///
/// `'a` is the lifetime of the byte string being split, while `F` is the type
/// of the predicate, i.e., `FnMut(char) -> bool`.
#[derive(Debug)]
pub struct FieldsWith<'a, F> {
    f: F,
    bytes: &'a BStr,
    chars: CharIndices<'a>,
}

impl<'a, F: FnMut(char) -> bool> FieldsWith<'a, F> {
    fn new(bytes: &'a BStr, f: F) -> FieldsWith<'a, F> {
        FieldsWith {
            f: f,
            bytes: bytes,
            chars: bytes.char_indices(),
        }
    }
}

impl<'a, F: FnMut(char) -> bool> Iterator for FieldsWith<'a, F> {
    type Item = &'a BStr;

    #[inline]
    fn next(&mut self) -> Option<&'a BStr> {
        let (start, mut end);
        loop {
            match self.chars.next() {
                None => return None,
                Some((s, e, ch)) => {
                    if !(self.f)(ch) {
                        start = s;
                        end = e;
                        break;
                    }
                }
            }
        }
        while let Some((_, e, ch)) = self.chars.next() {
            if (self.f)(ch) {
                break;
            }
            end = e;
        }
        Some(&self.bytes[start..end])
    }
}

/// An iterator over substrings in a byte string, split by a separator.
///
/// `'a` is the lifetime of the byte string being split, while `F` is the type
/// of the predicate, i.e., `FnMut(char) -> bool`.
#[derive(Debug)]
pub struct Split<'a> {
    finder: Find<'a>,
    /// The end position of the previous match of our splitter. The element
    /// we yield corresponds to the substring starting at `last` up to the
    /// beginning of the next match of the splitter.
    last: usize,
    /// Only set when iteration is complete. A corner case here is when a
    /// splitter is matched at the end of the haystack. At that point, we still
    /// need to yield an empty string following it.
    done: bool,
}

impl<'a> Split<'a> {
    fn new(haystack: &'a BStr, splitter: &'a BStr) -> Split<'a> {
        let finder = haystack.find_iter(splitter);
        Split { finder, last: 0, done: false }
    }
}

impl<'a> Iterator for Split<'a> {
    type Item = &'a BStr;

    #[inline]
    fn next(&mut self) -> Option<&'a BStr> {
        let haystack = self.finder.haystack;
        match self.finder.next() {
            Some(start) => {
                let next = &haystack[self.last..start];
                self.last = start + self.finder.searcher.needle().len();
                Some(next)
            }
            None => {
                if self.last >= haystack.len() {
                    if !self.done {
                        self.done = true;
                        Some(B(""))
                    } else {
                        None
                    }
                } else {
                    let s = &haystack[self.last..];
                    self.last = haystack.len();
                    self.done = true;
                    Some(s)
                }
            }
        }
    }
}

/// An iterator over substrings in a byte string, split by a separator, in
/// reverse.
///
/// `'a` is the lifetime of the byte string being split, while `F` is the type
/// of the predicate, i.e., `FnMut(char) -> bool`.
#[derive(Debug)]
pub struct SplitReverse<'a> {
    finder: FindReverse<'a>,
    /// The end position of the previous match of our splitter. The element
    /// we yield corresponds to the substring starting at `last` up to the
    /// beginning of the next match of the splitter.
    last: usize,
    /// Only set when iteration is complete. A corner case here is when a
    /// splitter is matched at the end of the haystack. At that point, we still
    /// need to yield an empty string following it.
    done: bool,
}

impl<'a> SplitReverse<'a> {
    fn new(haystack: &'a BStr, splitter: &'a BStr) -> SplitReverse<'a> {
        let finder = haystack.rfind_iter(splitter);
        SplitReverse { finder, last: haystack.len(), done: false }
    }
}

impl<'a> Iterator for SplitReverse<'a> {
    type Item = &'a BStr;

    #[inline]
    fn next(&mut self) -> Option<&'a BStr> {
        let haystack = self.finder.haystack();
        match self.finder.next() {
            Some(start) => {
                let nlen = self.finder.needle().len();
                let next = &haystack[start + nlen..self.last];
                self.last = start;
                Some(next)
            }
            None => {
                if self.last == 0 {
                    if !self.done {
                        self.done = true;
                        Some(B(""))
                    } else {
                        None
                    }
                } else {
                    let s = &haystack[..self.last];
                    self.last = 0;
                    self.done = true;
                    Some(s)
                }
            }
        }
    }
}

/// An iterator over at most `n` substrings in a byte string, split by a
/// separator.
///
/// `'a` is the lifetime of the byte string being split, while `F` is the type
/// of the predicate, i.e., `FnMut(char) -> bool`.
#[derive(Debug)]
pub struct SplitN<'a> {
    split: Split<'a>,
    limit: usize,
    count: usize,
}

impl<'a> SplitN<'a> {
    fn new(
        haystack: &'a BStr,
        splitter: &'a BStr,
        limit: usize,
    ) -> SplitN<'a> {
        let split = haystack.split(splitter);
        SplitN { split, limit, count: 0 }
    }
}

impl<'a> Iterator for SplitN<'a> {
    type Item = &'a BStr;

    #[inline]
    fn next(&mut self) -> Option<&'a BStr> {
        self.count += 1;
        if self.count > self.limit {
            None
        } else if self.count == self.limit {
            Some(&self.split.finder.haystack[self.split.last..])
        } else {
            self.split.next()
        }
    }
}


/// An iterator over at most `n` substrings in a byte string, split by a
/// separator, in reverse.
///
/// `'a` is the lifetime of the byte string being split, while `F` is the type
/// of the predicate, i.e., `FnMut(char) -> bool`.
#[derive(Debug)]
pub struct SplitNReverse<'a> {
    split: SplitReverse<'a>,
    limit: usize,
    count: usize,
}

impl<'a> SplitNReverse<'a> {
    fn new(
        haystack: &'a BStr,
        splitter: &'a BStr,
        limit: usize,
    ) -> SplitNReverse<'a> {
        let split = haystack.rsplit(splitter);
        SplitNReverse { split, limit, count: 0 }
    }
}

impl<'a> Iterator for SplitNReverse<'a> {
    type Item = &'a BStr;

    #[inline]
    fn next(&mut self) -> Option<&'a BStr> {
        self.count += 1;
        if self.count > self.limit {
            None
        } else if self.count == self.limit {
            Some(&self.split.finder.haystack()[..self.split.last])
        } else {
            self.split.next()
        }
    }
}

/// An iterator over all lines in a byte string, without their terminators.
///
/// For this iterator, the only line terminators recognized are `\r\n` and
/// `\n`.
///
/// `'a` is the lifetime of the byte string being iterated over.
pub struct Lines<'a> {
    it: LinesWithTerminator<'a>,
}

impl<'a> Lines<'a> {
    fn new(bytes: &'a BStr) -> Lines<'a> {
        Lines { it: LinesWithTerminator::new(bytes) }
    }
}

impl<'a> Iterator for Lines<'a> {
    type Item = &'a BStr;

    #[inline]
    fn next(&mut self) -> Option<&'a BStr> {
        let mut line = self.it.next()?;
        if line.last() == Some(b'\n') {
            line = &line[..line.len() - 1];
            if line.last() == Some(b'\r') {
                line = &line[..line.len() - 1];
            }
        }
        Some(line)
    }
}

/// An iterator over all lines in a byte string, including their terminators.
///
/// For this iterator, the only line terminator recognized is `\n`. (Since
/// line terminators are included, this also handles `\r\n` line endings.)
///
/// Line terminators are only included if they are present in the original
/// byte string. For example, the last line in a byte string may not end with
/// a line terminator.
///
/// Concatenating all elements yielded by this iterator is guaranteed to yield
/// the original byte string.
///
/// `'a` is the lifetime of the byte string being iterated over.
pub struct LinesWithTerminator<'a> {
    bytes: &'a BStr,
}

impl<'a> LinesWithTerminator<'a> {
    fn new(bytes: &'a BStr) -> LinesWithTerminator<'a> {
        LinesWithTerminator { bytes }
    }
}

impl<'a> Iterator for LinesWithTerminator<'a> {
    type Item = &'a BStr;

    #[inline]
    fn next(&mut self) -> Option<&'a BStr> {
        match self.bytes.find_byte(b'\n') {
            None if self.bytes.is_empty() => None,
            None => {
                let line = self.bytes;
                self.bytes = B("");
                Some(line)
            }
            Some(end) => {
                let line = &self.bytes[..end + 1];
                self.bytes = &self.bytes[end + 1..];
                Some(line)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use tests::LOSSY_TESTS;
    use super::*;

    #[test]
    fn to_str_lossy() {
        for (i, &(expected, input)) in LOSSY_TESTS.iter().enumerate() {
            let got = B(input).to_str_lossy();
            assert_eq!(
                expected.as_bytes(),
                got.as_bytes(),
                "to_str_lossy(ith: {:?}, given: {:?})",
                i, input,
            );

            let mut got = String::new();
            B(input).to_str_lossy_into(&mut got);
            assert_eq!(
                expected.as_bytes(), got.as_bytes(), "to_str_lossy_into",
            );

            let got = String::from_utf8_lossy(input);
            assert_eq!(expected.as_bytes(), got.as_bytes(), "std");
        }
    }

    #[test]
    #[should_panic]
    fn copy_within_fail1() {
        let mut buf = *b"foobar";
        let s = BStr::new_mut(&mut buf);
        s.copy_within(0..2, 5);
    }

    #[test]
    #[should_panic]
    fn copy_within_fail2() {
        let mut buf = *b"foobar";
        let s = BStr::new_mut(&mut buf);
        s.copy_within(3..2, 0);
    }

    #[test]
    #[should_panic]
    fn copy_within_fail3() {
        let mut buf = *b"foobar";
        let s = BStr::new_mut(&mut buf);
        s.copy_within(5..7, 0);
    }

    #[test]
    #[should_panic]
    fn copy_within_fail4() {
        let mut buf = *b"foobar";
        let s = BStr::new_mut(&mut buf);
        s.copy_within(0..1, 6);
    }
}
