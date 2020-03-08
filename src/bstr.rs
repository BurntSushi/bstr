use core::mem;

/// A wrapper for `&[u8]` that provides convenient string oriented trait impls.
///
/// If you need ownership or a growable byte string buffer, then use
/// [`BString`](struct.BString.html).
///
/// Using a `&BStr` is just like using a `&[u8]`, since `BStr`
/// implements `Deref` to `[u8]`. So all methods available on `[u8]`
/// are also available on `BStr`.
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
#[derive(Hash)]
#[repr(transparent)]
pub struct BStr {
    pub(crate) bytes: [u8],
}

impl BStr {
    #[inline]
    pub(crate) fn new<B: ?Sized + AsRef<[u8]>>(bytes: &B) -> &BStr {
        BStr::from_bytes(bytes.as_ref())
    }

    #[inline]
    pub(crate) fn new_mut<B: ?Sized + AsMut<[u8]>>(
        bytes: &mut B,
    ) -> &mut BStr {
        BStr::from_bytes_mut(bytes.as_mut())
    }

    #[inline]
    pub(crate) fn from_bytes(slice: &[u8]) -> &BStr {
        unsafe { mem::transmute(slice) }
    }

    #[inline]
    pub(crate) fn from_bytes_mut(slice: &mut [u8]) -> &mut BStr {
        unsafe { mem::transmute(slice) }
    }

    #[inline]
    pub(crate) fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }
}

/// Construct a literal `BStr` usable in `static` or `const` items.
///
/// # Examples
///
/// ## Basic usage
///
/// Note that a byte string literal must be used, e.g. `b"foobar"` and not
/// `"foobar"`.
///
/// ```
/// # use bstr::{B, BStr};
/// const EXAMPLE: &BStr = bstr::literal!(b"foobar");
/// assert_eq!(EXAMPLE, B("foobar"));
/// ```
///
/// ## Use in combination with `include_bytes!`
///
/// ```
/// # const _: &str = stringify! {
/// const FILE_BYTES: &BStr = bstr::literal!(include_bytes!("./file.dat"));
/// # };
/// ```
///
/// ## Populating a field in a static struct
///
/// ```rust
/// # #[cfg(feature = "std")]
/// # fn main() {
/// # use std::borrow::Cow;
/// # use bstr::{B, BStr};
///
/// struct Archive {
///     name: Cow<'static, str>,
///     raw: Cow<'static, BStr>,
///     // etc...
/// }
///
/// static BUNDLED: Archive = Archive {
///     name: Cow::Borrowed("bundled"),
///     raw: Cow::Borrowed(bstr::literal!(b"important data...")),
///     // etc...
/// };
///
/// assert_eq!(&*BUNDLED.raw, B("important data..."));
/// # }
/// # #[cfg(not(feature = "std"))]
/// # fn main() {}
/// ```
#[macro_export]
macro_rules! literal {
    // Take an `expr` (and not a `literal`) as an argument so that
    // `bstr::literal!(include_bytes!(...))` works.
    ($bytes: expr) => {{
        // Avoid running the argument inside an `unsafe` block. Use underscores
        // to silence a dead code warning if the constant declared with this
        // literal ends up unused.
        const _BYTES: &'static [u8] = $bytes;
        const _BSTR: &'static $crate::BStr = unsafe {
            $crate::__private::ConstTransmuter { bytes: _BYTES }.bstr
        };
        _BSTR
    }};
}
