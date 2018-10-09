#[cfg(feature = "std")]
use std::borrow::Cow;
use core::ops;

use bstr::BStr;
#[cfg(feature = "std")]
use bstring::BString;

/// A specialized copy-on-write BStr.
///
/// The purpose of this type is to permit usage of a "borrowed or owned byte
/// string" in a way that keeps std/no-std compatibility. That is, in no-std
/// mode, this type devolves into a simple &BStr with no owned variant
/// availble.
#[derive(Clone, Debug)]
pub struct CowBStr<'a>(Imp<'a>);

#[cfg(feature = "std")]
#[derive(Clone, Debug)]
struct Imp<'a>(Cow<'a, BStr>);

#[cfg(not(feature = "std"))]
#[derive(Clone, Debug)]
struct Imp<'a>(&'a BStr);

impl<'a> ops::Deref for CowBStr<'a> {
    type Target = BStr;

    fn deref(&self) -> &BStr {
        self.as_bstr()
    }
}

impl<'a> CowBStr<'a> {
    /// Create a new borrowed CowBStr.
    pub fn new<B: ?Sized + AsRef<[u8]>>(bytes: &'a B) -> CowBStr<'a> {
        CowBStr(Imp::new(BStr::new(bytes)))
    }

    /// Create a new owned CowBStr.
    #[cfg(feature = "std")]
    pub fn new_owned(bytes: BString) -> CowBStr<'static> {
        CowBStr(Imp(Cow::Owned(bytes)))
    }

    /// Return a borrowed byte string, regardless of whether this is an owned
    /// or borrowed byte string internally.
    pub fn as_bstr(&self) -> &BStr {
        self.0.as_bstr()
    }

    /// Return an owned version of this copy-on-write byte string.
    ///
    /// If this is already an owned byte string internally, then this is a
    /// no-op. Otherwise, the internal byte string is copied.
    #[cfg(feature = "std")]
    pub fn into_owned(self) -> CowBStr<'static> {
        match (self.0).0 {
            Cow::Borrowed(b) => CowBStr::new_owned(b.to_bstring()),
            Cow::Owned(b) => CowBStr::new_owned(b),
        }
    }
}

impl<'a> Imp<'a> {
    #[cfg(feature = "std")]
    pub fn new(bytes: &'a BStr) -> Imp<'a> {
        Imp(Cow::Borrowed(bytes))
    }

    #[cfg(not(feature = "std"))]
    pub fn new(bytes: &'a BStr) -> Imp<'a> {
        Imp(bytes)
    }

    #[cfg(feature = "std")]
    pub fn as_bstr(&self) -> &BStr {
        // &*self.0
        match self.0 {
            Cow::Owned(ref x) => x,
            Cow::Borrowed(x) => x,
        }
    }

    #[cfg(not(feature = "std"))]
    pub fn as_bstr(&self) -> &BStr {
        self.0
    }
}
