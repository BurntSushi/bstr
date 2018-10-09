use core::ops;

use bstr::BStr;

/// Ensure that callers cannot implement `SliceIndex` by making an
/// umplementable trait its super trait.
pub trait Sealed {}
impl Sealed for usize {}
impl Sealed for ops::Range<usize> {}
impl Sealed for ops::RangeTo<usize> {}
impl Sealed for ops::RangeFrom<usize> {}
impl Sealed for ops::RangeFull {}
impl Sealed for ops::RangeInclusive<usize> {}
impl Sealed for ops::RangeToInclusive<usize> {}

/// A trait that parameterizes the different types of indexing a byte string.
///
/// In general, this trait makes it possible to define generic routines like
/// `get` that can accept either single positions or ranges, and return single
/// bytes or slices, respectively.
///
/// This trait is sealed such that callers cannot implement it. In general,
/// callers should not need to interact with this trait directly unless you're
/// defining generic functions that index or slice a byte string.
pub trait SliceIndex: Sealed {
    /// The output type returned by methods. For indexing by position, this
    /// is always a single byte (`u8`). For ranges, this is always a slice
    /// (`BStr`).
    type Output: ?Sized;

    /// Returns a shared reference to the output at this location, if in
    /// bounds.
    fn get(self, slice: &BStr) -> Option<&Self::Output>;

    /// Returns a mutable reference to the output at this location, if in
    /// bounds.
    fn get_mut(self, slice: &mut BStr) -> Option<&mut Self::Output>;

    /// Returns a shared reference to the output at this location, without
    /// performing any bounds checking.
    unsafe fn get_unchecked(self, slice: &BStr) -> &Self::Output;

    /// Returns a mutable reference to the output at this location, without
    /// performing any bounds checking.
    unsafe fn get_unchecked_mut(self, slice: &mut BStr) -> &mut Self::Output;

    /// Returns a shared reference to the output at this location, panicking
    /// if out of bounds.
    fn index(self, slice: &BStr) -> &Self::Output;

    /// Returns a mutable reference to the output at this location, panicking
    /// if out of bounds.
    fn index_mut(self, slice: &mut BStr) -> &mut Self::Output;
}

impl SliceIndex for usize {
    type Output = u8;

    #[inline]
    fn get(self, slice: &BStr) -> Option<&u8> {
        slice.as_bytes().get(self)
    }

    #[inline]
    fn get_mut(self, slice: &mut BStr) -> Option<&mut u8> {
        slice.as_bytes_mut().get_mut(self)
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: &BStr) -> &u8 {
        slice.as_bytes().get_unchecked(self)
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: &mut BStr) -> &mut u8 {
        slice.as_bytes_mut().get_unchecked_mut(self)
    }

    #[inline]
    fn index(self, slice: &BStr) -> &u8 {
        &slice.as_bytes()[self]
    }

    #[inline]
    fn index_mut(self, slice: &mut BStr) -> &mut u8 {
        &mut slice.as_bytes_mut()[self]
    }
}

impl SliceIndex for ops::Range<usize> {
    type Output = BStr;

    #[inline]
    fn get(self, slice: &BStr) -> Option<&BStr> {
        slice.as_bytes().get(self).map(BStr::new)
    }

    #[inline]
    fn get_mut(self, slice: &mut BStr) -> Option<&mut BStr> {
        slice.as_bytes_mut().get_mut(self).map(BStr::new_mut)
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: &BStr) -> &BStr {
        BStr::new(slice.as_bytes().get_unchecked(self))
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: &mut BStr) -> &mut BStr {
        BStr::new_mut(slice.as_bytes_mut().get_unchecked_mut(self))
    }

    #[inline]
    fn index(self, slice: &BStr) -> &BStr {
        &slice[self]
    }

    #[inline]
    fn index_mut(self, slice: &mut BStr) -> &mut BStr {
        &mut slice[self]
    }
}

impl SliceIndex for ops::RangeTo<usize> {
    type Output = BStr;

    #[inline]
    fn get(self, slice: &BStr) -> Option<&BStr> {
        slice.as_bytes().get(self).map(BStr::new)
    }

    #[inline]
    fn get_mut(self, slice: &mut BStr) -> Option<&mut BStr> {
        slice.as_bytes_mut().get_mut(self).map(BStr::new_mut)
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: &BStr) -> &BStr {
        BStr::new(slice.as_bytes().get_unchecked(self))
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: &mut BStr) -> &mut BStr {
        BStr::new_mut(slice.as_bytes_mut().get_unchecked_mut(self))
    }

    #[inline]
    fn index(self, slice: &BStr) -> &BStr {
        &slice[self]
    }

    #[inline]
    fn index_mut(self, slice: &mut BStr) -> &mut BStr {
        &mut slice[self]
    }
}

impl SliceIndex for ops::RangeFrom<usize> {
    type Output = BStr;

    #[inline]
    fn get(self, slice: &BStr) -> Option<&BStr> {
        slice.as_bytes().get(self).map(BStr::new)
    }

    #[inline]
    fn get_mut(self, slice: &mut BStr) -> Option<&mut BStr> {
        slice.as_bytes_mut().get_mut(self).map(BStr::new_mut)
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: &BStr) -> &BStr {
        BStr::new(slice.as_bytes().get_unchecked(self))
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: &mut BStr) -> &mut BStr {
        BStr::new_mut(slice.as_bytes_mut().get_unchecked_mut(self))
    }

    #[inline]
    fn index(self, slice: &BStr) -> &BStr {
        &slice[self]
    }

    #[inline]
    fn index_mut(self, slice: &mut BStr) -> &mut BStr {
        &mut slice[self]
    }
}

impl SliceIndex for ops::RangeFull {
    type Output = BStr;

    #[inline]
    fn get(self, slice: &BStr) -> Option<&BStr> {
        slice.as_bytes().get(self).map(BStr::new)
    }

    #[inline]
    fn get_mut(self, slice: &mut BStr) -> Option<&mut BStr> {
        slice.as_bytes_mut().get_mut(self).map(BStr::new_mut)
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: &BStr) -> &BStr {
        BStr::new(slice.as_bytes().get_unchecked(self))
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: &mut BStr) -> &mut BStr {
        BStr::new_mut(slice.as_bytes_mut().get_unchecked_mut(self))
    }

    #[inline]
    fn index(self, slice: &BStr) -> &BStr {
        &slice[self]
    }

    #[inline]
    fn index_mut(self, slice: &mut BStr) -> &mut BStr {
        &mut slice[self]
    }
}

impl SliceIndex for ops::RangeInclusive<usize> {
    type Output = BStr;

    #[inline]
    fn get(self, slice: &BStr) -> Option<&BStr> {
        slice.as_bytes().get(self).map(BStr::new)
    }

    #[inline]
    fn get_mut(self, slice: &mut BStr) -> Option<&mut BStr> {
        slice.as_bytes_mut().get_mut(self).map(BStr::new_mut)
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: &BStr) -> &BStr {
        BStr::new(slice.as_bytes().get_unchecked(self))
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: &mut BStr) -> &mut BStr {
        BStr::new_mut(slice.as_bytes_mut().get_unchecked_mut(self))
    }

    #[inline]
    fn index(self, slice: &BStr) -> &BStr {
        &slice[self]
    }

    #[inline]
    fn index_mut(self, slice: &mut BStr) -> &mut BStr {
        &mut slice[self]
    }
}

impl SliceIndex for ops::RangeToInclusive<usize> {
    type Output = BStr;

    #[inline]
    fn get(self, slice: &BStr) -> Option<&BStr> {
        slice.as_bytes().get(self).map(BStr::new)
    }

    #[inline]
    fn get_mut(self, slice: &mut BStr) -> Option<&mut BStr> {
        slice.as_bytes_mut().get_mut(self).map(BStr::new_mut)
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: &BStr) -> &BStr {
        BStr::new(slice.as_bytes().get_unchecked(self))
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: &mut BStr) -> &mut BStr {
        BStr::new_mut(slice.as_bytes_mut().get_unchecked_mut(self))
    }

    #[inline]
    fn index(self, slice: &BStr) -> &BStr {
        &slice[self]
    }

    #[inline]
    fn index_mut(self, slice: &mut BStr) -> &mut BStr {
        &mut slice[self]
    }
}
