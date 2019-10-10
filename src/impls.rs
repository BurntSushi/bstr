macro_rules! impl_partial_eq {
    ($lhs:ty, $rhs:ty) => {
        impl<'a, 'b> PartialEq<$rhs> for $lhs {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool {
                let other: &[u8] = other.as_ref();
                PartialEq::eq(self.as_bytes(), other)
            }
        }

        impl<'a, 'b> PartialEq<$lhs> for $rhs {
            #[inline]
            fn eq(&self, other: &$lhs) -> bool {
                let this: &[u8] = self.as_ref();
                PartialEq::eq(this, other.as_bytes())
            }
        }
    };
}

#[cfg(feature = "std")]
macro_rules! impl_partial_eq_cow {
    ($lhs:ty, $rhs:ty) => {
        impl<'a, 'b> PartialEq<$rhs> for $lhs {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool {
                let other: &[u8] = (&**other).as_ref();
                PartialEq::eq(self.as_bytes(), other)
            }
        }

        impl<'a, 'b> PartialEq<$lhs> for $rhs {
            #[inline]
            fn eq(&self, other: &$lhs) -> bool {
                let this: &[u8] = (&**other).as_ref();
                PartialEq::eq(this, other.as_bytes())
            }
        }
    };
}

macro_rules! impl_partial_ord {
    ($lhs:ty, $rhs:ty) => {
        impl<'a, 'b> PartialOrd<$rhs> for $lhs {
            #[inline]
            fn partial_cmp(&self, other: &$rhs) -> Option<Ordering> {
                let other: &[u8] = other.as_ref();
                PartialOrd::partial_cmp(self.as_bytes(), other)
            }
        }

        impl<'a, 'b> PartialOrd<$lhs> for $rhs {
            #[inline]
            fn partial_cmp(&self, other: &$lhs) -> Option<Ordering> {
                let this: &[u8] = self.as_ref();
                PartialOrd::partial_cmp(this, other.as_bytes())
            }
        }
    };
}

#[cfg(feature = "std")]
mod bstring {
    use std::borrow::{Borrow, Cow, ToOwned};
    use std::cmp::Ordering;
    use std::fmt;
    use std::iter::FromIterator;
    use std::ops;

    use bstr::BStr;
    use bstring::BString;
    use ext_vec::ByteVec;

    impl fmt::Display for BString {
        #[inline]
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            fmt::Display::fmt(self.as_bstr(), f)
        }
    }

    impl fmt::Debug for BString {
        #[inline]
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            fmt::Debug::fmt(self.as_bstr(), f)
        }
    }

    impl ops::Deref for BString {
        type Target = Vec<u8>;

        #[inline]
        fn deref(&self) -> &Vec<u8> {
            &self.bytes
        }
    }

    impl ops::DerefMut for BString {
        #[inline]
        fn deref_mut(&mut self) -> &mut Vec<u8> {
            &mut self.bytes
        }
    }

    impl AsRef<[u8]> for BString {
        #[inline]
        fn as_ref(&self) -> &[u8] {
            &self.bytes
        }
    }

    impl AsRef<BStr> for BString {
        #[inline]
        fn as_ref(&self) -> &BStr {
            self.as_bstr()
        }
    }

    impl AsMut<[u8]> for BString {
        #[inline]
        fn as_mut(&mut self) -> &mut [u8] {
            &mut self.bytes
        }
    }

    impl AsMut<BStr> for BString {
        #[inline]
        fn as_mut(&mut self) -> &mut BStr {
            self.as_mut_bstr()
        }
    }

    impl Borrow<BStr> for BString {
        #[inline]
        fn borrow(&self) -> &BStr {
            self.as_bstr()
        }
    }

    impl ToOwned for BStr {
        type Owned = BString;

        #[inline]
        fn to_owned(&self) -> BString {
            BString::from(self)
        }
    }

    impl Default for BString {
        fn default() -> BString {
            BString::from(vec![])
        }
    }

    impl<'a> From<&'a [u8]> for BString {
        #[inline]
        fn from(s: &'a [u8]) -> BString {
            BString::from(s.to_vec())
        }
    }

    impl From<Vec<u8>> for BString {
        #[inline]
        fn from(s: Vec<u8>) -> BString {
            BString { bytes: s }
        }
    }

    impl From<BString> for Vec<u8> {
        #[inline]
        fn from(s: BString) -> Vec<u8> {
            s.bytes
        }
    }

    impl<'a> From<&'a str> for BString {
        #[inline]
        fn from(s: &'a str) -> BString {
            BString::from(s.as_bytes().to_vec())
        }
    }

    impl From<String> for BString {
        #[inline]
        fn from(s: String) -> BString {
            BString::from(s.into_bytes())
        }
    }

    impl<'a> From<&'a BStr> for BString {
        #[inline]
        fn from(s: &'a BStr) -> BString {
            BString::from(s.bytes.to_vec())
        }
    }

    impl<'a> From<BString> for Cow<'a, BStr> {
        #[inline]
        fn from(s: BString) -> Cow<'a, BStr> {
            Cow::Owned(s)
        }
    }

    impl FromIterator<char> for BString {
        #[inline]
        fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> BString {
            BString::from(iter.into_iter().collect::<String>())
        }
    }

    impl FromIterator<u8> for BString {
        #[inline]
        fn from_iter<T: IntoIterator<Item = u8>>(iter: T) -> BString {
            BString::from(iter.into_iter().collect::<Vec<u8>>())
        }
    }

    impl<'a> FromIterator<&'a str> for BString {
        #[inline]
        fn from_iter<T: IntoIterator<Item = &'a str>>(iter: T) -> BString {
            let mut buf = vec![];
            for b in iter {
                buf.push_str(b);
            }
            BString::from(buf)
        }
    }

    impl<'a> FromIterator<&'a [u8]> for BString {
        #[inline]
        fn from_iter<T: IntoIterator<Item = &'a [u8]>>(iter: T) -> BString {
            let mut buf = vec![];
            for b in iter {
                buf.push_str(b);
            }
            BString::from(buf)
        }
    }

    impl<'a> FromIterator<&'a BStr> for BString {
        #[inline]
        fn from_iter<T: IntoIterator<Item = &'a BStr>>(iter: T) -> BString {
            let mut buf = vec![];
            for b in iter {
                buf.push_str(b);
            }
            BString::from(buf)
        }
    }

    impl FromIterator<BString> for BString {
        #[inline]
        fn from_iter<T: IntoIterator<Item = BString>>(iter: T) -> BString {
            let mut buf = vec![];
            for b in iter {
                buf.push_str(b);
            }
            BString::from(buf)
        }
    }

    impl Eq for BString {}

    impl PartialEq for BString {
        #[inline]
        fn eq(&self, other: &BString) -> bool {
            &self[..] == &other[..]
        }
    }

    impl_partial_eq!(BString, Vec<u8>);
    impl_partial_eq!(BString, [u8]);
    impl_partial_eq!(BString, &'a [u8]);
    impl_partial_eq!(BString, String);
    impl_partial_eq!(BString, str);
    impl_partial_eq!(BString, &'a str);
    impl_partial_eq!(BString, BStr);
    impl_partial_eq!(BString, &'a BStr);

    impl PartialOrd for BString {
        #[inline]
        fn partial_cmp(&self, other: &BString) -> Option<Ordering> {
            PartialOrd::partial_cmp(&self.bytes, &other.bytes)
        }
    }

    impl Ord for BString {
        #[inline]
        fn cmp(&self, other: &BString) -> Ordering {
            self.partial_cmp(other).unwrap()
        }
    }

    impl_partial_ord!(BString, Vec<u8>);
    impl_partial_ord!(BString, [u8]);
    impl_partial_ord!(BString, &'a [u8]);
    impl_partial_ord!(BString, String);
    impl_partial_ord!(BString, str);
    impl_partial_ord!(BString, &'a str);
    impl_partial_ord!(BString, BStr);
    impl_partial_ord!(BString, &'a BStr);
}

mod bstr {
    #[cfg(feature = "std")]
    use std::borrow::Cow;

    use core::cmp::Ordering;
    use core::fmt;
    use core::ops;

    use bstr::BStr;
    use ext_slice::ByteSlice;

    impl fmt::Display for BStr {
        #[inline]
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            for chunk in self.utf8_chunks() {
                f.write_str(chunk.valid())?;
                if !chunk.invalid().is_empty() {
                    f.write_str("\u{FFFD}")?;
                }
            }
            Ok(())
        }
    }

    impl fmt::Debug for BStr {
        #[inline]
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "\"")?;
            for (s, e, ch) in self.char_indices() {
                if ch == '\u{FFFD}' {
                    for &b in self[s..e].as_bytes() {
                        write!(f, r"\x{:X}", b)?;
                    }
                } else {
                    write!(f, "{}", ch.escape_debug())?;
                }
            }
            write!(f, "\"")?;
            Ok(())
        }
    }

    impl ops::Deref for BStr {
        type Target = [u8];

        #[inline]
        fn deref(&self) -> &[u8] {
            &self.bytes
        }
    }

    impl ops::DerefMut for BStr {
        #[inline]
        fn deref_mut(&mut self) -> &mut [u8] {
            &mut self.bytes
        }
    }

    impl ops::Index<usize> for BStr {
        type Output = u8;

        #[inline]
        fn index(&self, idx: usize) -> &u8 {
            &self.as_bytes()[idx]
        }
    }

    impl ops::Index<ops::RangeFull> for BStr {
        type Output = BStr;

        #[inline]
        fn index(&self, _: ops::RangeFull) -> &BStr {
            self
        }
    }

    impl ops::Index<ops::Range<usize>> for BStr {
        type Output = BStr;

        #[inline]
        fn index(&self, r: ops::Range<usize>) -> &BStr {
            BStr::new(&self.as_bytes()[r.start..r.end])
        }
    }

    impl ops::Index<ops::RangeInclusive<usize>> for BStr {
        type Output = BStr;

        #[inline]
        fn index(&self, r: ops::RangeInclusive<usize>) -> &BStr {
            BStr::new(&self.as_bytes()[*r.start()..=*r.end()])
        }
    }

    impl ops::Index<ops::RangeFrom<usize>> for BStr {
        type Output = BStr;

        #[inline]
        fn index(&self, r: ops::RangeFrom<usize>) -> &BStr {
            BStr::new(&self.as_bytes()[r.start..])
        }
    }

    impl ops::Index<ops::RangeTo<usize>> for BStr {
        type Output = BStr;

        #[inline]
        fn index(&self, r: ops::RangeTo<usize>) -> &BStr {
            BStr::new(&self.as_bytes()[..r.end])
        }
    }

    impl ops::Index<ops::RangeToInclusive<usize>> for BStr {
        type Output = BStr;

        #[inline]
        fn index(&self, r: ops::RangeToInclusive<usize>) -> &BStr {
            BStr::new(&self.as_bytes()[..=r.end])
        }
    }

    impl ops::IndexMut<usize> for BStr {
        #[inline]
        fn index_mut(&mut self, idx: usize) -> &mut u8 {
            &mut self.bytes[idx]
        }
    }

    impl ops::IndexMut<ops::RangeFull> for BStr {
        #[inline]
        fn index_mut(&mut self, _: ops::RangeFull) -> &mut BStr {
            self
        }
    }

    impl ops::IndexMut<ops::Range<usize>> for BStr {
        #[inline]
        fn index_mut(&mut self, r: ops::Range<usize>) -> &mut BStr {
            BStr::from_bytes_mut(&mut self.bytes[r.start..r.end])
        }
    }

    impl ops::IndexMut<ops::RangeInclusive<usize>> for BStr {
        #[inline]
        fn index_mut(&mut self, r: ops::RangeInclusive<usize>) -> &mut BStr {
            BStr::from_bytes_mut(&mut self.bytes[*r.start()..=*r.end()])
        }
    }

    impl ops::IndexMut<ops::RangeFrom<usize>> for BStr {
        #[inline]
        fn index_mut(&mut self, r: ops::RangeFrom<usize>) -> &mut BStr {
            BStr::from_bytes_mut(&mut self.bytes[r.start..])
        }
    }

    impl ops::IndexMut<ops::RangeTo<usize>> for BStr {
        #[inline]
        fn index_mut(&mut self, r: ops::RangeTo<usize>) -> &mut BStr {
            BStr::from_bytes_mut(&mut self.bytes[..r.end])
        }
    }

    impl ops::IndexMut<ops::RangeToInclusive<usize>> for BStr {
        #[inline]
        fn index_mut(&mut self, r: ops::RangeToInclusive<usize>) -> &mut BStr {
            BStr::from_bytes_mut(&mut self.bytes[..=r.end])
        }
    }

    impl AsRef<[u8]> for BStr {
        #[inline]
        fn as_ref(&self) -> &[u8] {
            self.as_bytes()
        }
    }

    impl AsRef<BStr> for [u8] {
        #[inline]
        fn as_ref(&self) -> &BStr {
            BStr::new(self)
        }
    }

    impl AsRef<BStr> for str {
        #[inline]
        fn as_ref(&self) -> &BStr {
            BStr::new(self)
        }
    }

    impl AsMut<[u8]> for BStr {
        #[inline]
        fn as_mut(&mut self) -> &mut [u8] {
            &mut self.bytes
        }
    }

    impl AsMut<BStr> for [u8] {
        #[inline]
        fn as_mut(&mut self) -> &mut BStr {
            BStr::new_mut(self)
        }
    }

    impl<'a> Default for &'a BStr {
        fn default() -> &'a BStr {
            BStr::from_bytes(b"")
        }
    }

    impl<'a> Default for &'a mut BStr {
        fn default() -> &'a mut BStr {
            BStr::from_bytes_mut(&mut [])
        }
    }

    impl<'a> From<&'a [u8]> for &'a BStr {
        #[inline]
        fn from(s: &'a [u8]) -> &'a BStr {
            BStr::from_bytes(s)
        }
    }

    impl<'a> From<&'a str> for &'a BStr {
        #[inline]
        fn from(s: &'a str) -> &'a BStr {
            BStr::from_bytes(s.as_bytes())
        }
    }

    #[cfg(feature = "std")]
    impl<'a> From<&'a BStr> for Cow<'a, BStr> {
        #[inline]
        fn from(s: &'a BStr) -> Cow<'a, BStr> {
            Cow::Borrowed(s)
        }
    }

    impl Eq for BStr {}

    impl PartialEq<BStr> for BStr {
        #[inline]
        fn eq(&self, other: &BStr) -> bool {
            self.as_bytes() == other.as_bytes()
        }
    }

    impl_partial_eq!(BStr, [u8]);
    impl_partial_eq!(BStr, &'a [u8]);
    impl_partial_eq!(BStr, str);
    impl_partial_eq!(BStr, &'a str);

    #[cfg(feature = "std")]
    impl_partial_eq!(BStr, Vec<u8>);
    #[cfg(feature = "std")]
    impl_partial_eq!(&'a BStr, Vec<u8>);
    #[cfg(feature = "std")]
    impl_partial_eq!(BStr, String);
    #[cfg(feature = "std")]
    impl_partial_eq!(&'a BStr, String);
    #[cfg(feature = "std")]
    impl_partial_eq_cow!(&'a BStr, Cow<'a, BStr>);
    #[cfg(feature = "std")]
    impl_partial_eq_cow!(&'a BStr, Cow<'a, str>);
    #[cfg(feature = "std")]
    impl_partial_eq_cow!(&'a BStr, Cow<'a, [u8]>);

    impl PartialOrd for BStr {
        #[inline]
        fn partial_cmp(&self, other: &BStr) -> Option<Ordering> {
            PartialOrd::partial_cmp(self.as_bytes(), other.as_bytes())
        }
    }

    impl Ord for BStr {
        #[inline]
        fn cmp(&self, other: &BStr) -> Ordering {
            self.partial_cmp(other).unwrap()
        }
    }

    impl_partial_ord!(BStr, [u8]);
    impl_partial_ord!(BStr, &'a [u8]);
    impl_partial_ord!(BStr, str);
    impl_partial_ord!(BStr, &'a str);

    #[cfg(feature = "std")]
    impl_partial_ord!(BStr, Vec<u8>);
    #[cfg(feature = "std")]
    impl_partial_ord!(&'a BStr, Vec<u8>);
    #[cfg(feature = "std")]
    impl_partial_ord!(BStr, String);
    #[cfg(feature = "std")]
    impl_partial_ord!(&'a BStr, String);
}

#[cfg(feature = "serde1-nostd")]
mod bstr_serde {
    use core::fmt;

    use serde::{
        de::Error, de::Visitor, Deserialize, Deserializer, Serialize,
        Serializer,
    };

    use bstr::BStr;

    impl Serialize for BStr {
        #[inline]
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            serializer.serialize_bytes(self.as_bytes())
        }
    }

    impl<'a, 'de: 'a> Deserialize<'de> for &'a BStr {
        #[inline]
        fn deserialize<D>(deserializer: D) -> Result<&'a BStr, D::Error>
        where
            D: Deserializer<'de>,
        {
            struct BStrVisitor;

            impl<'de> Visitor<'de> for BStrVisitor {
                type Value = &'de BStr;

                fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    f.write_str("a borrowed byte string")
                }

                #[inline]
                fn visit_borrowed_bytes<E: Error>(
                    self,
                    value: &'de [u8],
                ) -> Result<&'de BStr, E> {
                    Ok(BStr::new(value))
                }

                #[inline]
                fn visit_borrowed_str<E: Error>(
                    self,
                    value: &'de str,
                ) -> Result<&'de BStr, E> {
                    Ok(BStr::new(value))
                }
            }

            deserializer.deserialize_bytes(BStrVisitor)
        }
    }
}

#[cfg(feature = "serde1")]
mod bstring_serde {
    use std::cmp;
    use std::fmt;

    use serde::{
        de::Error, de::SeqAccess, de::Visitor, Deserialize, Deserializer,
        Serialize, Serializer,
    };

    use bstring::BString;

    impl Serialize for BString {
        #[inline]
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            serializer.serialize_bytes(self.as_bytes())
        }
    }

    impl<'de> Deserialize<'de> for BString {
        #[inline]
        fn deserialize<D>(deserializer: D) -> Result<BString, D::Error>
        where
            D: Deserializer<'de>,
        {
            struct BStringVisitor;

            impl<'de> Visitor<'de> for BStringVisitor {
                type Value = BString;

                fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    f.write_str("a byte string")
                }

                #[inline]
                fn visit_seq<V: SeqAccess<'de>>(
                    self,
                    mut visitor: V,
                ) -> Result<BString, V::Error> {
                    let len = cmp::min(visitor.size_hint().unwrap_or(0), 256);
                    let mut bytes = Vec::with_capacity(len);
                    while let Some(v) = visitor.next_element()? {
                        bytes.push(v);
                    }
                    Ok(BString::from(bytes))
                }

                #[inline]
                fn visit_bytes<E: Error>(
                    self,
                    value: &[u8],
                ) -> Result<BString, E> {
                    Ok(BString::from(value))
                }

                #[inline]
                fn visit_byte_buf<E: Error>(
                    self,
                    value: Vec<u8>,
                ) -> Result<BString, E> {
                    Ok(BString::from(value))
                }

                #[inline]
                fn visit_str<E: Error>(
                    self,
                    value: &str,
                ) -> Result<BString, E> {
                    Ok(BString::from(value))
                }

                #[inline]
                fn visit_string<E: Error>(
                    self,
                    value: String,
                ) -> Result<BString, E> {
                    Ok(BString::from(value))
                }
            }

            deserializer.deserialize_byte_buf(BStringVisitor)
        }
    }
}

#[cfg(test)]
mod bstring_arbitrary {
    use bstring::BString;

    use quickcheck::{Arbitrary, Gen};

    impl Arbitrary for BString {
        fn arbitrary<G: Gen>(g: &mut G) -> BString {
            BString::from(Vec::<u8>::arbitrary(g))
        }

        fn shrink(&self) -> Box<dyn Iterator<Item = BString>> {
            Box::new(self.bytes.shrink().map(BString::from))
        }
    }
}
