/** A trait which provides `from_bytes_radix()` for integer types.

This acts like `from_str_radix`, including panicking if `radix` is not in [2, 32].
However, there are a few minor differences to `from_str_radix`:
`src` is a `&BStr` and `radix` is the output type rather than always `u32`.
The result type is slightly different too.
```
use bstr::{BStr, FromBytesRadix, IntErrorKind};

for radix in 2..=36 {
    let e = BStr::new(b"");
    let empty = u8::from_bytes_radix(&e, 10);
    assert_eq!(empty.unwrap_err().kind(), &IntErrorKind::Empty);

    let a = BStr::new(b"11");
    let eleven = u8::from_bytes_radix(&a, radix);
    assert_eq!(eleven, Ok(radix + 1));

    let b = BStr::new("111111111");
    let pos_overflow = u8::from_bytes_radix(&b, radix);
    assert_eq!(pos_overflow.unwrap_err().kind(), &IntErrorKind::PosOverflow);

    let c = BStr::new("-111");
    let negatory = u8::from_bytes_radix(&c, radix);
    assert_eq!(negatory.unwrap_err().kind(), &IntErrorKind::InvalidDigit);

    let radix = radix as i32;
    let totally_fine = i32::from_bytes_radix(&c, radix);
    assert_eq!(totally_fine, Ok(-(radix*radix + radix + 1)));
}
```

The `NonZero` versions of integers are not currently supported for parsing.
Instead, please parse the equivalent possibly-zero integer, then convert:
```
use core::num::NonZeroU8;
use bstr::{BStr, FromBytesRadix};

let a = BStr::new(b"11");
let eleven = u8::from_bytes_radix(&a, 10).ok().and_then(NonZeroU8::new);
assert_eq!(eleven, NonZeroU8::new(11));

let zero = BStr::new(b"0");
let nada = u8::from_bytes_radix(&zero, 10).ok().and_then(NonZeroU8::new);
assert_eq!(nada, None);
```



*/
pub trait FromBytesRadix<T>
where
    T: PartialOrd
        + Copy
        + core::ops::Add<Output = T>
        + core::ops::Sub<Output = T>
        + core::ops::Mul<Output = T>,
{
    /// Whatever integer type is being parsed.
    type Integer;

    fn from_bytes_radix(
        src: &dyn AsRef<[u8]>,
        radix: Self::Integer,
    ) -> Result<Self::Integer, ParseIntError>;
}

// ParseIntError and impl is almost entirely copy-pasted from the standard library

/// Represents an error in parsing.
///
/// See [`IntErrorKind`] for a list of possible causes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseIntError {
    pub(super) kind: IntErrorKind,
}

impl ParseIntError {
    pub fn kind(&self) -> &IntErrorKind {
        &self.kind
    }
    #[doc(hidden)]
    pub fn __description(&self) -> &str {
        match self.kind {
            IntErrorKind::Empty => "cannot parse integer from empty string",
            IntErrorKind::InvalidDigit => "invalid digit found in string",
            IntErrorKind::PosOverflow => {
                "number too large to fit in target type"
            }
            IntErrorKind::NegOverflow => {
                "number too small to fit in target type"
            }
            IntErrorKind::Zero => "number would be zero for non-zero type",
        }
    }
}

impl std::fmt::Display for ParseIntError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.__description().fmt(f)
    }
}

/// Enum to store the various types of errors that can cause parsing an integer to fail.
///
/// Polyfill for post-1.55 [`core::num::IntErrorKind`]; that can just be re-used post-MSRV bump.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum IntErrorKind {
    /// Value being parsed is empty.
    ///
    /// This variant will be constructed when parsing an empty string.
    Empty,
    /// Contains an invalid digit in its context.
    ///
    /// Among other causes, this variant will be constructed when parsing a string that
    /// contains a non-ASCII char.
    ///
    /// This variant is also constructed when a `+` or `-` is misplaced within a string
    /// either on its own or in the middle of a number.
    InvalidDigit,
    /// Integer is too large to store in target integer type.
    PosOverflow,
    /// Integer is too small to store in target integer type.
    NegOverflow,
    /// Value was Zero
    ///
    /// This variant will be emitted when the parsing string has a value of zero, which
    /// would be illegal for non-zero types.
    Zero,
}

// TODO: once crate MSRV >= 1.55, just re-export this.
// pub use core::num::IntErrorKind;

macro_rules! make_from_bytes_radix {
    ($t:ident) => {
        impl FromBytesRadix<$t> for $t {
            type Integer = $t;

            fn from_bytes_radix(
                src: &dyn AsRef<[u8]>,
                radix: $t,
            ) -> Result<$t, crate::ParseIntError>
            {
                // This more-or-less follows the stdlib implementation.

                assert!((2..=36).contains(&radix), "from_str_radix_int: must lie in the range `[2, 36]` - found {}", radix);

                let src = src.as_ref();

                if let Some(s0) = src.get(0) {
                    // The stdlib implementation is that runs of `+` or `-` are invalid.
                    // So we need only consider the leading character.
                    let (start, is_neg) = if *s0 == b'-' {(1, true) } else if *s0 == b'+' {(1, false)} else {(0, false)};

                    // Leading negative on an unsigned type
                    if is_neg && $t::MIN == 0 {
                        return Err(crate::ParseIntError{kind: crate::IntErrorKind::InvalidDigit});
                    }

                    // Input string was a single plus or minus
                    if start == 1 && src.len() == 1 {
                        return Err(crate::ParseIntError{kind: crate::IntErrorKind::InvalidDigit});
                    }

                    // Items for manual determination of digit
                    let r = radix as u8;
                    let num_max = if r < 10 { r } else { 10 };
                    let abc_max = if r < 10 { 0 } else { r - 10 };

                    // The accumulator
                    let mut acc: $t = 0;

                    for i in start..src.len() {
                        let k = src[i];

                        let mul = acc.checked_mul(radix);

                        let s : u8 = if k >= 48 && k < (48 + num_max) {
                            // 48: `0` in ASCII
                            (k - 48)
                        } else if k >= 65 && k < 65 + abc_max {
                            // 65: `A` in ASCII
                            (k - 65)
                        } else if k > 97 && k < 97 + abc_max {
                            // 97: `a` in ASCII
                            (k - 97)
                        } else {
                            return Err(crate::ParseIntError{kind: crate::IntErrorKind::InvalidDigit});
                        };

                        if is_neg {
                            if let Some(x) = mul.and_then(|m| m.checked_sub(s as $t)){
                                acc = x;
                            } else {
                                return Err(crate::ParseIntError{kind: crate::IntErrorKind::NegOverflow});
                            }
                        } else {
                            if let Some(x) = mul.and_then(|m| m.checked_add(s as $t)) {
                                acc = x;
                            } else {
                                return Err(crate::ParseIntError{kind: crate::IntErrorKind::PosOverflow});
                            }
                        }
                    }

                    Ok(acc)

                } else {
                    return Err(crate::ParseIntError{kind: crate::IntErrorKind::Empty});
                }
            }
        }
    }
}

make_from_bytes_radix!(u8);
make_from_bytes_radix!(u16);
make_from_bytes_radix!(u32);
make_from_bytes_radix!(u64);
make_from_bytes_radix!(u128);
make_from_bytes_radix!(usize);

make_from_bytes_radix!(i8);
make_from_bytes_radix!(i16);
make_from_bytes_radix!(i32);
make_from_bytes_radix!(i64);
make_from_bytes_radix!(i128);
make_from_bytes_radix!(isize);

// NOTE: once MSRV exceeds 1.64 it should be possible to implement everything for the NonZero types too.

#[cfg(test)]
mod tests {
    /*!
     * Things tested:
     *
     * Zero
     * Normal case `b"11"` (should always parse as `Ok(radix + 1)`)
     * Too-long string ({number of bytes + 1} ones) (should be `PosOverflow`)
     * Leading negative (should be OK for signed types, `InvalidDigit` for unsigned)
     * Empty string (should be `Empty`)
     * Leading double negative (should always be `InvalidDigit`)
     * Leading positive (should always parse OK)
     * Leading double positive (should always be `InvalidDigit`)
     * Signed empty string (should be `InvalidDigit`)
     *
     * MIN and MAX round-trip (done in base 10 only, because `to_string` assumes that)
     *
     */

    use super::*;
    use crate::BStr;
    use crate::BString;
    use crate::IntErrorKind;

    #[test]
    fn test_parse_u8() {
        for radix in 2..=36 {
            let z = BStr::new(b"0");
            assert_eq!(u8::from_bytes_radix(&z, radix), Ok(0));

            let a = BStr::new(b"11");
            let eleven = u8::from_bytes_radix(&a, radix);
            assert_eq!(eleven, Ok(radix + 1));

            let b = BStr::new(b"111111111");
            let pos_overflow = u8::from_bytes_radix(&b, radix);
            assert_eq!(
                pos_overflow.unwrap_err().kind(),
                &IntErrorKind::PosOverflow
            );

            let c = BStr::new(b"-11");
            let negatory = u8::from_bytes_radix(&c, radix);
            assert_eq!(
                negatory.unwrap_err().kind(),
                &IntErrorKind::InvalidDigit
            );

            let d = BStr::new(b"--11");
            let two_wrongs = u8::from_bytes_radix(&d, radix);
            assert_eq!(
                two_wrongs.unwrap_err().kind(),
                &IntErrorKind::InvalidDigit
            );

            let e = BStr::new(b"");
            let empty = u8::from_bytes_radix(&e, radix);
            assert_eq!(empty.unwrap_err().kind(), &IntErrorKind::Empty);

            let f = BStr::new(b"+11");
            assert_eq!(u8::from_bytes_radix(&f, radix), Ok(radix + 1));

            let g = BStr::new(b"++11");
            assert_eq!(
                u8::from_bytes_radix(&g, radix).unwrap_err().kind(),
                &IntErrorKind::InvalidDigit
            );

            let i = BStr::new("+");
            assert_eq!(
                u8::from_bytes_radix(&i, radix).unwrap_err().kind(),
                &IntErrorKind::InvalidDigit
            );
        }
        // this only stringifies in base 10
        let min = BString::from(u8::MIN.to_string());
        assert_eq!(u8::from_bytes_radix(&min.as_bstr(), 10), Ok(u8::MIN));
        let max = BString::from(u8::MAX.to_string());
        assert_eq!(u8::from_bytes_radix(&max.as_bstr(), 10), Ok(u8::MAX));
    }

    #[test]
    fn test_parse_i8() {
        for radix in 2..=36 {
            let z = BStr::new(b"0");
            assert_eq!(i8::from_bytes_radix(&z, radix), Ok(0));

            let a = BStr::new(b"11");
            let eleven = i8::from_bytes_radix(&a, radix);
            assert_eq!(eleven, Ok(radix + 1));

            let b = BStr::new(b"111111111");
            let pos_overflow = i8::from_bytes_radix(&b, radix);
            assert_eq!(
                pos_overflow.unwrap_err().kind(),
                &IntErrorKind::PosOverflow
            );

            let c = BStr::new(b"-11");
            let totally_fine = i8::from_bytes_radix(&c, radix);
            assert_eq!(totally_fine, Ok(-(radix + 1)));

            let d = BStr::new(b"--11");
            let two_wrongs = i8::from_bytes_radix(&d, radix);
            assert_eq!(
                two_wrongs.unwrap_err().kind(),
                &IntErrorKind::InvalidDigit
            );

            let e = BStr::new(b"");
            let empty = i8::from_bytes_radix(&e, radix);
            assert_eq!(empty.unwrap_err().kind(), &IntErrorKind::Empty);

            let f = BStr::new(b"+11");
            assert_eq!(i8::from_bytes_radix(&f, radix), Ok(radix + 1));

            let g = BStr::new(b"++11");
            assert_eq!(
                i8::from_bytes_radix(&g, radix).unwrap_err().kind(),
                &IntErrorKind::InvalidDigit
            );

            let h = BStr::new(b"-111111111");
            assert_eq!(
                i8::from_bytes_radix(&h, radix).unwrap_err().kind(),
                &IntErrorKind::NegOverflow
            );
        }
        // this only stringifies in base 10
        let min = BString::from(i8::MIN.to_string());
        assert_eq!(i8::from_bytes_radix(&min.as_bstr(), 10).unwrap(), i8::MIN);
        let max = BString::from(i8::MAX.to_string());
        assert_eq!(i8::from_bytes_radix(&max.as_bstr(), 10).unwrap(), i8::MAX);
    }
}
