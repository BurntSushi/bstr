/** A trait which provides `from_bytes_radix()` for integer types.

This acts like `from_str_radix`, including panicking if `radix` is not in
[2, 32] and supporting `[0-9A-Za-z]` as possible digits, depending on the
value of `radix`.
```
use bstr::{FromBytesRadix, IntErrorKind, B};

for radix in 2..=36 {

    let r = radix as u8;

    let e = B("");
    let empty = u8::from_bytes_radix(&e, 10);
    assert_eq!(empty.unwrap_err().kind(), &IntErrorKind::Empty);

    let a = B("11");
    let eleven = u8::from_bytes_radix(&a, radix);
    assert_eq!(eleven, Ok(r + 1));

    let b = B("111111111");
    let pos_overflow = u8::from_bytes_radix(&b, radix);
    assert_eq!(pos_overflow.unwrap_err().kind(), &IntErrorKind::PosOverflow);

    let c = B("-111");
    let negatory = u8::from_bytes_radix(&c, radix);
    assert_eq!(negatory.unwrap_err().kind(), &IntErrorKind::InvalidDigit);


    let r = radix as i32;

    let totally_fine = i32::from_bytes_radix(&c, radix);
    assert_eq!(totally_fine, Ok(-(r*r + r + 1)));
}
```

The `NonZero` versions of integers are not currently supported for parsing.
Instead, please parse the equivalent possibly-zero integer, then convert:
```
use core::num::NonZeroU8;
use bstr::{FromBytesRadix, B};

let a = B("11");
let eleven = u8::from_bytes_radix(&a, 10).ok().and_then(NonZeroU8::new);
assert_eq!(eleven, NonZeroU8::new(11));

let zero = B("0");
let nada = u8::from_bytes_radix(&zero, 10).ok().and_then(NonZeroU8::new);
assert_eq!(nada, None);
```

*/

mod private {
    pub trait Sealed {}
}

pub trait FromBytesRadix: Sized + private::Sealed {
    fn from_bytes_radix(
        src: &dyn AsRef<[u8]>,
        radix: u32,
    ) -> Result<Self, ParseIntError>
    where
        Self: Sized;
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
        impl private::Sealed for $t {}

        impl FromBytesRadix for $t {
            fn from_bytes_radix(
                src: &dyn AsRef<[u8]>,
                radix: u32,
            ) -> Result<$t, crate::ParseIntError>
            {
                //! Convert a `u8` slice in a given base (`radix`)
                //! to an integer.
                //!
                //! This acts like [`from_str_radix`](https://doc.rust-lang.org/std/primitive.i8.html#method.from_str_radix):
                //!
                //! * Digits are a subset of `[0-9A-Za-z]`, depending on `radix`
                //! * A `radix` outside [2, 32] will cause a __panic__
                //! * A single `+` may optionally precede the digits
                //! * For signed types a single `-` may optionally precede the digits
                //! * Any other characters (including whitespace and `_`) are invalid
                //!

                // Provide a nice formatted error message if we can.
                #[cfg(feature = "alloc")]
                assert!((2..=36).contains(&radix), "from_bytes_radix_int: must lie in the range `[2, 36]` - found {}", radix);

                #[cfg(not(feature = "alloc"))]
                assert!((2..=36).contains(&radix));

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

                        let mul = acc.checked_mul(radix as $t);

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
     * Leading positive (should always parse as `Ok(radix + 1)`)
     * Leading double positive (should always be `InvalidDigit`)
     * Standalone `+` or `-` (should be `InvalidDigit`)
     *
     * MIN and MAX round-trip (done in base 10 only, because `to_string` assumes that)
     * MIN-1 (if signed) and MAX+1 for negative and positive overflows (ditto base 10)
     *
     * Over-large radix (matching stdlib panic)
     *
     * Error on whitespace or underscore (matching stdlib)
     *
     */

    use super::*;
    use crate::{BString, IntErrorKind, B};

    #[test]
    fn parse_u8() {
        for radix in 2..=36 {
            let r = radix as u8;

            assert_eq!(u8::from_bytes_radix(&B("0"), radix), Ok(0));

            let eleven = u8::from_bytes_radix(&B("11"), radix);
            assert_eq!(eleven, Ok(r + 1));

            // Nine 1s in a row is larger than a u8 even in base 2
            let pos_overflow = u8::from_bytes_radix(&B("111111111"), radix);
            assert_eq!(
                pos_overflow.unwrap_err().kind(),
                &IntErrorKind::PosOverflow
            );

            let negatory = u8::from_bytes_radix(&B("-11"), radix);
            assert_eq!(
                negatory.unwrap_err().kind(),
                &IntErrorKind::InvalidDigit
            );

            let two_wrongs = u8::from_bytes_radix(&B("--11"), radix);
            assert_eq!(
                two_wrongs.unwrap_err().kind(),
                &IntErrorKind::InvalidDigit
            );

            let empty = u8::from_bytes_radix(&B(""), radix);
            assert_eq!(empty.unwrap_err().kind(), &IntErrorKind::Empty);

            let leading_plus = u8::from_bytes_radix(&B("+11"), radix);
            assert_eq!(leading_plus, Ok(r + 1));

            let ungood = u8::from_bytes_radix(&B("++11"), radix);
            assert_eq!(
                ungood.unwrap_err().kind(),
                &IntErrorKind::InvalidDigit
            );

            let plus_only = u8::from_bytes_radix(&B("+"), radix);
            assert_eq!(
                plus_only.unwrap_err().kind(),
                &IntErrorKind::InvalidDigit
            );

            assert_eq!(
                u8::from_bytes_radix(&B("-"), radix).unwrap_err().kind(),
                &IntErrorKind::InvalidDigit
            );
        }
        // this only stringifies in base 10
        let min = BString::from(u8::MIN.to_string());
        assert_eq!(u8::from_bytes_radix(&min.as_bstr(), 10), Ok(u8::MIN));
        let max = BString::from(u8::MAX.to_string());
        assert_eq!(u8::from_bytes_radix(&max.as_bstr(), 10), Ok(u8::MAX));

        let maxmax = BString::from((u8::MAX as i16 + 1_i16).to_string());
        assert_eq!(
            u8::from_bytes_radix(&maxmax.as_bstr(), 10).unwrap_err().kind(),
            &IntErrorKind::PosOverflow
        );
    }

    #[test]
    fn parse_i8() {
        for radix in 2..=36 {
            let r = radix as i8;

            assert_eq!(i8::from_bytes_radix(&B("0"), radix), Ok(0));

            let eleven = i8::from_bytes_radix(&B("11"), radix);
            assert_eq!(eleven, Ok(r + 1));

            // Eight ones in a row is sufficient to overflow an i8
            let pos_overflow = i8::from_bytes_radix(&B("11111111"), radix);
            assert_eq!(
                pos_overflow.unwrap_err().kind(),
                &IntErrorKind::PosOverflow
            );

            let leading_minus = i8::from_bytes_radix(&B("-11"), radix);
            assert_eq!(leading_minus, Ok(-(r + 1)));

            let two_wrongs = i8::from_bytes_radix(&B("--11"), radix);
            assert_eq!(
                two_wrongs.unwrap_err().kind(),
                &IntErrorKind::InvalidDigit
            );

            let empty = i8::from_bytes_radix(&B(""), radix);
            assert_eq!(empty.unwrap_err().kind(), &IntErrorKind::Empty);

            let leading_plus = i8::from_bytes_radix(&B("+11"), radix);
            assert_eq!(leading_plus, Ok(r + 1));

            let ungood = i8::from_bytes_radix(&B("++11"), radix);
            assert_eq!(
                ungood.unwrap_err().kind(),
                &IntErrorKind::InvalidDigit
            );

            let plus_only = i8::from_bytes_radix(&B("+"), radix);
            assert_eq!(
                plus_only.unwrap_err().kind(),
                &IntErrorKind::InvalidDigit
            );
            let minus_only = i8::from_bytes_radix(&B("-"), radix);
            assert_eq!(
                minus_only.unwrap_err().kind(),
                &IntErrorKind::InvalidDigit
            );

            let neg_overflow = i8::from_bytes_radix(&B("-11111111"), radix);
            assert_eq!(
                neg_overflow.unwrap_err().kind(),
                &IntErrorKind::NegOverflow
            );
        }
        // this only stringifies in base 10
        let min = BString::from(i8::MIN.to_string());
        assert_eq!(i8::from_bytes_radix(&min.as_bstr(), 10).unwrap(), i8::MIN);
        let max = BString::from(i8::MAX.to_string());
        assert_eq!(i8::from_bytes_radix(&max.as_bstr(), 10).unwrap(), i8::MAX);

        let minmin = BString::from((i8::MIN as i16 - 1_i16).to_string());
        assert_eq!(
            i8::from_bytes_radix(&minmin.as_bstr(), 10).unwrap_err().kind(),
            &IntErrorKind::NegOverflow
        );

        let maxmax = BString::from((i8::MAX as i16 + 1_i16).to_string());
        assert_eq!(
            i8::from_bytes_radix(&maxmax.as_bstr(), 10).unwrap_err().kind(),
            &IntErrorKind::PosOverflow
        );
    }

    /// Test a radix that's greater than allowed
    #[test]
    #[should_panic]
    fn radix_too_large() {
        let b = B("11");
        let _ = u8::from_bytes_radix(&b, 1000);
    }

    /// Ensure we behave like the stdlib here
    #[test]
    fn underscore_whitespace() {
        let _ = i32::from_str_radix("1_000_000", 10).unwrap_err();
        let _ = i32::from_bytes_radix(&B("1_000_000"), 10).unwrap_err();

        let _ = i32::from_str_radix("1 000 000", 10).unwrap_err();
        let _ = i32::from_bytes_radix(&B("1 000 000"), 10).unwrap_err();
    }
}
