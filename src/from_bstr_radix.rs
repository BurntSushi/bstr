/** A trait which provides `from_bstr_radix()` for integer types.

This acts like `from_str_radix`, including panicking if `radix` is not in [2, 32].
However, there are a few minor differences to `from_str_radix`:
`src` is a `&BStr` and `radix` is the output type rather than always `u32`.
The result type is slightly different too.
 ```
 use bstr::BStr;
 use bstr::FromBStrRadix;
 use core::num::IntErrorKind;

for radix in 2..=36 {
    let e = BStr::new(b"");
    let empty = u8::from_bstr_radix(e, 10);
    assert_eq!(empty, Err(IntErrorKind::Empty));

    let a = BStr::new(b"11");
    let eleven = u8::from_bstr_radix(a, radix);
    assert_eq!(eleven, Ok(radix + 1));

    let bbb = BStr::new("111111111");
    let pos_overflow = u8::from_bstr_radix(bbb, radix);
    assert_eq!(pos_overflow, Err(IntErrorKind::PosOverflow));

    let ccc = BStr::new("-111");
    let neg_overflow = u8::from_bstr_radix(ccc, radix);
    assert_eq!(neg_overflow, Err(IntErrorKind::InvalidDigit));

    let radix = radix as i32;
    let totally_fine = i32::from_bstr_radix(ccc, radix);
    assert_eq!(totally_fine, Ok(-(radix*radix + radix + 1)));
}
```
*/

pub trait FromBStrRadix<T>
where
    T: PartialOrd
        + Copy
        + core::ops::Add<Output = T>
        + core::ops::Sub<Output = T>
        + core::ops::Mul<Output = T>,
{
    type Output;

    fn from_bstr_radix(
        src: &crate::BStr,
        radix: Self::Output,
    ) -> Result<Self::Output, core::num::IntErrorKind>;
}

macro_rules! make_from_bstr_radix {
    ($t:ident) => {
        impl FromBStrRadix<$t> for $t {
            type Output = $t;

            fn from_bstr_radix(
                src: &crate::BStr,
                radix: $t,
            ) -> Result<$t, core::num::IntErrorKind> {
                // This more-or-less follows the stdlib implementation, but it's... simpler.

                assert!((2..=36).contains(&radix), "from_str_radix_int: must lie in the range `[2, 36]` - found {}", radix);

                if src.is_empty() {
                    return Err(core::num::IntErrorKind::Empty);
                }

                // The stdlib implementation is that runs of `+` or `-` are invalid.
                // So we need only consider the leading character.
                let (start, is_neg) = if src[0] == b'-' {(1, true) } else if src[0] == b'+' {(1, false)} else {(0, false)};

                // Leading negative on an unsigned type
                if is_neg && $t::MIN == 0 {
                    return Err(core::num::IntErrorKind::InvalidDigit);
                }

                // Input string was a single plus or minus
                if start == 1 && src.len() == 1 {
                    return Err(core::num::IntErrorKind::InvalidDigit);
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
                        return Err(core::num::IntErrorKind::InvalidDigit);
                    };

                    if is_neg {
                        if let Some(x) = mul.and_then(|m| m.checked_sub(s as $t)){
                            acc = x;
                        } else {
                            return Err(core::num::IntErrorKind::NegOverflow);
                        }
                    } else {
                        if let Some(x) = mul.and_then(|m| m.checked_add(s as $t)) {
                            acc = x;
                        } else {
                            return Err(core::num::IntErrorKind::PosOverflow);
                        }
                    }
                }
                Ok(acc)
            }
        }
    }
}

make_from_bstr_radix!(u8);
make_from_bstr_radix!(u16);
make_from_bstr_radix!(u32);
make_from_bstr_radix!(u64);
make_from_bstr_radix!(u128);
make_from_bstr_radix!(usize);
make_from_bstr_radix!(i8);
make_from_bstr_radix!(i16);
make_from_bstr_radix!(i32);
make_from_bstr_radix!(i64);
make_from_bstr_radix!(i128);
make_from_bstr_radix!(isize);

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
    use core::num::IntErrorKind;

    #[test]
    fn all_radices_u8() {
        for radix in 2..=36 {
            let z = BStr::new(b"0");
            assert_eq!(u8::from_bstr_radix(z, radix), Ok(0));

            let a = BStr::new(b"11");
            let eleven = u8::from_bstr_radix(a, radix);
            assert_eq!(eleven, Ok(radix + 1));

            let b = BStr::new(b"111111111");
            let pos_overflow = u8::from_bstr_radix(b, radix);
            assert_eq!(pos_overflow, Err(IntErrorKind::PosOverflow));

            let c = BStr::new(b"-11");
            let negatory = u8::from_bstr_radix(c, radix);
            assert_eq!(negatory, Err(IntErrorKind::InvalidDigit));

            let d = BStr::new(b"--11");
            let two_wrongs = u8::from_bstr_radix(d, radix);
            assert_eq!(two_wrongs, Err(IntErrorKind::InvalidDigit));

            let e = BStr::new(b"");
            let empty = u8::from_bstr_radix(e, radix);
            assert_eq!(empty, Err(IntErrorKind::Empty));

            let f = BStr::new(b"+11");
            assert_eq!(u8::from_bstr_radix(f, radix), Ok(radix + 1));

            let g = BStr::new(b"++11");
            assert_eq!(
                u8::from_bstr_radix(g, radix),
                Err(IntErrorKind::InvalidDigit)
            );

            let i = BStr::new("+");
            assert_eq!(
                u8::from_bstr_radix(i, radix),
                Err(IntErrorKind::InvalidDigit)
            );
        }
        // this only stringifies in base 10
        let min = BString::from(u8::MIN.to_string());
        assert_eq!(u8::from_bstr_radix(min.as_bstr(), 10), Ok(u8::MIN));
        let max = BString::from(u8::MAX.to_string());
        assert_eq!(u8::from_bstr_radix(max.as_bstr(), 10), Ok(u8::MAX));
    }

    #[test]
    fn all_radices_u64() {
        for radix in 2..=36 {
            let z = BStr::new(b"0");
            assert_eq!(u64::from_bstr_radix(z, radix), Ok(0));

            let a = BStr::new(b"11");
            let eleven = u64::from_bstr_radix(a, radix);
            assert_eq!(eleven, Ok(radix + 1));

            let b = BStr::new(b"11111111111111111111111111111111111111111111111111111111111111111");
            let pos_overflow = u64::from_bstr_radix(b, radix);
            assert_eq!(pos_overflow, Err(IntErrorKind::PosOverflow));

            let c = BStr::new(b"-11");
            let negatory = u64::from_bstr_radix(c, radix);
            assert_eq!(negatory, Err(IntErrorKind::InvalidDigit));

            let d = BStr::new(b"--11");
            let two_wrongs = u64::from_bstr_radix(d, radix);
            assert_eq!(two_wrongs, Err(IntErrorKind::InvalidDigit));

            let e = BStr::new(b"");
            let empty = u64::from_bstr_radix(e, radix);
            assert_eq!(empty, Err(IntErrorKind::Empty));

            let f = BStr::new(b"+11");
            assert_eq!(u64::from_bstr_radix(f, radix), Ok(radix + 1));

            let g = BStr::new(b"++11");
            assert_eq!(
                u64::from_bstr_radix(g, radix),
                Err(IntErrorKind::InvalidDigit)
            );

            let i = BStr::new("+");
            assert_eq!(
                u64::from_bstr_radix(i, radix),
                Err(IntErrorKind::InvalidDigit)
            );
        }
        // this only stringifies in base 10
        let min = BString::from(u64::MIN.to_string());
        assert_eq!(u64::from_bstr_radix(min.as_bstr(), 10).unwrap(), u64::MIN);
        let max = BString::from(u64::MAX.to_string());
        assert_eq!(u64::from_bstr_radix(max.as_bstr(), 10).unwrap(), u64::MAX);
    }

    #[test]
    fn all_radices_i8() {
        for radix in 2..=36 {
            let z = BStr::new(b"0");
            assert_eq!(i8::from_bstr_radix(z, radix), Ok(0));

            let a = BStr::new(b"11");
            let eleven = i8::from_bstr_radix(a, radix);
            assert_eq!(eleven, Ok(radix + 1));

            let b = BStr::new(b"111111111");
            let pos_overflow = i8::from_bstr_radix(b, radix);
            assert_eq!(pos_overflow, Err(IntErrorKind::PosOverflow));

            let c = BStr::new(b"-11");
            let totally_fine = i8::from_bstr_radix(c, radix);
            assert_eq!(totally_fine, Ok(-(radix + 1)));

            let d = BStr::new(b"--11");
            let two_wrongs = i8::from_bstr_radix(d, radix);
            assert_eq!(two_wrongs, Err(IntErrorKind::InvalidDigit));

            let e = BStr::new(b"");
            let empty = i8::from_bstr_radix(e, radix);
            assert_eq!(empty, Err(IntErrorKind::Empty));

            let f = BStr::new(b"+11");
            assert_eq!(i8::from_bstr_radix(f, radix), Ok(radix + 1));

            let g = BStr::new(b"++11");
            assert_eq!(
                i8::from_bstr_radix(g, radix),
                Err(IntErrorKind::InvalidDigit)
            );

            let h = BStr::new(b"-111111111");
            assert_eq!(
                i8::from_bstr_radix(h, radix).unwrap_err(),
                IntErrorKind::NegOverflow
            );
        }
        // this only stringifies in base 10
        let min = BString::from(i8::MIN.to_string());
        assert_eq!(i8::from_bstr_radix(min.as_bstr(), 10).unwrap(), i8::MIN);
        let max = BString::from(i8::MAX.to_string());
        assert_eq!(i8::from_bstr_radix(max.as_bstr(), 10).unwrap(), i8::MAX);
    }

    #[test]
    fn all_radices_i64() {
        for radix in 2..=36 {
            let z = BStr::new(b"0");
            assert_eq!(i64::from_bstr_radix(z, radix), Ok(0));

            let a = BStr::new(b"11");
            let eleven = i64::from_bstr_radix(a, radix);
            assert_eq!(eleven, Ok(radix + 1));

            let b = BStr::new(b"11111111111111111111111111111111111111111111111111111111111111111");
            let pos_overflow = i64::from_bstr_radix(b, radix);
            assert_eq!(pos_overflow, Err(IntErrorKind::PosOverflow));

            let c = BStr::new(b"-11");
            let totally_fine = i64::from_bstr_radix(c, radix);
            assert_eq!(totally_fine, Ok(-(radix + 1)));

            let d = BStr::new(b"--11");
            let two_wrongs = i64::from_bstr_radix(d, radix);
            assert_eq!(two_wrongs, Err(IntErrorKind::InvalidDigit));

            let e = BStr::new(b"");
            let empty = i64::from_bstr_radix(e, radix);
            assert_eq!(empty, Err(IntErrorKind::Empty));

            let f = BStr::new(b"+11");
            assert_eq!(i64::from_bstr_radix(f, radix), Ok(radix + 1));

            let g = BStr::new(b"++11");
            assert_eq!(
                i64::from_bstr_radix(g, radix),
                Err(IntErrorKind::InvalidDigit)
            );

            let h = BStr::new(b"-11111111111111111111111111111111111111111111111111111111111111111");
            assert_eq!(
                i64::from_bstr_radix(h, radix).unwrap_err(),
                IntErrorKind::NegOverflow
            );

            let i = BStr::new("+");
            assert_eq!(
                i64::from_bstr_radix(i, radix),
                Err(IntErrorKind::InvalidDigit)
            );

            let j = BStr::new("-");
            assert_eq!(
                i64::from_bstr_radix(j, radix),
                Err(IntErrorKind::InvalidDigit)
            );
        }

        // this only stringifies in base 10
        let min = BString::from(i64::MIN.to_string());
        assert_eq!(i64::from_bstr_radix(min.as_bstr(), 10).unwrap(), i64::MIN);
        let max = BString::from(i64::MAX.to_string());
        assert_eq!(i64::from_bstr_radix(max.as_bstr(), 10).unwrap(), i64::MAX);
    }
}
