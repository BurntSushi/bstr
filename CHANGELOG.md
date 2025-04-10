# Changelog
All notable changes to this project will be documented in this file.

## [1.12.0] - 2025-04-08

### Added
- Add `Default` impl for `Box<BStr>` (#206)

## [1.11.3] - 2025-01-02

No user-visible changes.

## [1.11.2] - 2025-01-02

### Fixes
- Fix `Debug` implementations of `BStr` and `BString` to use hexadecimal escapes for bytes in range from `0x1` to `0x1F` inclusive (`1` to `31` in decimal) instead of Unicode escapes (#201)

## [1.11.1] - 2024-12-11

### Other
- Unicode test data is no longer uploaded to `crates.io` package, saving space (979b3435b4a9732f40e47c71cded1307a3d4f376)

## [1.11.0] - 2024-11-14

### Breaking
- Bump MSRV from 1.65 to 1.73 (#198)

### Added
- Add `PartialEq<[u8; N]>` and `PartialOrd<[u8; N]>` impls for `BStr` and `BString` (#198)

### Fixes
- Fix `Debug` impls of `BStr` and `BString` to always use lower case in hexadecimal escapes (#198)

### Other
- Fix Clippy lint violations (#198)

## [1.10.0] - 2024-07-26

No changes in this release. Minor version was raised to reflect that new API was added.

## [1.9.2] - 2024-07-25 [YANKED]

This release was yanked because it added new API but only bumped patch version instead of minor version, violating SemVer.

### Added
- Add `From<&'a BString>` impl for `Cow<'a, BStr>` (#187)

## [1.9.1] - 2024-02-24

### Fixes
- Fix `BufReadExt::for_byte_record_with_terminator` to return immediately on end of input (7b6e0259850dfbcfa4707e88e3a6a4f2a1ad4b34)

### Other
- Fix one of benchmarks to actually measure what it is supposed to measure (cc13102d64de7b43efaf804046065b68f6c9a0c0)

## [1.9.0] - 2023-12-29

### Added
- Add `Clone` impls for iterators `Find`, `FindReverse`, `Fields`, `FieldsWith`, `Split`, `SplitReverse`, `SplitN` and `SplitNReverse` (#174)

## [1.8.0] - 2023-11-09

### Added
- Add `FromStr` impl for `BString` (#170)

## [1.7.0] - 2023-10-10

### Breaking changes
- Bump MSRV from 1.60 to 1.65 (fbf9b1d2f9aa80b5cc222d724db30906b705d3b7)

### Fixes
- Fix `{Graphemes, GraphemeIndices, Words, WordIndices, Sentences, SentenceIndices}::next` and `{Graphemes, GraphemeIndices}::next_back` to no longer panic on some inputs in `#![no_std]` (09cfd76c91711507362628c482805eed32d5f6c0)

## [1.6.2] - 2023-08-30

### Other
- Exclude code generation scripts from `crates.io` packages (#167)

## [1.6.1] - 2023-08-29

### Fixes
- Make `{Finder, FinderReverse}::into_owned` available when `alloc` feature is enabled rather than `std` (bf2a2c18aa024f72b32235e7921aaf4da8a5eb9d)

## [1.6.0] - 2023-07-05

No user-visible changes

## [1.5.0] - 2023-05-21

### Added
- Add `Borrow` and `BorrowMut` impls for conversions between `BStr`, `BString`, `str`, `String`, `[u8]` and `Vec<u8>` (#159)

### Fixes
- Fix dead code warnings when building with no default features (#159)

## [1.4.0] - 2023-03-18

### Added
- Add `ByteSlice::escape_bytes` and `ByteVec::unescape_bytes` (#154)
- Add `From<[u8; N]>` impls for `BString` and `BStr` and `From<&[u8; N]>` impl for `&BStr` (#154)

## [1.3.0] - 2023-02-20

### Added
- Add `AsRef<BStr>` impl for `BStr` (#148)

## [1.2.0] - 2023-02-01

### Added
- Add `Clone` impl for `Box<BStr>` (#145)

## [1.1.0] - 2022-12-15

### Added
- Add `ByteSlice` impl for `[u8; N]` (#133)
- Add `Deserialize` impl for `Box<BStr>` (#143)

## [1.0.1] - 2022-09-12

### Fixes
- Fix `serde` feature to actually enable `serde` impls (#134)

## [1.0.0] - 2022-09-07

### Breaking changes
- Remove `ByteSlice::copy_within_str`. Use `<[_]>::copy_within` instead (6ec5f562db5d0da2056e1555cd51631802e25559)
- Set MSRV to 1.60.0 (#128)

### Added
- Add `BStr::new` (6beae06b3ec6e2a331ce2cf701a2d378c8b9f0d2)

### Fixes
- Make `unicode` feature depend on `std` feature (72024a801c261bf351e88172a66f6a00ef4e3b86)

### Optimisations
- Speed up `{Graphemes, GraphemeIndices}::next` on ASCII text (6df1c9db1e213250e965fa57926d62f3dc64f9e3)
