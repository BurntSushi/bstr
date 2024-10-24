//! This fuzzer attempts to test the functional correctness of the `bstr::utf8::validate` function.
//! This coverage is desirable, because some `unsafe` blocks in the `bstr` crate depend on the
//! guarantees made by `utf8::validate` - e.g. the soundness of `bstr::ByteSlice::to_str` depends
//! on these guarantees.
//!
//! The `utf8::validate` function is in a non-public module, which means that we can't test it
//! directly.  Therefore we test via `bstr::ByteSlice::to_str` instead.
//!
//! We use the following [test oracle](https://en.wikipedia.org/wiki/Test_oracle) to validate
//! results returned by `utf8::validate`:
//!
//! * A standard library implementation (`std::str::from_utf8` is analogous to
//!   `bstr::ByteSlice::to_str` and `run_utf8_validation` in `core/str/validations.rs` is analogous
//!   to `bstr::utf8::validate`).
//!   https://github.com/BurntSushi/bstr/issues/25#issuecomment-543835601 explains
//!   why `bstr` doesn't reuse the standard library's implementation.
//! * TODO: Consider also adding a manual, simple (and therefore hopefully "obviously correct")
//!   implementation as another test oracle.

#![no_main]

use bstr::ByteSlice;
use libfuzzer_sys::fuzz_target;

fn validate(data: &[u8]) {
    let bstr_result = data.to_str();
    let std_result = std::str::from_utf8(data);

    match bstr_result {
        Ok(bstr_str) => {
            let Ok(std_str) = std_result else {
                panic!("`bstr` succeeded but `std` failed");
            };
            assert_eq!(data.as_ptr(), bstr_str.as_ptr());
            assert_eq!(data.as_ptr(), std_str.as_ptr());
            assert_eq!(data.len(), bstr_str.len());
            assert_eq!(data.len(), std_str.len());
        }
        Err(bstr_err) => {
            let Err(std_err) = std_result else {
                panic!("`bstr` failed but `std` succeeded");
            };
            assert_eq!(bstr_err.error_len(), std_err.error_len());
            assert_eq!(bstr_err.valid_up_to(), std_err.valid_up_to());
        }
    }
}

fuzz_target!(|data: &[u8]| {
    // Test various alignments, because `utf8::validate` calls into `ascii::first_non_ascii_byte`
    // and the latter is sensitive to the alignment.
    for alignment_offset in 0..=(std::cmp::min(data.len(), 16)) {
        validate(&data[alignment_offset..]);
    }
});
