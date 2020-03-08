//! Quickly smoke test that this all compiles.
#[macro_use]
extern crate bstr;

use bstr::{BStr, B};

pub const EXAMPLE_FILE: &'static BStr =
    literal!(include_bytes!("./example.txt"));
pub static STATIC_ITEM: &'static BStr = literal!(b"static!");

struct Foo;

impl Foo {
    pub const INHERENT: &'static BStr = literal!(b"1234");
}

#[test]
fn test_constants() {
    assert_eq!(EXAMPLE_FILE, literal!(b"foobar 1 2 3 abc"));
    assert_eq!(STATIC_ITEM, literal!(b"static!"));
    assert_eq!(Foo::INHERENT, B("1234"));
}
