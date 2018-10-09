bstr
====
This crate provides a `BString` and `BStr` types that are conventionally UTF-8
for Rust. They differ from the standard library's `String` and `str` types in
that they are not required to be valid UTF-8.

[![Linux build status](https://api.travis-ci.org/BurntSushi/bstr.svg)](https://travis-ci.org/BurntSushi/bstr)
[![Windows build status](https://ci.appveyor.com/api/projects/status/github/BurntSushi/bstr?svg=true)](https://ci.appveyor.com/project/BurntSushi/bstr)
[![](http://meritbadge.herokuapp.com/bstr)](https://crates.io/crates/bstr)

**THIS CRATE IS A WORK IN PROGRESS.**


### Documentation

https://docs.rs/bstr


### Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
bstr = "0.1"
```

and this to your crate root:

```rust
extern crate bstr;
```


### License

This project is licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or
   http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or
   http://opensource.org/licenses/MIT)

at your option.
