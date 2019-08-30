#!/bin/sh

# vim: tabstop=2 shiftwidth=2 softtabstop=2

set -ex

cargo build --verbose
cargo build --verbose --features serde1
cargo build --verbose --no-default-features
cargo build --verbose --no-default-features --features serde1-nostd
cargo doc --verbose

if [ "$TRAVIS_RUST_VERSION" = "stable" ]; then
  rustup component add rustfmt
  cargo fmt -- --check
  (cd bench && cargo fmt -- --check)
fi

# Our dev dependencies are increasing their MSRV more quickly then we want to,
# so only test the basic build on non-stable/beta/nightly builds.
if ! echo "$TRAVIS_RUST_VERSION" | grep -Eq '^[^0-9]+$'; then
    exit 0
fi

cargo test --verbose
if [ "$TRAVIS_RUST_VERSION" = "nightly" ]; then
  cargo test --verbose --manifest-path bench/Cargo.toml --benches
fi
