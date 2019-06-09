#!/bin/sh

set -ex

cargo build --verbose
cargo doc --verbose

# Our dev dependencies are increasing their MSRV more quickly then we want to,
# so only test the basic build on non-stable/beta/nightly builds.
if ! echo "$TRAVIS_RUST_VERSION" | grep -Eq '^[^0-9]+$'; then
    exit 0
fi

cargo test --verbose
if [ "$TRAVIS_RUST_VERSION" = "nightly" ]; then
  cargo bench --verbose --manifest-path bench/Cargo.toml -- --test
fi
