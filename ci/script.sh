#!/bin/sh

set -ex

cargo build --verbose
cargo doc --verbose
cargo test --verbose
