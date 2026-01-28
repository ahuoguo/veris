#!/bin/bash

set -e

BASEDIR=$(realpath $(dirname "$0"))

# build the rlib file for libc crate, which verus-mimalloc takes as a dependency

cd $BASEDIR
mkdir -p build

# TOOD: should I be careful about the version?
cd random
# cargo clean --release
cargo +1.92.0 build --release
cd ..
OPENDP_RLIB_NAME=$(find ./random/target/release/deps/ -name 'libopendp-*.rlib')
