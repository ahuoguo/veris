#!/bin/bash
exec cargo verus verify -p ub "$@" --manifest-path "$(dirname "$0")/../Cargo.toml"
