// ignore-test
// We changed a few things with regards to no_std. We still want to support it
// with cargo-prusti, but from now on std is a feature of the prusti-contracts
// trait that is enabled by default. Can be disabled by setting default-features=false.
//
// Since prusti-rustc works with a precompiled version of prusti-contracts,
// we decided to enable it permanently there, which is why this test is ignored now.
// Another solution would be to compile 2 versions of prusti-contracts and make it
// configurable which version is linked, but for now we didn't see this as necessary.

//! This ui-test makes sure that `prusti-contracts` does not depend on the Rust standard library.
//! If this test fails (i.e. this file compiles successfully), then `prusti-contracts` depends on the standard library.
#![no_std]
use prusti_contracts::*;

#[requires(true)]
#[ensures(true)]
fn test() {}

fn main() {}
