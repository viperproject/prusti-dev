//! This ui-test makes sure that `prusti-contracts` does not depend on the Rust standard library.
//! If this test fails (i.e. this file compiles successfully), then `prusti-contracts` depends on the standard library.
#![no_std]
extern crate prusti_contracts;
use prusti_contracts::*;

#[requires(true)]
#[ensures(true)]
fn test() {}

fn main() {}
