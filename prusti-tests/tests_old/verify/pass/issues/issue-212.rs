// This test checks that if a parameter is called result, the parameter is used in the specification
// instead of the return value.

#![allow(dead_code)]
use prusti_contracts::*;

#[requires(result == 0)]
#[ensures(result == 0)]
fn fun(result: i32) -> i32 {
    1
}

#[trusted]
fn main() {}
