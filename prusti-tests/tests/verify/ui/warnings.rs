#![allow(dead_code)]
#![allow(unused)]
use prusti_contracts::*;

#[requires(result == 0)]
#[ensures(result == 0)]
fn foo(result: u32) -> u32 {
    0
}

#[trusted]
fn main() {}
