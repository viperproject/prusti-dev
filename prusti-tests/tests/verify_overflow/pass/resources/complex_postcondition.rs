// compile-flags: -Psimplify_encoding=false
// TODO: Fix bug in simplifier
#![allow(dead_code, unused)]
use prusti_contracts::*;

#[resource]
struct Money();

#[ensures(
    (n > 1 && true) ==> transfers(Money(), 1)
)]
fn foo(n: u32) -> bool {
    produces!(transfers(Money(), 1));
    true
}

pub fn main(){}
