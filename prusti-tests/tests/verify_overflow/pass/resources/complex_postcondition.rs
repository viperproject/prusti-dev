// compile-flags: -Psimplify_encoding=false
// TODO: Fix bug in simplifier
#![allow(dead_code, unused)]
use prusti_contracts::*;

#[resource_kind]
struct Money();

#[ensures(
    (n > 1 && true) ==> resource(Money(), 1)
)]
fn foo(n: u32) -> bool {
    produce!(resource(Money(), 1));
    true
}

pub fn main(){}
