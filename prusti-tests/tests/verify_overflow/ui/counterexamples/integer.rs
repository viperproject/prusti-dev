//@ compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

#![allow(unused)]

use prusti_contracts::*;

#[requires(a == Int::from(2))] //force specific counterexample
#[ensures(a == Int::from(5))]
fn test1(a: Int) {}

#[requires(a == Int::from(10))] //force specific counterexample
#[ensures(!result)]
fn test2(a: Int, b: Int) -> bool{
    let c = a + b;
    c == Int::from(30)
}


#[requires(a == Int::from(10) && c == Int::from(11) && b == Int::from(0))] //force specific counterexample
#[ensures(result)]
fn test3(a: Int, b: Int, c: Int) -> bool {
    a + c >= b + c
}

fn main() {}
