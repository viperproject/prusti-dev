// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

#![allow(unused)]

use prusti_contracts::*;

#[ensures(a == Int::new(5))]
fn test1(a: Int) {}

#[requires(a == Int::new(10))] //force specific counterexample
#[ensures(!result)]
fn test2(a: Int, b: Int) -> bool{
    let c = a + b;
    c == Int::new(30)
}


#[requires(a == Int::new(10) && c == Int::new(11))] //force specific counterexample
#[ensures(result)]
fn test3(a: Int, b: Int, c: Int) -> bool {
    a + c >= b + c
}

fn main() {}
