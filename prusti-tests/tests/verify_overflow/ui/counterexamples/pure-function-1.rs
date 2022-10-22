// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true -Pcheck_overflows=false

#![allow(unused)]

use prusti_contracts::*;

#[pure]
#[terminates(Int::new(1))]
fn foo(x: i32) -> i32{
    x + 5
}

#[pure]
#[terminates(Int::new(1))]
fn bar(x: i32) -> bool{
    x == 3
}

#[ensures(result)]
fn fail (x: i32,) -> bool {
    let y = foo(x);
    if bar(y) {
        false
    } else{
        true
    }
}

fn main(){}
