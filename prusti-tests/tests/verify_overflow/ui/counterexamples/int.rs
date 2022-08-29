// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true -Pcheck_overflows=false

use prusti_contracts::*;

#[ensures(result != 86)]
fn test1(x: i32) -> i32 {
    let y = x + 1;
    y * 2
}

#[pure]
#[ensures(result != 42)]
fn test2(x: i32) -> i32 {
    x + 21
}

fn main() {}
