// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true -Pcheck_overflows=false

use prusti_contracts::*;

#[pure]
fn sum(x:i32) -> i32 {
    if x <= 0 {
        0
    } else {
        x + sum(x - 1)
    }
}

#[ensures(sum(5) == 0)] //TODO: add ce support for pure functions in specifications
fn test1() {}

fn main() {}
