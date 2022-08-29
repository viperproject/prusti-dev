// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true -Pcheck_overflows=false

use prusti_contracts::*;

#[pure]
#[requires(x >= -2)]
#[ensures(result == (x * (x + 1)) / 2)]
fn sum(x:i32) -> i32 {
    if x <= 0 {
        0
    } else {
        x + sum(x - 1)
    }
}

fn main() {}
