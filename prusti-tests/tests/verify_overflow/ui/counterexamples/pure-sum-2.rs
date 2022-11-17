// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true -Pcheck_overflows=false

use prusti_contracts::*;

#[pure]
#[terminates(Int::new(x) + Int::new(1))]
fn sum(x:i64) -> i64 {
    if x <= 0 {
        0
    } else {
        x + sum(x - 1)
    }
}

#[ensures(sum(5) == 0)] //TODO: add ce support for pure functions in specifications
fn test1() {}

fn main() {}
