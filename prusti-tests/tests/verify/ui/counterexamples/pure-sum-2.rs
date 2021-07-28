// compile-flags: -Pcounterexample=true

use prusti_contracts::*;

#[pure]
//#[requires(x >= -2)]
//#[ensures(result == (x * (x + 1)) / 2)]
fn sum(x:i32) -> i32 {
    if x <= 0 {
        0
    } else {
        x + sum(x - 1)
    }
}

#[ensures(sum(5) == 0)]
fn test1() {}

fn main() {}
