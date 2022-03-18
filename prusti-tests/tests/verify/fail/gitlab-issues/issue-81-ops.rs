// compile-flags: -Poptimizations=none
use prusti_contracts::*;

#[pure]
#[requires(n > 0)]
#[ensures(true)]
#[ensures(true && (result == 5 || false))] //~ ERROR postcondition
#[ensures(true)]
fn magic(n: i32) -> i32 {
    n
}

fn main() {}
