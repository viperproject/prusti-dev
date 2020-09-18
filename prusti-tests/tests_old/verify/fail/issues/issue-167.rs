use prusti_contracts::*;

#[pure]
#[requires(n > 0)]
#[ensures(result == 5)] //~ ERROR postcondition might not hold
fn magic(n: i32) -> i32 {
    n
}

fn main() {}
