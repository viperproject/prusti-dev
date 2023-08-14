use prusti_contracts::*;

#[pure]
#[ensures(double(x) % 2 == 0)] //~ ERROR precondition of pure function call might not hold
fn double(x: i64) -> i64 { //~ ERROR only trusted functions can call themselves in their contracts
    2 * x
}

fn main() {}
