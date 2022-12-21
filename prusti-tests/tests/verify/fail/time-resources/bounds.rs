// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

// This tests that we can't call functions only with upper bounds in a function with lower and upper bounds specification

#[requires(time_credits(1))]
fn constant() -> u32 {
    42
}

#[requires(time_credits(2))]
#[ensures(time_receipts(2))]
fn main() {
    constant(); //~ ERROR
}
