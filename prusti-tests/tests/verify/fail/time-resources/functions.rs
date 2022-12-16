// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

// This tests that function with time specification can only call function with time specification

#[requires(time_credits(2))]
#[ensures(time_receipts(2))]
fn main() {
    constant(); //~ ERROR
}

fn constant() -> u32 {
    42
}
