// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

// This tests that we can't call functions only with upper bounds in a function with a lower bound specification and inversely
#[requires(time_credits(2))]
fn foo() {
    constant();
}

#[ensures(time_receipts(1))]
fn constant() -> u32 {
    42
}

#[ensures(time_receipts(3))]
fn main() {
    foo();
}
