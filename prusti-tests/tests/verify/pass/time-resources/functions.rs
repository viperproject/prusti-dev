// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

#[requires(time_credits(1))]
#[ensures(time_receipts(1))]
fn foo() -> u32 {
    42
}

// This tests that calling a function with time constrains in a function without time constrant is okay
fn main() {
    foo();
}
