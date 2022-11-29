// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

// This tests that we can use function with lower bound in function without specification
fn main() {
    constant();
}

// This tests that only specifing the lower bound is ok
#[ensures(time_receipts(1))]
fn constant() -> u32 {
    42
}
