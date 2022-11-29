// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

#[requires(time_credits(2))]
#[ensures(time_receipts(2))]
fn main() {
    constant();
}

#[requires(time_credits(1))]
#[ensures(time_receipts(1))]
fn constant() -> u32 {
    42
}
