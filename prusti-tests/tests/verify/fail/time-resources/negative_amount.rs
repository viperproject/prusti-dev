// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

#[requires(time_credits(1 - 2))] //~ ERROR
#[ensures(time_receipts(2 - 4))] //~ ERROR
fn main() {}
