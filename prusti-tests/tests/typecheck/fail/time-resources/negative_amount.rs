// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

#[requires(time_credits(-1))] //~ ERROR
#[ensures(time_receipts(-1))] //~ ERROR
fn main() {}
