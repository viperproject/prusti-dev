// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

// This tests that omitting the upper bound fails
#[ensures(time_receipts(1))]
fn main() {//~ ERROR Not enough time credits.
    let mut i = 0;
    let mut _n = 0;
    i += 42;
}
