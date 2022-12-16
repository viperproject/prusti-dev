// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

// This tests that omitting the upper bound fails
#[ensures(time_receipts(1))]
fn main() {
  let mut i = 0;
  let mut _n = 0;
  while i < 42 {
    _n += 1;
    i += 1;
  }
}