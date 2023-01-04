// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

// TODO: fix error reporting for negative time resources.

#[requires(time_credits(1))]
#[ensures(time_receipts(2 - 4))] //~ ERROR
fn main() {
}

#[requires(time_credits(1))]
fn foo() {
  assert!(time_credits(1 - 2)); //~ ERROR 
}
