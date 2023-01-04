// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

#[requires(time_credits(0))]
#[ensures(time_receipts(1))]
fn main() -> () { //~ ERROR Not enough time credits.
    ()
}

#[requires(time_credits(1))]
#[ensures(time_receipts(4))]
fn foo() {} //~ ERROR Not enough time receipts at the end of the function.
