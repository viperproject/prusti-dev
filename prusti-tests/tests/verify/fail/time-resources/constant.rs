// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

#[requires(time_credits(0))] //~ ERROR
#[ensures(time_receipts(4))] //~ ERROR
fn main() -> () {
    ()
}
