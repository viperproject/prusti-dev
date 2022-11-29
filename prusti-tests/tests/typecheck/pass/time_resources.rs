// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

#[requires(time_credits(10))]
#[ensures(time_receipts(10))]
fn main() {
    let mut i: usize = 0;
    while i < 10 {
        body_invariant!(time_credits(10 - i));
        body_invariant!(time_receipts(i));
        i += 1;
    }
}
