// compile-flags: -Ptime_reasoning=true

use prusti_contracts::*;

#[requires(time_credits(n as usize))]
#[ensures(time_receipts(n as usize))]
fn foo(n: u32) -> u32 {
    n
}

#[requires(time_credits(10))]
#[ensures(time_receipts(10))]
fn main() {
    let mut i = 0;
    while i < 10 {
        body_invariant!(time_credits(10 - i));
        body_invariant!(time_receipts(i));
        i += 1;
    }
}
