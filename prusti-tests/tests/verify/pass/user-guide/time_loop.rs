// compile-flags: -Ptime_reasoning=true
//// ANCHOR: nothing
//// ANCHOR_END: nothing
// The next line is only required for doctests, you can ignore/remove it
extern crate prusti_contracts;
use prusti_contracts::*;

#[requires(time_credits(1))]
fn main() {}

//// ANCHOR: code
#[requires(time_credits(n + 1))]
#[ensures(time_receipts(n + 1))]
fn do_work(n: usize) {
    let mut i = 0;
    while i < n {
        body_invariant!(time_receipts(i) & time_credits(n - i));
        i += 1;
    }
}
//// ANCHOR_END: code
