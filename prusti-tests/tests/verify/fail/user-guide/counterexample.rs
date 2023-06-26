//// ANCHOR: nothing
//// ANCHOR_END: nothing
// The next line is only required for doctests, you can ignore/remove it
extern crate prusti_contracts;
use prusti_contracts::*;

fn main() {}

// Note: counterexample = true

//// ANCHOR: code
// #[requires(x >= 0)] // Forgot to add this condition
#[ensures(result == x * (x + 1) / 2)] //~ ERROR postcondition might not hold
fn summation(x: i32) -> i32 {
    let mut i = 1;
    let mut sum = 0;
    while i <= x {
        body_invariant!(sum == (i - 1) * i / 2);
        sum += i;
        i += 1;
    }
    sum
}
//// ANCHOR_END: code