//// ANCHOR: nothing
//// ANCHOR_END: nothing
// The next line is only required for doctests, you can ignore/remove it
extern crate prusti_contracts;
use prusti_contracts::*;

fn main() {}

//// ANCHOR: specification
#[requires(x >= 0)]
#[ensures(result == x * (x + 1) / 2)]
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
//// ANCHOR_END: specification