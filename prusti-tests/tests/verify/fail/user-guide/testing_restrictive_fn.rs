// The next line is only required for doctests, you can ignore/remove it
extern crate prusti_contracts;
use prusti_contracts::*;

fn main() {}

//// ANCHOR: code
#[requires(x == 10)] // Restrictive precondition
#[ensures(result == x * x)]
pub fn restrictive_square(x: i32) -> i32 {
    x * x
}

fn test() {
    assert!(restrictive_square(10) == 100); // Works
    assert!(restrictive_square(5) == 25); //~ ERROR precondition might not hold.
}
//// ANCHOR_END: code