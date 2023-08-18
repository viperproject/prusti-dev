// The next line is only required for doctests, you can ignore/remove it
extern crate prusti_contracts;
use prusti_contracts::*;

fn main() {}

//// ANCHOR: code
#[pure]
// Note that a postcondition is not actually needed here, since `abs` is #[pure]
#[ensures(x >= 0 ==> result == x)]
pub fn abs(x: i32) -> i32 {
    x
}

fn test_abs() {
    prusti_assert!(abs(8) == 8); // Works
    prusti_assert!(abs(-10) == 10); //~ ERROR the asserted expression might not hold
}
//// ANCHOR_END: code
