// The next line is only required for doctests, you can ignore/remove it
extern crate prusti_contracts;
use prusti_contracts::*;

fn main() {}

//// ANCHOR: code
#[ensures(result == x * x * x)]
fn square(x: i32) -> i32 {
    x * x * x
}

fn test() {
    let x = 10;
    let x_squared = square(x);
    prusti_assert!(x_squared == 100); //~ ERROR the asserted expression might not hold
}
//// ANCHOR_END: code