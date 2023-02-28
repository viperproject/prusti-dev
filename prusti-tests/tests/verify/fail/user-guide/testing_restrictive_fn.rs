// The next line is only required for doctests, you can ignore/remove it
extern crate prusti_contracts;
use prusti_contracts::*;

fn main() {}

//// ANCHOR: code
#[requires(x == 10)]
#[ensures(result == x * x)]
fn restrictive_square(x: i32) -> i32 {
    x * x
}

fn test() {
    let x = 10;
    let x_squared = restrictive_square(x);

    let y = 5;
    let y_squared = restrictive_square(y); //~ ERROR precondition might not hold.
}
//// ANCHOR_END: code