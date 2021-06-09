extern crate prusti_contracts;
use prusti_contracts::*;

// #[predicate]
// fn is_finite(x:f64) -> bool {
//     -20. <= x && x <= 20.
//     // f64::NEG_INFINITY < x && x < f64::INFINITY
// }

// #[pure]
// fn abs(x: f64) -> f64 {
//     if x < 0. { -x } else { x }
// }

// #[requires(is_finite(x) && is_finite(y))]
// #[ensures(result == true)] //~ ERROR postcondition might not hold
// fn foo(x:f64, y:f64) -> bool {
//     abs(x + y) <= 20.
// } 







fn main() {}