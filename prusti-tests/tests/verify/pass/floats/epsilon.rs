extern crate prusti_contracts;
use prusti_contracts::*;

#[requires(x >= 0.)]
#[ensures(result > 0.)]
fn plus_eps(x:f64) -> f64 { x + f64::EPSILON}

fn main() {    
    assert!(0. + f64::EPSILON > 0.); // might fail because of timeout
}