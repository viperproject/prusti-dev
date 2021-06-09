extern crate prusti_contracts;
use prusti_contracts::*;

#[predicate]
fn is_zero(x:f64) -> bool { x == 0. }

#[predicate]
fn is_finite(x:f64) -> bool {f64::NEG_INFINITY < x && x < f64::INFINITY}

#[requires(is_finite(x))]
#[ensures(is_zero(result))]
fn foo(x:f64) -> f64 { x - x }


fn main() {}