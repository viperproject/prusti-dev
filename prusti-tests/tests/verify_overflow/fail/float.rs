extern crate prusti_contracts;
use prusti_contracts::*;

#[ensures(result < 0.0)] //~ ERROR
fn test_floats32_pos() -> f32 {
    return 1.0f32;
}

#[ensures(result > 0.0)] //~ ERROR
fn test_floats32_neg() -> f32 {
    return -1.0f32;
}

#[ensures(result != 0.0)] //~ ERROR
fn test_floats32_zero() -> f32 {
    return 0.0f32;
}

#[ensures(result < 0.0)] //~ ERROR
fn test_floats64_pos() -> f64 {
    return 1.0f64;
}

#[ensures(result > 0.0)] //~ ERROR
fn test_floats64_neg() -> f64 {
    return -1.0f64;
}

#[ensures(result != 0.0)] //~ ERROR
fn test_floats64_zero() -> f64 {
    return 0.0f64;
}

#[requires(a < 0.0)]
#[ensures(result < 0.0)] //~ ERROR
fn test_float_with_params(a: f32) -> f32{
    return -a;
}

fn main () {}