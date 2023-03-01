// compile-flags: -Pviper_backend=Lithium

use prusti_contracts::*;

#[pure]
#[terminates]
fn is_nan_32(f: f32) -> bool {
    f != f
}

#[pure]
#[terminates]
fn is_nan_64(f: f64) -> bool {
    f != f
}

#[pure]
#[terminates]
fn is_infinite_32(f: f32) -> bool {
    f == f32::INFINITY || f == f32::NEG_INFINITY
}

#[pure]
#[terminates]
fn is_infinite_64(f: f64) -> bool {
    f == f64::INFINITY || f == f64::NEG_INFINITY
}

fn test_nan_32_is_nan() {
    let a = 0.0f32 / 0.0f32;
    assert!(is_nan_32(a));
}

fn test_nan_32_is_inf() {
    let a = 0.0f32 / 0.0f32;
    assert!(is_infinite_32(a)); //~ ERROR might not hold
}

fn test_nan_64_is_nan() {
    let a = 0.0f64 / 0.0f64;
    assert!(is_nan_64(a));
}

fn test_nan_64_is_inf() {
    let a = 0.0f64 / 0.0f64;
    assert!(is_infinite_64(a)); //~ ERROR might not hold
}

fn test_inf_32_is_inf() {
    let a = 1.0f32 / 0.0f32;
    assert!(is_infinite_32(a));
}

fn test_inf_32_is_nan() {
    let a = 1.0f32 / 0.0f32;
    assert!(is_nan_32(a)); //~ ERROR might not hold
}

fn test_inf_64_is_inf() {
    let a = 1.0f64 / 0.0f64;
    assert!(is_infinite_64(a));
}

fn test_inf_64_is_nan() {
    let a = 1.0f64 / 0.0f64;
    assert!(is_nan_64(a)); //~ ERROR might not hold
}

fn test_neg_inf_32_is_inf() {
    let a = -1.0f32 / 0.0f32;
    assert!(is_infinite_32(a));
}

fn test_neg_inf_32_is_nan() {
    let a = -1.0f32 / 0.0f32;
    assert!(is_nan_32(a)); //~ ERROR might not hold
}

fn test_neg_inf_64_is_inf() {
    let a = -1.0f64 / 0.0f64;
    assert!(is_infinite_64(a));
}

fn test_neg_inf_64_is_nan() {
    let a = -1.0f64 / 0.0f64;
    assert!(is_nan_64(a)); //~ ERROR might not hold
}

// THEORY OF INIFINITY

#[requires(is_nan_32(f))]
#[ensures(!is_infinite_32(f))]
fn axiom1(f: f32) {}

#[requires(is_infinite_32(f))]
#[ensures(!is_nan_32(f))]
fn axiom2(f: f32) {}

#[requires(is_infinite_32(f))]
#[ensures(is_infinite_32(f + 1_f32))]
fn axiom3(f: f32) {}

#[requires(is_infinite_32(f))]
#[ensures(is_infinite_32(f - 1_f32))]
fn axiom4(f: f32) {}

#[requires(is_infinite_32(f))]
#[ensures(is_infinite_32(f * 2_f32))]
fn axiom5(f: f32) {}

#[requires(is_infinite_32(f))]
#[ensures(is_infinite_32(f / 2_f32))]
fn axiom6(f: f32) {}

// THEORY OF NAN

#[requires(is_infinite_32(f))]
#[ensures(!is_nan_32(f))]
fn axiom7(f: f32) {}

#[requires(is_nan_32(f))]
#[ensures(is_nan_32(f + 1_f32))]
fn axiom8(f: f32) {}

#[requires(is_nan_32(f))]
#[ensures(is_nan_32(f - 1_f32))]
fn axiom9(f: f32) {}

#[requires(is_nan_32(f))]
#[ensures(is_nan_32(f * 2_f32))]
fn axiom10(f: f32) {}

#[requires(is_nan_32(f))]
#[ensures(is_nan_32(f / 2_f32))]
fn axiom11(f: f32) {}

#[ensures(is_nan_32(f32::NAN))]
fn axiom12() {}

fn main() {}
