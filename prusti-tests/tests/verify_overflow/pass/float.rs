use prusti_contracts::*;

#[ensures(result > 0.0)]
fn test_floats32_pos() -> f32 {
    return 1.0f32;
}

#[ensures(result < 0.0)]
fn test_floats32_neg() -> f32 {
    return -1.0f32;
}

#[ensures(result == 0.0)]
fn test_floats32_zero() -> f32 {
    return 0.0f32;
}

#[ensures(result > 0.0)]
fn test_floats64_pos() -> f64 {
    return 1.0f64;
}

#[ensures(result < 0.0)]
fn test_floats64_neg() -> f64 {
    return -1.0f64;
}

#[ensures(result == 0.0)]
fn test_floats64_zero() -> f64 {
    return 0.0f64;
}

#[requires(a < 0.0)]
#[ensures(result > 0.0)]
fn test_float_with_params(a: f32) -> f32{
    return -a;
}

fn test_f32_from_bv() {
    let _a = 1.2f32;
}

fn test_f32_add() {
    let a = 1.2f32;
    let b = 1.4f32;
    let _c = a + b;
}

fn test_f32_sub() {
    let a = 1.2f32;
    let b = 1.4f32;
    let _c = a - b;
}

fn test_f32_mul() {
    let a = 1.2f32;
    let b = 1.4f32;
    let _c = a * b;
}

fn test_f32_div() {
    let a = 1.2f32;
    let b = 1.4f32;
    let _c = a / b;
}

fn test_f32_min() {
    let a = 1.2f32;
    let b = 1.4f32;
    let _c = a.min(b);
}

fn test_f32_max() {
    let a = 1.2f32;
    let b = 1.4f32;
    let _c = a.max(b);
}

fn test_f32_eq() {
    let a = 1.2f32;
    let b = 1.4f32;
    let _c = a == b;
}

fn test_f32_leq() {
    let a = 1.2f32;
    let b = 1.4f32;
    let _c = a <= b;
}

fn test_f32_geq() {
    let a = 1.2f32;
    let b = 1.4f32;
    let _c = a >= b;
}

fn test_f32_lt() {
    let a = 1.2f32;
    let b = 1.4f32;
    let _c = a < b;
}

fn test_f32_gt() {
    let a = 1.2f32;
    let b = 1.4f32;
    let _c = a > b;
}

fn test_f32_neg() {
    let a = 1.2f32;
    let _b = -a;
}

fn test_f32_abs() {
    let a = 1.2f32;
    let _b = a.abs();
}

fn test_f64_from_bv() {
    let _a = 1.2f64;
}

fn test_f64_add() {
    let a = 1.2f64;
    let b = 1.4f64;
    let _c = a + b;
}

fn test_f64_sub() {
    let a = 1.2f64;
    let b = 1.4f64;
    let _c = a - b;
}

fn test_f64_mul() {
    let a = 1.2f64;
    let b = 1.4f64;
    let _c = a * b;
}

fn test_f64_div() {
    let a = 1.2f64;
    let b = 1.4f64;
    let _c = a / b;
}

fn test_f64_min() {
    let a = 1.2f64;
    let b = 1.4f64;
    let _c = a.min(b);
}

fn test_f64_max() {
    let a = 1.2f64;
    let b = 1.4f64;
    let _c = a.max(b);
}

fn test_f64_eq() {
    let a = 1.2f64;
    let b = 1.4f64;
    let _c = a == b;
}

fn test_f64_leq() {
    let a = 1.2f64;
    let b = 1.4f64;
    let _c = a <= b;
}

fn test_f64_geq() {
    let a = 1.2f64;
    let b = 1.4f64;
    let _c = a >= b;
}

fn test_f64_lt() {
    let a = 1.2f64;
    let b = 1.4f64;
    let _c = a < b;
}

fn test_f64_gt() {
    let a = 1.2f64;
    let b = 1.4f64;
    let _c = a > b;
}

fn test_f64_neg() {
    let a = 1.2f64;
    let _b = -a;
}

fn test_f64_abs() {
    let a = 1.2f64;
    let _b = a.abs();
}

fn main () {}
