// Symbolic completeness of the builtin `/` and `%` encodings, complementing
// the concrete cases in `no-annotations/modulo.rs`. Rust uses truncated
// division (`/` rounds toward zero, `%` takes the sign of the dividend); the
// three properties below hold for *all* operands and together pin the encoding
// down to exactly those semantics: any `q, r` with `a == b*q + r`,
// `sign(r) == sign(a)` and `|r| < |b|` is the unique truncated quotient and
// remainder. (The division identity in particular only verifies when `/` and
// `%` use a matching encoding.)

#![allow(dead_code, unused_variables)]

use prusti_contracts::*;

// Fundamental division identity ties `/` and `%` together.
#[requires(b != 0)]
#[requires(a != i32::MIN || b != -1)]
#[ensures(b * (a / b) + a % b == a)]
fn identity_i32(a: i32, b: i32) {}

// The remainder is truncated: it takes the sign of the dividend.
#[requires(b != 0)]
#[requires(a != i32::MIN || b != -1)]
#[ensures(a >= 0 ==> a % b >= 0)]
#[ensures(a <= 0 ==> a % b <= 0)]
fn rem_sign_i32(a: i32, b: i32) {}

// The remainder is strictly smaller in magnitude than the divisor.
#[requires(b != 0)]
#[requires(a != i32::MIN || b != -1)]
#[ensures(b > 0 ==> -b < a % b && a % b < b)]
#[ensures(b < 0 ==> b < a % b && a % b < -b)]
fn rem_bound_i32(a: i32, b: i32) {}

// The unsigned path takes no sign correction; the identity must still hold.
#[requires(b != 0)]
#[ensures(b * (a / b) + a % b == a)]
fn identity_usize(a: usize, b: usize) {}
