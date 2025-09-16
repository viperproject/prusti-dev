//! An adaptation of the example from
//! https://rosettacode.org/wiki/Ackermann_function#Rust
//!
//! Changes:
//!
//! +   Replaced ``println!`` with calling trusted functions.
//! +   Unified function types.
//! +   Renamed functions.
//!
//! Verified properties:
//!
//! +   Absence of panics.
//! +   The return value is positive.
//! +   The functions are equivalent.

use prusti_contracts::*;

#[pure]
#[ensures({
    let overflow = (a > 0 && b > 0 && 0 < (a - 0x7FFFFFFF) + b) || (a < 0 && b < 0 && (a + 0x7FFFFFFF) + (b + 1) < 0);
    match result {
        Some(r) => !overflow && a + b == r,
        None => overflow,
    }
})]
#[trusted]
fn checked_add(a: i32, b: i32) -> Option<i32> {
    a.checked_add(b)
}

#[pure]
#[requires(0 <= m && 0 <= n)]
#[ensures(if let Some(r) = result { r >= 0 } else { true })]
fn ack_pure(m: i32, n: i32) -> Option<i32> {
    if m == 0 {
        checked_add(n, 1)
    } else if n == 0 {
        ack_pure(m - 1, 1)
    } else if let Some(nn) = ack_pure(m, n - 1) {
        ack_pure(m - 1, nn)
    } else {
        None
    }
}


#[requires(0 <= m && 0 <= n)]
#[ensures(result === ack_pure(m, n))]
#[ensures(if let Some(r) = result { r >= 0 } else { true })]
fn ack1(m: i32, n: i32) -> Option<i32> {
    if m == 0 {
        checked_add(n, 1)
    } else if n == 0 {
        ack1(m - 1, 1)
    } else if let Some(nn) = ack1(m, n - 1) {
        ack1(m - 1, nn)
    } else {
        None
    }
}

#[requires(0 <= m && 0 <= n)]
#[ensures(result === ack_pure(m, n))]
#[ensures(if let Some(r) = result { r >= 0 } else { true })]
fn ack2(m: i32, n: i32) -> Option<i32> {
    match (m, n) {
        (0, n) => checked_add(n, 1),
        (m, 0) => ack2(m - 1, 1),
        (m, n) => match ack2(m, n - 1) {
            Some(nn) => ack2(m - 1, nn),
            None => None,
        },
    }
}

#[trusted]
fn print_i32(a: Option<i32>) {
    println!("{:?}", a); // Some(125)
}

fn main() {
    let a1 = ack1(3, 4);
    let a2 = ack2(3, 4);
    assert!(a1 == a2);
    print_i32(a1);
}
