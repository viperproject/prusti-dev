// Coverage for the mathematical (unbounded) `Int` ghost type: `Int::from`
// for the various primitive integers, arithmetic, negation, every comparison
// operator, and use as a pure-function argument and return type.

use prusti_contracts::*;

// `Int::from` for every signed and unsigned width, mixed in one comparison.
fn from_all_widths() {
    prusti_assert!(Int::from(1i8) == Int::from(1u64));
    prusti_assert!(Int::from(2i16) == Int::from(2u32));
    prusti_assert!(Int::from(3i32) == Int::from(3u16));
    prusti_assert!(Int::from(4i64) == Int::from(4u8));
    prusti_assert!(Int::from(5i128) == Int::from(5u128));
    prusti_assert!(Int::from(6isize) == Int::from(6usize));
}

// Arithmetic and negation, including exact integer division and remainder.
fn arithmetic() {
    prusti_assert!(Int::from(2) + Int::from(3) == Int::from(5));
    prusti_assert!(Int::from(5) - Int::from(8) == Int::from(-3));
    prusti_assert!(Int::from(4) * Int::from(6) == Int::from(24));
    prusti_assert!(Int::from(7) / Int::from(2) == Int::from(3));
    prusti_assert!(Int::from(7) % Int::from(2) == Int::from(1));
    prusti_assert!(-Int::from(9) == Int::from(0) - Int::from(9));
}

// Every comparison operator, on both sides of the truth value.
fn comparisons() {
    prusti_assert!(Int::from(2) == Int::from(2));
    prusti_assert!(Int::from(2) != Int::from(3));
    prusti_assert!(Int::from(2) < Int::from(3));
    prusti_assert!(Int::from(2) <= Int::from(2));
    prusti_assert!(Int::from(3) > Int::from(2));
    prusti_assert!(Int::from(3) >= Int::from(3));
    prusti_assert!(!(Int::from(3) < Int::from(3)));
    prusti_assert!(!(Int::from(2) > Int::from(2)));
}

// `Int` is unbounded: sums that would overflow a fixed-width integer are exact.
fn unbounded() {
    prusti_assert!(Int::from(i64::MAX) + Int::from(1) > Int::from(i64::MAX));
    prusti_assert!(Int::from(i64::MAX) + Int::from(i64::MAX) == Int::from(2) * Int::from(i64::MAX));
}

// `Int` as a pure-function argument and return type, related in the contract.
#[pure]
#[requires(a >= Int::from(0))]
#[ensures(result >= a)]
#[ensures(result == a + a)]
fn double(a: Int) -> Int {
    a + a
}

fn use_pure() {
    let two = Int::from(2);
    prusti_assert!(double(two) == Int::from(4));
    prusti_assert!(double(double(two)) == Int::from(8));
}
