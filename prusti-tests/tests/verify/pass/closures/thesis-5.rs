#![feature(stmt_expr_attributes)]

use prusti_contracts::*;

/// Examples from Fabian Wolff's thesis.

// ignore-test
// TODO: closure state encoding, assignment

fn main() {
    let ho_cl = |i: i32| { move || -> i32 { i } };
    let mut a = ho_cl (1);
    let mut b = ho_cl (2);
    a = b;
}
