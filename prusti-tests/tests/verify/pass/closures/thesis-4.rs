#![feature(stmt_expr_attributes)]

use prusti_contracts::*;

/// Examples from Fabian Wolff's thesis.

// ignore-test
// TODO: move semantics
// TODO: rewrite test to use structs with Clone (?)

fn main() {
    let mut x = "x".to_owned();
    let mut y = "y".to_owned();
    let mut z = "z".to_owned();
    let x_borrow = &x; // we can have overlapping immutable borrows

    // || introduces a closure; arguments go between the bars:
    let cl = || {
        let x_clone = x.clone(); // this only reads from x
        y.push_str(&x_clone); // modify y
        std::mem::drop(z); // this call requires ownership of z
    };

    cl();
    println!("{} {}", x_borrow, y); // we can't use z anymore here
}
