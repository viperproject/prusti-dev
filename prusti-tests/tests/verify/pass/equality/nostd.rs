//! This is a regression test for the following error messages in `#![no_std]` crates:
//! [Prusti: invalid specification] use of impure function "core::cmp::PartialEq::eq" in pure code is not allowed
//! [Prusti: invalid specification] use of impure function "core::cmp::PartialEq::ne" in pure code is not allowed

#![no_std]

use prusti_contracts::*;

#[derive(Clone, Copy, PartialEq, Eq)]
struct A(usize);

#[pure]
#[requires(left == right)]
fn eq(left: A, right: A) -> bool {
    left == right
}

#[pure]
#[requires(left != right)]
fn ne(left: A, right: A) -> bool{
    left != right
}

fn main() {
    assert!(eq(A(0), A(0)));
    assert!(ne(A(1), A(0)));
}