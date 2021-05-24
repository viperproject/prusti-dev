#![feature(type_ascription)]
#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(unused_must_use)]

extern crate prusti_contracts;
use prusti_contracts::*;

#[prusti_use("./prusti-tests/tests/verify/pass/extern-spec/swap.rs")]
fn main() {
    let mut x = 5;
    let mut y = 42;

    std::mem::swap(&mut x, &mut y);

    assert!(42 == x);
    assert!(5 == y);
}