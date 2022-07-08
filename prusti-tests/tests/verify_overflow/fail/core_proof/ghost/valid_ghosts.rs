// compile-flags: -Punsafe_core_proof=true

#![allow(unused)]

use prusti_contracts::*;
use std::ops::*;

fn test1() {
    let mut x = Ghost::new(5u32);
    let g = ghost! {
        x = Ghost::new(10);
    };
    prusti_assert!(x == Ghost::new(10));
}

fn test2() {
    let mut x = Ghost::new(5u32);
    let g = ghost! {
        x = Ghost::new(10);
    };
    prusti_assert!(x == Ghost::new(5));     //~ ERROR: the asserted expression might not hold
}

fn main() {}
