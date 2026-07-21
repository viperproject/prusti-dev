//@ compile-flags: -Punsafe_core_proof=true

#![allow(unused)]

use prusti_contracts::*;
use std::ops::*;

fn test1() {
    let x = Ghost::new(5u32);
    let x = ghost! { 10u32 };
    prusti_assert!(x == Ghost::new(10));
}

fn test2() {
    let x = Ghost::new(5u32);
    let x = ghost! { 10u32 };
    prusti_assert!(x == Ghost::new(5));     //~ ERROR: the asserted expression might not hold
}

fn main() {}
