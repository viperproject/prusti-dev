/// Tests that parser handles spans correctly.

extern crate prusti_contracts;


#[requires="forall x: i32, y: usize :: {x + 2, x + 3; x + 4} x > 0 ==> x + 2 > 2"]
pub fn test1a(x: i32) {}

#[requires="forall x: 32, y: usize :: {} x > 0 ==> x > -1"]
pub fn test1b(x: i32) {}

#[requires="forall"]
pub fn test1c(x: i32) {}

#[requires="forall x: i32, y: usize :: {x + 2, x + 3; x + 4} x > 0 ==> x + 2 > 2
    ==> true"]
pub fn test1d(x: i32) {}


fn main() {}
