use prusti_contracts::*;

#[requires(true))]
pub fn unbalanced_right(x: i32) {}

#[requires((true)]
pub fn unbalanced_left(x: i32) {}

fn main() {}
