#![feature(register_tool)]
#![register_tool(prusti)]

use prusti_contracts::*;

#[requires(true ++ 1)]
fn test1() {}

#[ensures(true ++ 1)]
fn test2() {}

fn test3() {
    for _ in 0..2 {
        body_invariant!(true ++ 1)
    }
}

#[requires(true)]
#[ensures(true)]
fn test4() {
    for _ in 0..2 {
        body_invariant!(true ++ 1)
    }
}

#[requires(true)]
#[ensures(true ++ 1)]
fn test5() {
    for _ in 0..2 {
        body_invariant!(true ++ 1)
    }
}

fn main() {}
