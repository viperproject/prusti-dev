#![feature(register_tool)]
#![register_tool(prusti)]

use prusti_contracts::*;

#[derive(Clone,Copy,PartialEq,Eq)]
struct A {
    i: i32,
}

#[pure]
#[ensures(result == x)]
fn id(x: A) -> A {
    x
}

#[pure]
#[ensures(result == id(id(id(id(x)))))]
fn foo(x: A) -> A {
    x
}


fn main() {
}

