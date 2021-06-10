use prusti_contracts::*;

#[derive(Clone,Copy,PartialEq,Eq)]
struct A {
    i: i32,
}

#[pure]
fn id(_x: A) -> A {
    _x
}

#[requires(id(_x) == id(_y))]
#[ensures(result == _y)]
fn first(_x: A, _y: A) -> A {
    _x
}

fn main() {}
