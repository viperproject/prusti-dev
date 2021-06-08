use prusti_contracts::*;

#[derive(Clone,Copy,PartialEq,Eq)]
struct A {
    i: i32,
}

#[pure]
fn id(_x: A) -> A {
    _x
}

#[pure]
#[requires(_x == _y)]
#[ensures(id(result) == id(_y))]
fn first(_x: A, _y: A) -> A {
    _x
}

fn main() {}
