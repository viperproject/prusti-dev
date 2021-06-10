use prusti_contracts::*;

#[derive(Clone,Copy,PartialEq,Eq)]
struct A {
    i: i32,
}

#[pure]
fn pos(_x: A) -> bool {
    _x.i > 0
}

#[pure]
#[requires(pos(_x) && pos(_y))]
#[ensures(pos(result) && pos(_x) && pos(_y))]
fn first(_x: A, _y: A) -> A {
    _x
}

fn main() {}
