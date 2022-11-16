use prusti_contracts::*;

#[derive(Clone,Copy,PartialEq,Eq)]
struct A {
    i: i32,
}

#[pure]
fn pos(_x: A, _j: i32) -> bool {
    _x.i > _j
}

#[pure]
#[requires(pos(_x, 17) && pos(_y, 17))]
#[ensures(pos(result, 17) && pos(_x, 17) && pos(_y, 17))]
fn first(_x: A, _y: A) -> A {
    _x
}

fn main() {}
