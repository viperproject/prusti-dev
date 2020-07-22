extern crate prusti_contracts;

#[derive(Clone,Copy,PartialEq,Eq)]
struct A {
    i: i32,
}

#[pure]
fn pos(x: A) -> bool {
    x.i > 0
}

#[pure]
#[requires="pos(x) && pos(y)"]
#[ensures="pos(result) && pos(x) && pos(y)"]
fn first(x: A, y: A) -> A {
    x
}

fn main() {
}

