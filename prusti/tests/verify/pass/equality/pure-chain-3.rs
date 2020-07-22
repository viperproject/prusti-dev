extern crate prusti_contracts;

#[derive(Clone,Copy,PartialEq,Eq)]
struct A {
    i: i32,
}

#[pure]
fn pos(x: A, j: i32) -> bool {
    x.i > j
}

#[pure]
#[requires="pos(x, 17) && pos(y, 17)"]
#[ensures="pos(result, 17) && pos(x, 17) && pos(y, 17)"]
fn first(x: A, y: A) -> A {
    x
}

fn main() {
}

