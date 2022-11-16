use prusti_contracts::*;

#[derive(Clone,Copy,PartialEq,Eq)]
struct A {
    i: i32,
}

#[pure]
#[ensures(_x == result)]
fn get_value(_x: A, _y: A) -> A {
    _x
}

fn main() {
}
