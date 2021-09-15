use prusti_contracts::*;

#[derive(Clone,PartialEq,Eq)]
struct A {
    i: i32,
}

#[requires(_x == _y)]
#[ensures(old(_x) == old(_y))]
fn get_value(_x: A, _y: A) -> A {
    _x
}

fn main() {
}
