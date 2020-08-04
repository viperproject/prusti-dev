#![feature(register_tool)]
#![register_tool(prusti)]

use prusti_contracts::*;


#[derive(Clone,PartialEq,Eq)]
struct A {
    i: i32,
    t: (i32, i32),
}

#[pure]
fn get_value(_x: &A) -> i32 {
    _x.i + _x.t.0 + _x.t.1
}


#[requires(_x == _y)]
#[ensures(result == 2*get_value(_x))]
fn test_eq_propagation(_x: &A, _y: &A) -> i32 {
    get_value(_x) + get_value(_y)
}

fn main() {
}
