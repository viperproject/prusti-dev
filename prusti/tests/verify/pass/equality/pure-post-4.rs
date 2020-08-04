#![feature(register_tool)]
#![register_tool(prusti)]

use prusti_contracts::*;

#[derive(Clone,Copy,PartialEq,Eq)]
struct A {
    i: i32,
}

#[pure]
#[trusted]
#[ensures(_x == result)]
fn first(_x: A, _y: A) -> A {
    _x
}

fn main() {

    let _a = A { i: 17 };
    let _b = A { i: 42 };

    let _u = first(_a, _b);
    assert!(_u == _a);
    
    // assert!(u == b); // fails
}

