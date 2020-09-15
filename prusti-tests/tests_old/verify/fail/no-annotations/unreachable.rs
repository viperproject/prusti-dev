#![feature(nll)]

use prusti_contracts::*;

// The end of the following function is unreachable
fn foo(x: i32) -> i32 {
    unreachable!(); //~ ERROR unreachable!(..) statement might be reachable
}

fn main(){}
