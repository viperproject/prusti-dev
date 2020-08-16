#![feature(register_tool)]
#![register_tool(prusti)]

use prusti_contracts::*;

fn test_loop(b: bool) {
    let mut g = b;
    while g {
        body_invariant!(g); // Ok, as the loop invariant is not reached after `g = false`
        g = false;
    }
}

#[trusted]
fn main() {}
