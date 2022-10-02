extern crate prusti_contracts;
use prusti_contracts::*;

// Non-copy type
struct T {}

#[pure]
fn main() {
    let mut x: T = T {};
    let mut bx = &mut x;
    let mut n = 0;
    loop {
        bx = &mut x;
        if n == 1 {
            break;
        }
        n = n + 1;
    }
    // Force a gradual expiry
    let bxx = bx;
    let xx = x;
}

