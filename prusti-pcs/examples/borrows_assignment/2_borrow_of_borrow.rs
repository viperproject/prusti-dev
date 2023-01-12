extern crate prusti_contracts;
use prusti_contracts::*;

struct K {d: u32}

#[pure]
fn main() {
    let mut x: K = K {d: 0};
    let mut bx = &mut x;
    let x = &mut bx;
}
