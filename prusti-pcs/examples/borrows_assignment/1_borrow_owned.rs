extern crate prusti_contracts;
use prusti_contracts::*;

struct K {d: u32}

#[pure]
fn main() {
    let mut x: K = K {d: 0};
    let _ = &mut x;
}
