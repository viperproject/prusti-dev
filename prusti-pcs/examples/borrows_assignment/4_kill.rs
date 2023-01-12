extern crate prusti_contracts;
use prusti_contracts::*;

struct K {d: u32}

#[pure]
fn main() {
    let mut x = &mut K {d: 0};
    let y = &mut (*x);
    x = &mut K {d: 1};
    let _ = y;
    let _ = x;
}
