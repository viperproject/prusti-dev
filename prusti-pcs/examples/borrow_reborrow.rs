extern crate prusti_contracts;
use prusti_contracts::*;

struct K {kd: u32}


#[pure]
fn main() {
    let mut x: K = K {kd: 4};
    let mut z: K = K {kd: 4};
    let mut y = &mut x;
    let w = &mut y;
    y = &mut z;
    x = K {kd: 5};
}
