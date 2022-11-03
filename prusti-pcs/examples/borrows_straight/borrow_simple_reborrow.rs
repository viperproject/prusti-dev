extern crate prusti_contracts;
use prusti_contracts::*;

struct K {kd: u32}


#[pure]
fn main() {
    let mut k: K = K {kd: 4};
    let mut x = &mut k; 
    let mut y = &mut (*x);
    let yy = y; 
    let xx = x; 
    let kk = k; 
}

