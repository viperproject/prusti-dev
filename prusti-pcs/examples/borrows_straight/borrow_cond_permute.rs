extern crate prusti_contracts;
use prusti_contracts::*;

struct K {kd: u32}

struct S {
    s1: K,
    s2: K,
}


#[pure]
fn main() {
    let mut x: K = K {kd: 4};
    let mut y: K = K {kd: 5};
    
    let mut s: S = S {s1: x, s2: y};
    let mut z1 = &mut s.s1;
    let mut z2 = &mut s.s2;

    if true {
        let tmp = z1;
        z1 = z2;
        z2 = tmp;
    }

    let zz1 = z1;
    let zz2 = z2;


}
