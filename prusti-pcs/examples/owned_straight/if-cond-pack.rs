extern crate prusti_contracts;
use prusti_contracts::*;

struct K {kd: u32}

struct S {
    s1: K,
    s2: T,
}

struct T {
    td: K,
}



#[pure]
fn main() {
    let mut x: K = K {kd: 4};
    let mut y: K = K {kd: 5};
    let mut x1: K = K {kd: 5};
    let mut y1: K = K {kd: 5};
    
    let mut s: S = S {s1: x, s2: T { td: y } };
    
    if true {
        s.s1 = x1;
        s.s2.td = y1;
    }

    let w = s;
}
