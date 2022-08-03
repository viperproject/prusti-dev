extern crate prusti_contracts;
use prusti_contracts::*;

struct T {}

struct S {t1: T, t2: T}


#[pure]
fn main() {
    let mut s = S {t1: T {}, t2: T {}};
    
    if true {
        // Partially drop the struct
        let tmp = s.t1;
    }

    // Unconditionally rejoin
    s.t1 = T {};

    let w = s;
}
