extern crate prusti_contracts;
use prusti_contracts::*;

struct T {}

struct S {t1: T, t2: T}


#[pure]
fn main() {
    let mut s = S {t1: T {}, t2: T {}};
    
    if true {
        // Partially drop all fields of the struct 
        let tmp1 = s.t1;
        let tmp2 = s.t2;
    }

    // Unconditionally rejoin
    s.t1 = T {};
    s.t2 = T {};

    let w = s;
}
