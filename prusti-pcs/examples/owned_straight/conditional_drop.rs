extern crate prusti_contracts;
use prusti_contracts::*;

struct T {}

struct S {t1: T, t2: T}


#[pure]
fn main() {
    let mut t = T {};
    
    if true {
        // Conditionally drop
        let tmp = t;
    }

    // Unconditionally re-init
    t = T {};

    let w = t;
}
