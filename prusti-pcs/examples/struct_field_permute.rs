extern crate prusti_contracts;
use prusti_contracts::*;

struct T {}

struct S {t1: T, t2: T}


#[pure]
fn main() {
    let mut s = S {t1: T {}, t2: T {}};
    
    if true {
        let tmp = s.t1;
        s.t1 = s.t2;
        s.t2 = tmp;
    }

    let w = s;
}
