// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;

fn test1() {
    let mut a = 1;
    let _b = &mut a;
    a = 3;
}

fn test2() {
    let mut a = 1;
    let _b = &mut a;
    assert!(a == 1);    //~ ERROR: the asserted expression might not hold
}

fn main() {}
