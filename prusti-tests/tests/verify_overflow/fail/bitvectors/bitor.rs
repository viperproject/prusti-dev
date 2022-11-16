// compile-flags: -Pencode_bitvectors=true

use prusti_contracts::*;

fn bitor_1() {
    let a = 1u8;
    let b = a | 2;
    assert!(b == 3);
}

fn bitor_2() {
    let a = 1u8;
    let b = a | 2;
    assert!(b == 1);    //~ ERROR: the asserted expression might not hold
}

fn main() {}

