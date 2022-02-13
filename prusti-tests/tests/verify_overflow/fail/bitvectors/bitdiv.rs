// compile-flags: -Pencode_bitvectors=true

use prusti_contracts::*;

fn bitdiv_1() {
    let a = 1u8;
    let b = a | 2;
    let c = b / 3;
    assert!(c == 1);
}

fn bitdiv_2() {
    let a = 1u8;
    let b = a | 2;
    let c = b / 3;
    assert!(c == 2);    //~ ERROR: the asserted expression might not hold
}

fn main() {}
