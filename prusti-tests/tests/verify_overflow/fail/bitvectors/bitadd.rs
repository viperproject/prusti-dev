// compile-flags: -Pencode_bitvectors=true

use prusti_contracts::*;

fn bitadd_1() {
    let a = 1u8;
    let b = a | 2;
    let c = b + 4;
    assert!(c == 7);
}

fn bitadd_2() {
    let a = 1u8;
    let b = a | 2;
    let c = b + 4;
    assert!(c == 8);    //~ ERROR: the asserted expression might not hold
}

fn main() {}
