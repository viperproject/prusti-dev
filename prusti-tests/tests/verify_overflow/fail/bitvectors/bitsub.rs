// compile-flags: -Pencode_bitvectors=true

use prusti_contracts::*;

fn bitsub_1() {
    let a = 1u8;
    let b = a | 8;
    let c = b - 4;
    assert!(c == 5);
}

fn bitsub_2() {
    let a = 1u8;
    let b = a | 2;
    let c = b - 4;  //~ ERROR: this arithmetic operation will overflow
    assert!(c == 8);    //~ ERROR: the asserted expression might not hold
}

fn main() {}

