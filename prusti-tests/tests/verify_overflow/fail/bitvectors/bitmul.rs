// compile-flags: -Pencode_bitvectors=true

use prusti_contracts::*;

fn bitmul_1() {
    let a = 1u8;
    let b = a | 2;
    let c = b * 3;
    assert!(c == 9);
}

fn bitmul_2() {
    let a = 1u8;
    let b = a | 2;
    let c = b * 3;
    assert!(c == 8);    //~ ERROR: the asserted expression might not hold
}

fn main() {}
