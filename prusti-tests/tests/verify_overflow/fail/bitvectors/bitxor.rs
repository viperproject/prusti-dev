// compile-flags: -Pencode_bitvectors=true

use prusti_contracts::*;

fn bitxor_1() {
    let a = 254u8;
    let b = a ^ 2;
    assert!(b == 252);
}

fn bitxor_2() {
    let a = 254u8;
    let b = a ^ 2;
    assert!(b == 253);  //~ ERROR: the asserted expression might not hold
}

fn main() {}

