// compile-flags: -Pencode_bitvectors=true

use prusti_contracts::*;

fn bitand_1() {
    let a = 3u8;
    let b = a & 2;
    assert!(b == 2);
}

fn bitand_2() {
    let a = 3u8;
    let b = a & 2;
    assert!(b == 3);    //~ ERROR: the asserted expression might not hold
}

fn main() {}
