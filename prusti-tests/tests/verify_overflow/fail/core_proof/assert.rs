// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;

fn assert1() {
    assert!(false);     //~ ERROR: the asserted expression might not hold
}

fn main() {}
