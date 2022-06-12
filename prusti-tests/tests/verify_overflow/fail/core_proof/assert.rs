// compile-flags: -Punsafe_core_proof=true -Psmt_quant_instantiations_bound=1000

use prusti_contracts::*;

fn assert1() {
    assert!(false);     //~ ERROR: the asserted expression might not hold
}

fn assert2() {
    assert!(true);
}

fn main() {}
