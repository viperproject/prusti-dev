// compile-flags: -Punsafe_core_proof=true -Psmt_quant_instantiations_bound=10000
//
// FIXME: This example requires a large smt_quant_instantiations_bound
// because most of our quantifiers used in background theories are
// reinstantiated on every push/pop cycle performed by Silicon.

use prusti_contracts::*;

fn test1() {
    let a = 4u32;
    let b = 4u32;
    let c = 5u32;
    assert!(a == b);
    assert!(a != c);
    assert!(!(a == c));
    assert!(a < c);
    assert!(a <= c);
}

fn main() {}
