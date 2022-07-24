// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_quantifier_instantiations_bound_global=10000 -Psmt_quantifier_instantiations_bound_trace=200 -Psmt_quantifier_instantiations_bound_trace_kind=10 -Psmt_quantifier_instantiations_bound_global_kind=20

use prusti_contracts::*;

fn assert1() {
    assert!(false);     //~ ERROR: the asserted expression might not hold
}

fn assert2() {
    assert!(true);
}

fn main() {}
