// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_quantifier_instantiations_bound_global=10000 -Psmt_quantifier_instantiations_bound_trace=200 -Psmt_quantifier_instantiations_bound_trace_kind=5 -Psmt_quantifier_instantiations_bound_global_kind=20

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
