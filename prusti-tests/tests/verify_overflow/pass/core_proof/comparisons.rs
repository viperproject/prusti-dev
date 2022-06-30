// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_quantifier_instantiations_bound_global=10000 -Psmt_quantifier_instantiations_bound_trace=300 -Psmt_quantifier_instantiations_bound_trace_kind=20 -Plog_smt_wrapper_interaction=true -Pwrite_smt_statistics=true -Psmt_quantifier_instantiations_bound_global_kind=150 -Psmt_unique_triggers_bound=30 -Psmt_unique_triggers_bound_total=300
//
// FIXME: This example requires a large smt_quantifier_instantiations_bound_global
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
