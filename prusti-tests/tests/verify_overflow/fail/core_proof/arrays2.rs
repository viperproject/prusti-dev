// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_quantifier_instantiations_bound_global=10000 -Psmt_quantifier_instantiations_bound_trace=8000 -Psmt_quantifier_instantiations_bound_trace_kind=1000 -Psmt_quantifier_instantiations_bound_global_kind=800 -Psmt_unique_triggers_bound=10000 -Passert_timeout=60000

use prusti_contracts::*;

fn test1() {
    let mut a = [1; 100];
    a[1] = 2;
    assert!(a[1] == 2);
    assert!(a[0] == 1);
}

fn test2() {
    let mut a = [1; 100];
    a[1] = 2;
    assert!(a[1] == 2);
    assert!(a[0] == 1);
    assert!(a[0] == 2);     //~ ERROR: the asserted expression might not hold
}

fn main() {}
