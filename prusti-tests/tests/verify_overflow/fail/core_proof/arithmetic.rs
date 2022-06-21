// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_quantifier_instantiations_bound_global=10000 -Psmt_quantifier_instantiations_bound_trace=200 -Psmt_quantifier_instantiations_bound_trace_kind=5 -Psmt_quantifier_instantiations_bound_global_kind=20

use prusti_contracts::*;

fn test1() {
    let a = 1;
    let b = 2;
    let c = a + b;
    assert!(c == 3);
}

fn test2() {
    let a = 1;
    let b = 2;
    let c = a + b;
    assert!(c == 4);    //~ ERROR the asserted expression might not hold
}

fn test3(a: i32, b: i32) -> i32 {
    a + b   //~ ERROR assertion might fail with "attempt to add with overflow"
}

fn main() {}
