// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_quantifier_instantiations_bound_global=10000 -Psmt_quantifier_instantiations_bound_trace=200 -Psmt_quantifier_instantiations_bound_trace_kind=5 -Psmt_quantifier_instantiations_bound_global_kind=20

use prusti_contracts::*;

struct T {
    val: i32
}

struct T2 {
    f1: T,
    f2: T,
}

fn construct() {
    let c = true;
    let a = T { val: 4 };
    let _b = T2 { f1: T { val: 5 }, f2: a };
}

fn construct2() {
    let a = T { val: 4 };
    let _b = (T { val: 5}, a);
}

fn copy() {
    let a = true;
    let b = !a;
}

fn main() {}
