// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_quantifier_instantiations_bound_global=10000 -Psmt_quantifier_instantiations_bound_trace=200 -Psmt_quantifier_instantiations_bound_trace_kind=20 -Psmt_quantifier_instantiations_bound_global_kind=100

use prusti_contracts::*;

#[requires(true)]
#[ensures(true)]
fn test1() {
}

#[requires(true)]
#[ensures(false)]   //~ ERROR: postcondition might not hold.
fn test2() {
}

#[requires(a + a == b)]
#[ensures(2 * a == b)]
fn test3(a: u32, b: u32) {}

#[requires(a + a == b)]
#[ensures(3 * a == b)]  //~ ERROR: postcondition might not hold.
fn test4(a: u32, b: u32) {}

fn test5() {
    test3(1, 3);    //~ ERROR: precondition might not hold.
}

fn test6() {
    test4(1, 2);
    assert!(false);
}

fn main() {}

