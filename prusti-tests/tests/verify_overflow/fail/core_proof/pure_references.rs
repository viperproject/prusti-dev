// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_quantifier_instantiations_bound_global=10000 -Psmt_quantifier_instantiations_bound_trace=200 -Psmt_quantifier_instantiations_bound_trace_kind=20 -Psmt_quantifier_instantiations_bound_global_kind=100

use prusti_contracts::*;

#[pure]
fn tuple1() -> (i32, i32) {
    (1, 2)
}

#[requires(tuple1() == tuple1())]
fn test1() {}

fn test2() {
    test1();
}

#[pure]
fn first(x: (i32, i32)) -> i32 {
    x.0
}

#[requires(first(tuple1()) == tuple1().0)]
fn test3() { }

fn test4() {
    test3();
}

#[requires(first(tuple1()) == tuple1().1)]
fn test5() { }

fn test6() {
    test5();    //~ ERROR: precondition might not hold
}

#[requires(first(t) == tuple1().1)]
fn test7(t: (i32, i32)) { }

fn test8() {
    let a = (2, 4);
    test7(a);
}

fn test9() {
    let a = (3, 4);
    test7(a);    //~ ERROR: precondition might not hold
}

fn main() {}
