// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_quantifier_instantiations_bound_global=10000 -Psmt_quantifier_instantiations_bound_trace=200 -Psmt_quantifier_instantiations_bound_trace_kind=20 -Psmt_quantifier_instantiations_bound_global_kind=100

use prusti_contracts::*;

#[pure]
fn identity(a: usize) -> usize {
    a
}

#[ensures(a == result)]
fn test1(a: usize) -> usize {
    identity(a)
}

#[ensures(a != result)] //~ ERROR postcondition might not hold.
fn test1_neg(a: usize) -> usize {
    identity(a)
}

#[ensures(a == identity(a))]
fn test2(a: usize) {}

#[pure]
fn identity2(a: usize) -> usize {
    identity(a)
}

#[ensures(a == identity2(a))]
fn test3(a: usize) {}

#[ensures(a != identity2(a))]   //~ ERROR postcondition might not hold.
fn test4(a: usize) {}

#[pure]
#[ensures(result <= n)]
fn count(n: usize) -> usize {
    if n == 0 { 0 }
    else { count(n-1) + 1 }
}

#[ensures(count(0) == 0)]
#[ensures(count(1) == 1)]
#[ensures(count(2) == 2)]
#[ensures(count(3) == 3)]
fn test5() {}

// This is expected to fail because the gas is set to 2 and proving this
// requires unfolding 3 times. If this succeeded, then it would indicate
// that we have a matching loop.
#[ensures(count(3) == 3)] //~ ERROR postcondition might not hold.
fn test6() {}

fn main() {}
