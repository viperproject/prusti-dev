// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_quantifier_instantiations_bound_global=10000 -Psmt_quantifier_instantiations_bound_trace=200 -Psmt_quantifier_instantiations_bound_trace_kind=20 -Psmt_quantifier_instantiations_bound_global_kind=100

use prusti_contracts::*;

#[trusted]
struct VecWrapper<T> {
    values: Vec<T>,
}

#[model]
struct VecWrapper<#[concrete] i32> {
    last_pushed: i32,
}

#[trusted]
#[ensures( v.model().last_pushed == val )]
fn push_i32(v: &mut VecWrapper<i32>, val: i32) {
    v.values.push(val);
}

#[ensures(v.model().last_pushed == 5)] //~ ERROR postcondition might not hold.
fn len(v: VecWrapper<i32>){
    ()
}

fn main() {}
