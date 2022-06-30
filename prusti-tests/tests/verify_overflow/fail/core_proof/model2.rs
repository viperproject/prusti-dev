// compile-flags: -Punsafe_core_proof=true -Puse_smt_wrapper=true -Psmt_quantifier_instantiations_bound_global=10000 -Psmt_quantifier_instantiations_bound_trace=200 -Psmt_quantifier_instantiations_bound_trace_kind=20 -Psmt_quantifier_instantiations_bound_global_kind=100

use prusti_contracts::*;

#[trusted]
struct VecWrapper<T> {
    values: Vec<T>,
}

#[model]
struct VecWrapper<#[concrete] Tmp> {
    last_pushed: Tmp,
}

#[derive(Clone, Copy)]
struct Tmp {
    x: i32
}

#[trusted]
#[ensures(result.model().last_pushed.x == val )]
fn create_vec_wrapper_i32(val: i32) -> VecWrapper<Tmp>{
    let mut v = VecWrapper{
        values: Vec::new(),
    };
    let x = Tmp{x: val};
    v.values.push(x);
    v
}


#[trusted]
#[ensures(v.model().last_pushed.x == val )]
fn push_i32(v: &mut VecWrapper<Tmp>, val: i32) {
    let x = Tmp{x: val};
    v.values.push(x);
}


#[ensures(v.model().last_pushed.x == 5)] //~ ERROR postcondition might not hold.
fn len(v: VecWrapper<Tmp>){
    ()
}

fn main() {}
