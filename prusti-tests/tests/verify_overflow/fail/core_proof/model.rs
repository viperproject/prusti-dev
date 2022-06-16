// compile-flags: -Punsafe_core_proof=true

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

#[requires(v.model().last_pushed != 0)]
#[ensures(v.model().last_pushed == 5)] //~ ERROR postcondition might not hold.
fn len( v: VecWrapper<i32>){
    ()// push_i32(&mut v, 5);
}

fn main() {}
