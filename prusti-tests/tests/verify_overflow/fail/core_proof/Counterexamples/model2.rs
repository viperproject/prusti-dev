// compile-flags: -Punsafe_core_proof=true

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
/*
#[ensures(result.model().last_pushed == 5)] //~ ERROR postcondition might not hold.
fn len2(val: i32, val2: i32) -> VecWrapper<i32>{
    let mut v = create_vec_wrapper_i32(val);
    push_i32(&mut v, val2);
    v
}*/

fn main() {}
