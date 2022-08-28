// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

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
#[ensures(result.model().last_pushed == val )]
fn create_vec_wrapper_i32(val: i32) -> VecWrapper<i32>{
    VecWrapper{
        values: vec![val],
    }
}


#[trusted]
#[ensures(v.model().last_pushed == val )]
fn push_i32(v: &mut VecWrapper<i32>, val: i32) {
    v.values.push(val);
}


#[ensures(v.model().last_pushed == 5)]
fn test(v: VecWrapper<i32>){}


/*
FIXME: Details: consistency error in test2: Consistency error: No matching local 
variable _1$snapshot$0 found with type Snap$ref$Unique$trusted$m_VecWrapper$I32$, 
instead found Snap$I32. (@27.11)

#[ensures(result.model().last_pushed == 5)]
fn test2(val: i32, val2: i32) -> VecWrapper<i32>{
    let mut v = create_vec_wrapper_i32(val);
    push_i32(&mut v, val2);
    v
}
*/

fn main() {}