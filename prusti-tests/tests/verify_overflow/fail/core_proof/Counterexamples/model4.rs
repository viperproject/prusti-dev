// compile-flags: -Punsafe_core_proof=true

use prusti_contracts::*;

#[trusted]
struct VecWrapper {
    values: Vec<i32>,
}

#[model]
struct VecWrapper{
    values: Seq<i32>,
}

#[trusted]
#[ensures(result.model().values == Seq::empty())]
fn create_vec_wrapper_i32() -> VecWrapper{
    VecWrapper{
        values: vec![],
    }
}

/*
#[trusted]
#[ensures(v.model().values == Seq::concat(old(v.model().values), Seq::single(val)))]
fn push_i32(v: &mut VecWrapper, val: i32) {
    v.values.push(val);
}
*/
//Seq::empty().len() == Int::new(0)
#[requires(v.model().values.len() == Int::new(1) )]
#[ensures(v.model().values[0] == 1)]
fn test2(v: VecWrapper) {
    ()
}

fn main() {}
