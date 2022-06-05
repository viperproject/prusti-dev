// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;
/*
use  std::boxed::Box;

#[model]
struct Box<#[concrete] i32>{
    value: i32,
}

#[extern_spec]
impl Box<i32>{
    fn new<i32>(x: i32) -> Box::<i32>;
}
*/


#[ensures(!result)]
fn box_test(x: Box<i32>) -> bool {
    //let y = Box::new(x);
    *x == 0
}


fn main(){}