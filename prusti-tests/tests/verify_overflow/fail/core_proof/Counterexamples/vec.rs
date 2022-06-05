// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;

use std::vec::Vec;

#[model]
struct Vec<#[concrete] i32> {
    last_pushed: i32,
}

#[model]
struct Vec<#[concrete] u32> {
    last_pushed: u32,
}

#[trusted]
#[ensures( result.model().last_pushed == 0 )]
fn create_vec_i32() -> Vec<i32> {
    Vec::new()
}
/*
#[trusted]
#[ensures( v.model().last_pushed == val )]
fn push_i32(v: &mut Vec<i32>, val: i32) {
    v.push(val);
}*/

/*
#[ensures(v.model().last_pushed == 5)]
fn len(a: i32){
    let mut v = create_vec_i32();
    v.push(a);
}*/
#[ensures(v.model().last_pushed == 5)]
fn len(v: Vec<i32>){
    ()
}