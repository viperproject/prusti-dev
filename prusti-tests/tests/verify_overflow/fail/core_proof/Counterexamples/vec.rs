// compile-flags: -Punsafe_core_proof=true -Pcounterexample=true

use prusti_contracts::*;

use std::vec::Vec;

#[model]
struct Vec<#[concrete] i32> {
    last_pushed: i32,
}

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