extern crate prusti_contracts;
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

#[trusted]
#[ensures( result.model().last_pushed == 0 )]
fn create_vec_u32() -> Vec<u32> {
    Vec::new()
}

#[trusted]
#[ensures( v.model().last_pushed == val )]
fn push_i32(v: &mut Vec<i32>, val: i32) {
    v.push(val);
}

#[trusted]
#[ensures( v.model().last_pushed == val )]
fn push_u32(v: &mut Vec<u32>, val: u32) {
    v.push(val);
}

#[requires( v_i32.model().last_pushed == 42 )]
#[requires( v_u32.model().last_pushed == 43 )]
fn check_model(v_i32: &Vec<i32>, v_u32: &Vec<u32>) {

}

fn main() {
    let mut v_i32: Vec<i32> = Vec::new();
    let mut v_u32: Vec<u32> = Vec::new();

    push_i32(&mut v_i32, 42);
    push_u32(&mut v_u32, 43);

    check_model(&v_i32, &v_u32);
}
