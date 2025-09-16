#![feature(nll)]
#![feature(box_patterns)]

use prusti_contracts::*;

use std::borrow::BorrowMut;

struct T {
    v: i32
}

#[pure]
fn get_v_imm(x: &T) -> i32 {
    x.v
}

#[pure]
fn get_v_mut_pure(x: &T) -> i32 {
    x.v
}

#[ensures(result == old(x.v))]
fn get_v_mut_call(x: &mut T) -> i32 {
    x.v
}

#[ensures(result == old(x.v))]
fn get_v_val(x: T) -> i32 {
    x.v
}

#[requires(0 <= guard && guard <= 3)]
#[ensures(result == old(get_v_imm(&x)))]
fn generic_get_v(x: T, guard: i32) -> i32 {
    let mut y = x;
    match guard {
        0 => get_v_imm(&y),
        1 => get_v_mut_pure(&mut y),
        2 => get_v_mut_call(&mut y),
        3 => get_v_val(y),
        _ => unreachable!(),
    }
}

fn main() {}
