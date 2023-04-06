#![allow(dead_code, unused)]
use prusti_contracts::*;

#[resource]
struct R();

#[ensures(transfers(R(), 1) && (more ==> transfers(R(), 1)))]
fn make(more: bool) {
    if(more) {
        produces!(transfers(R(), 2))
    } else {
        produces!(transfers(R(), 1))
    }
}

fn main(){}
