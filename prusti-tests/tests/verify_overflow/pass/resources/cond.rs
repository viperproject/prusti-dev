#![allow(dead_code, unused)]
use prusti_contracts::*;

#[resource_kind]
struct R();

#[ensures(resource(R(), 1) && (more ==> resource(R(), 1)))]
fn make(more: bool) {
    if(more) {
        produce!(resource(R(), 2))
    } else {
        produce!(resource(R(), 1))
    }
}

fn main(){}
