#![allow(dead_code, unused)]
use prusti_contracts::*;

#[resource_kind]
struct Money();


#[requires(cond ==> resource(Money(), 1))]
fn send_fungible_tokens(
    cond: bool
) { }

pub fn main(){}

