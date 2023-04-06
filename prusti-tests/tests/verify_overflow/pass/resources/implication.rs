#![allow(dead_code, unused)]
use prusti_contracts::*;

#[resource]
struct Money();


#[requires(cond ==> transfers(Money(), 1))]
fn send_fungible_tokens(
    cond: bool
) { }

pub fn main(){}

