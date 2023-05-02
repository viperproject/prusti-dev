// ignore-test
#![allow(dead_code, unused)]
use prusti_contracts::*;


#[resource_kind]
pub struct Token();

#[requires(forall(|i : usize| resource(Token(), 1)))] //~ ERROR
pub fn on_recv_packet(
) {
}

fn main() {
}
