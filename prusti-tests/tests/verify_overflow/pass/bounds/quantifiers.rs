use prusti_contracts::*;

#[pure]
fn check(_x: u32) -> bool { true }

#[ensures(forall(|k: u32| check(k)))]
pub fn test() {}

fn main() {}
