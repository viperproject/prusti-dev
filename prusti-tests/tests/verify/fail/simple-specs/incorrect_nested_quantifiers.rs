use prusti_contracts::*;

#[ensures(forall(|y: u32| forall(|z: u32| y + z > old(*x))))]
fn test(x: &mut u32) {}

fn main() {}
