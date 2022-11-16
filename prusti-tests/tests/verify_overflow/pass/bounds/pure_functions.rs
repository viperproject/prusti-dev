use prusti_contracts::*;

#[pure]
#[ensures(result)]
fn pure1(x: u32) -> bool { x >= 0 }

#[pure]
#[ensures(result)]
fn pure2(x: usize) -> bool { x >= 0 }

fn main() {}
