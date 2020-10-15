use prusti_contracts::*;

#[pure]
#[trusted]
#[requires(x == 42)]
#[ensures(result == 42)]
fn id(x: u32) -> u32 {
    x
}

#[requires(x == 42)]
#[ensures(result == 40)] // ERROR
fn test(x: u32) -> u32 {
    assert!(x == 42);
    x
}

fn main() {}
