use prusti_contracts::*;

#[pure]
fn something_true() -> bool {
    true
}

#[ensures(something_true() && false)]
fn client(a: u32) {}

fn main() {}
