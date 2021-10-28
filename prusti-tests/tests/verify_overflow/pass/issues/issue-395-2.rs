use prusti_contracts::*;

#[derive(Copy, Clone)]
struct X(u8, u8);

#[pure]
fn f() -> X {
    X(0, 0)
}

fn main() {}
