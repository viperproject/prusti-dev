use prusti_contracts::*;

fn main() {}

#[pure]
#[ensures(result == 1)]
fn foo() -> u32 {
    let a = [0, 1, 2];
    a[1]
}
