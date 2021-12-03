use prusti_contracts::*;

#[pure]
fn foo(_a: bool, _b: bool) {}

fn main() {
    foo(true, false);
}
