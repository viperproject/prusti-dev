extern crate prusti_contracts;

#[pure]
#[requires="n > 0"]
#[ensures="true && (result == 5 || false)"] //~ ERROR postcondition
fn magic(n: i32) -> i32 {
    n
}

fn main() {}
