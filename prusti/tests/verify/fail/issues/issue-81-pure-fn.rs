extern crate prusti_contracts;

#[pure]
#[ensures="result == false"]
fn bad(n: i32) -> bool {
    false
}

#[pure]
#[requires="n > 0"]
#[ensures="bad(n)"] //~ ERROR postcondition
fn magic(n: i32) -> i32 {
    n
}

fn main() {}
