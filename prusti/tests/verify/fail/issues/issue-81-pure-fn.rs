extern crate prusti_contracts;

#[pure]
#[ensures="result == false"]
fn bad(n: i32) -> bool {
    false
}

#[pure]
#[requires="n > 0"]
#[ensures="bad(n)"]
fn magic(n: i32) -> i32 { //~ ERROR postcondition
    n
}

fn main() {}
