extern crate prusti_contracts;

#[pure]
#[requires="n > 0"]
#[ensures="result == 5"]
fn magic(n: i32) -> i32 { //~ ERROR postcondition
    n
}

fn main() {}
