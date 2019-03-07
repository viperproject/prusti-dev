extern crate prusti_contracts;

#[pure]
#[requires="n > 0"]
#[ensures="true && (result == 5 || false)"]
fn magic(n: i32) -> i32 { //~ ERROR postcondition
    n
}

fn main() {}
