use prusti_contracts::*;

#[require(x!=0)] //~ ERROR cannot find attribute
#[ensures(result!=0)]
fn wrong(x: i32) -> i32 {
    x
}

fn main() {}
