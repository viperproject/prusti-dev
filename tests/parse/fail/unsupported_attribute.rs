extern crate prusti_contracts;

#[require="x!=0"]   //~ ERROR unsupported attribute
#[ensures="result!=0"]
fn divide(x: i32) -> i32 {
    x
}

fn main() {}
