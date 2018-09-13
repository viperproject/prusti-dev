extern crate prusti_contracts;

// ignore-test We need plugin namespaces for attributes, like "prusti::requires"

#[require="x!=0"]   //~ ERROR unsupported attribute
#[ensures="result!=0"]
fn divide(x: i32) -> i32 {
    x
}

fn main() {}
