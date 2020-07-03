/// An adaptation of the example from
/// https://rosettacode.org/wiki/Mutual_recursion#Rust

extern crate prusti_contracts;

fn multiply(a: i32, b: i32) -> i32 {
    a * b
}

#[trusted]
fn print_i32(number: i32) {
    print!("{} ", number);
}

fn main() {
    let x = multiply(2, 5);
    print_i32(x);
}
