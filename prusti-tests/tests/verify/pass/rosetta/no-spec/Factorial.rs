/// An adaptation of the example from
/// https://rosettacode.org/wiki/Factorial#Rust

use prusti_contracts::*;

fn factorial_recursive (n: u64) -> u64 {
    match n {
        0 => 1,
        _ => n * factorial_recursive(n-1)
    }
}

#[trusted]
fn print_u64(number: u64) {
    println!("{} ", number);
}

fn main () {
    let mut i = 0;
    while i < 10 {
        print_u64(factorial_recursive(i));
        i += 1;
    }
}
