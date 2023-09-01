//@run
//@compile-flags: -Pcheck_overflows=false
use prusti_contracts::*;

#[trusted]
fn main() {
    println!("3 + 5 = {}", add(3, 5));
    // this one will overflow, but given the contract of
    // add, the overflow check can "safely" be eliminated,
    // meaning this should not panic!
    println!("usize::MAX + 1 = {}", add(usize::MAX, 1));
}

#[requires(x < 1000 && y < 1000)]
fn add(x: usize, y: usize) -> usize {
    x + y
}
