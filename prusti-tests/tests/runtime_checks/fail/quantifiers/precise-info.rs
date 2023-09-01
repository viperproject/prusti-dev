//@run:101
use prusti_contracts::*;

#[trusted]
fn main() {
    foo(30, 25);
}

#[insert_runtime_check]
#[requires(a % 2 == 0 && forall(|x: u8| a + b + x <= 100 && a + b - x > 50))]
fn foo(a: u8, b: u8) {}
