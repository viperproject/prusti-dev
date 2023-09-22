//@run: 101
use prusti_contracts::*;

#[trusted]
fn main() {
    foo(2);
    foo(3);
}

#[insert_runtime_check]
#[requires(_x % 2 == 0)]
fn foo(_x: i32) {}
