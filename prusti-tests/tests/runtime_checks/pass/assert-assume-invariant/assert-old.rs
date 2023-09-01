//@run
use prusti_contracts::*;

#[trusted]
fn main() {
    foo(&mut 42);
}

#[trusted]
fn foo(x: &mut i32) {
    *x = 1;
    prusti_assert!(old(*x) == 42);
}
