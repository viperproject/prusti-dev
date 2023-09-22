//@run: 101
use prusti_contracts::*;

#[trusted]
fn main() {
    let mut a = 42;
    foo(&mut a);
}

#[trusted]
fn foo(x: &mut i32) {
    *x = 1;
    // fails: *x needs to be evaluated in old state
    prusti_assert!(#[insert_runtime_check] old(*x) == 1);
}
