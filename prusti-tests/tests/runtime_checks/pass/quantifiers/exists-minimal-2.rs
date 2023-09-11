//@run
use prusti_contracts::*;

#[insert_runtime_check]
#[requires(exists(|x: i8| x <= i8::MAX ==> x == i8::MAX))]
fn foo() {}

#[trusted]
fn main() {
    foo();
}
