//@run
use prusti_contracts::*;

#[insert_runtime_check]
#[requires(exists(|x: i16| x <= i16::MAX ==> x == i16::MAX))]
fn foo() {}

#[trusted]
fn main() {
    foo();
}
