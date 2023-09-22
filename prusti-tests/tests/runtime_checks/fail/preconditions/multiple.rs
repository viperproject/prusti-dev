//@run: 101
use prusti_contracts::*;

#[trusted]
fn main() {
    foo(41, 42); // first contract fails, which should be checked second
}

// This test is about checking if multiple precondition checks are
// properly chained.
// They are currently executed bottom up. If this ever breaks, maybe
// reorder the contracts, and make sure both checks are executed
// (meaning stdout file contains to check messages)
#[insert_runtime_check]
#[requires(x == 42)]
#[insert_runtime_check]
#[requires(y == 42)]
fn foo(x: i32, y: i32) {

}
