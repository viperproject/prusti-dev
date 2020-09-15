// This test checks that preconditions don't contain result (Issue #212)

use prusti_contracts::*;

#[requires(result > 0)]  //~ ERROR
pub fn fun() -> i32 {
    42
}

#[trusted]
fn main() {}
