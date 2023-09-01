//@run: 101
use prusti_contracts::*;

fn main() {
    foo(3);
    foo(2);
}

#[trusted]
#[insert_runtime_check]
#[ensures(result % 2 == 0)]
fn foo(x: i32) -> i32 {
    x + 1
}
