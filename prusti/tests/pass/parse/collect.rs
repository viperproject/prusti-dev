// compile-flags: -Zprint-desugared-specs -Zprint-collected-verification-items -Zhide-uuids
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"

#![feature(register_tool)]
#![register_tool(prusti)]

use prusti_contracts::*;

#[requires(true)]
fn test1() {}

#[ensures(true)]
fn test2() {}

fn test3() {
    let mut curr = 0;
    while curr < 2 {
        body_invariant!(true);
        curr += 1;
    }
}

#[requires(true)]
#[ensures(true)]
fn test4() {
    let mut curr = 0;
    while curr < 2 {
        body_invariant!(true);
        curr += 1;
    }
}

fn main() {}
