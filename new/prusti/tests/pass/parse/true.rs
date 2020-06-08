// compile-flags: -Zprint-desugared-specs
// normalize-stdout-test: "prusti_pre_item_test\d+_[a-z0-9]{32}" -> "prusti_post_item_testNUM_UUID"
// normalize-stdout-test: "prusti_post_item_test\d+_[a-z0-9]{32}" -> "prusti_post_item_testNUM_UUID"

use prusti_contracts::*;

#[requires(true)]
fn test1() {}

#[ensures(true)]
fn test2() {}

fn test3() {
    for _ in 0..2 {
        invariant!(true)
    }
}

#[requires(true)]
#[ensures(true)]
fn test4() {
    for _ in 0..2 {
        invariant!(true)
    }
}

fn main() {}
