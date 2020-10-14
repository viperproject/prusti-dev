// compile-flags: -Zprint-desugared-specs -Zprint-typeckd-specs -Zskip-verify -Zhide-uuids
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"

/// Failure cases for specification entailment parsing.

use prusti_contracts::*;

#[requires(f |= |i: i32| [ requires(i >= 5), ensures(result >= 6) ])]
fn test1<F: Fn (i32) -> i32> (f: F) {}

#[requires(g |= |i: i32| [ requires(true) ])]
fn test2<F: Fn (i32) -> i32> (g: F) {}

#[requires(f |= |i: i32| [ ensures(true) ])]
fn test3<F: Fn (i32) -> i32> (f: F) {}

#[requires(f |= |i: i32, j: i32| [ requires(i + j == 0), ensures(true) ])]
fn test4<F: Fn (i32, i32) -> i32> (f: F) {}

fn main() {}
