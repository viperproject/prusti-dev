// compile-flags: -Zprint-desugared-specs -Zprint-typeckd-specs -Zskip-verify -Zhide-uuids
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"

/// Tests for specification entailment parsing.

use prusti_contracts::*;

#[requires(f |=)]
fn test1<F: Fn (i32) -> i32> (f: F) {}

#[requires(f |= ||)]
fn test2<F: Fn (i32) -> i32> (f: F) {}

#[requires(f |= || 0)]
fn test3<F: Fn (i32) -> i32> (f: F) {}

#[requires(|= || [])]
fn test4<F: Fn (i32) -> i32> (f: F) {}

fn main() {}
