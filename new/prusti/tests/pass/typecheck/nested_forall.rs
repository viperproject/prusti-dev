// compile-flags: -Zprint-desugared-specs -Zprint-typeckd-specs -Zskip-verify
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"

#![feature(register_tool)]
#![register_tool(prusti)]

use prusti_contracts::*;

#[requires(forall(|a: i32| forall(|a: i32| a==a)))]
fn test1() {}

#[requires(forall(|a: i32| forall(|b: i32| a==a ==> b==b)))]
fn test2() {}

#[requires(forall(|a: i32| forall(|b: i32| forall(|c: i32| a==a && b==b))))]
fn test3() {}

fn main() {}
