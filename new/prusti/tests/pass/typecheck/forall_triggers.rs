// compile-flags: -Zprint-desugared-specs -Zprint-typeckd-specs -Zskip-verify -Zhide-uuids
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"

#![feature(register_tool)]
#![register_tool(prusti)]

use prusti_contracts::*;

#[requires(forall(|a: i32| true, triggers=[(a == a,)]))]
fn test1() {}

#[requires(forall(|a: i32| forall(|b: i32| true), triggers=[(a == a && true,)]))]
fn test2() {}

#[requires(forall(|a: i32| forall(|b: i32| true, triggers=[(a == a,)]), triggers=[(a == a,)]))]
fn test3() {}

#[requires(forall(|a: i32| forall(|b: i32| true, triggers=[(a == b,)]), triggers=[(a == a && true,)]))]
fn test4() {}

fn main() {}
