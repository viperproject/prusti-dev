// compile-flags: -Zprint-desugared-specs -Zprint-typeckd-specs -Zskip-verify -Zhide-uuids
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"

#![feature(register_tool)]
#![register_tool(prusti)]

use prusti_contracts::*;

#[requires(forall(|a: i32| (a+a == a+a)))]
fn test3() {}

#[requires(forall(|a: i32, b: i32| (a+b == a+b && true) == (a+b == a+b)))]
fn test4() {}

#[requires(forall(|a: i32, b: i32| a+b == a+b ==> a+b == a+b))]
fn test5() {}

#[requires(forall(|a: i32| a+a == a+a, triggers=[(1,2 == 2 && true)]))]
fn test8() {}

#[requires(forall(|a: i32, b: i32| a+b == a+b, triggers=[(1,2), (1,)]))]
fn test9() {}

#[requires(forall(|a: i32, b: i32| a+b == a+b ==> a+b == a+b, triggers=[(1,2,3), (1,2), (1,)]))]
fn test10() {}

fn main() {}
