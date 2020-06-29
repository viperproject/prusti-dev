// compile-flags: -Zprint-desugared-specs -Zprint-typeckd-specs -Zskip-verify
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"

#![feature(register_tool)]
#![register_tool(prusti)]

use prusti_contracts::*;

#[requires(forall(|a: i32| (a+a == a+a) && true))]
fn test3() {}

#[requires(forall(|a: i32, b: i32| (a+b == a+b && true) == (a+b == a+b)) && true && true)]
fn test4() {}

#[requires(forall(|a: i32, b: i32| a+b == a+b ==> a+b == a+b) && true && true && true)]
fn test5() {}

#[requires(forall(|a: i32| a+a == a+a, triggers=[(1,2 == 2 && true)]) && true && true && true && true)]
fn test8() {}

#[requires(forall(|a: i32, b: i32| a+b == a+b, triggers=[(1,2), (1,)]) && true && true && true && true && true)]
fn test9() {}

#[requires(forall(|a: i32, b: i32| a+b == a+b ==> a+b == a+b, triggers=[(1,2,3), (1,2), (1,)]) && true && true && true && true && true && true)]
fn test10() {}

fn main() {}
