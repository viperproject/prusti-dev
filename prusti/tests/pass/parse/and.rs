// compile-flags: -Zprint-desugared-specs -Zprint-typeckd-specs -Zskip-verify -Zhide-uuids
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"

#![feature(register_tool)]
#![register_tool(prusti)]

use prusti_contracts::*;

#[requires(true && true)]
fn test1() {}

#[requires(true && true && true)]
fn test2() {}

#[requires(true && (true && true))]
fn test3() {}

#[requires((true && true) && true)]
fn test4() {}

#[requires((true && true) && (true && true))]
fn test5() {}

fn main() {}
