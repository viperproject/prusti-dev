// compile-flags: -Zprint-desugared-specs -Zprint-typeckd-specs -Zhide-uuids
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"

#![feature(register_tool)]
#![register_tool(prusti)]

use prusti_contracts::*;

#[pure]
fn identity(x: u32) -> u32 { x }

#[ensures(forall(|x: u32| true))]
fn test1() {}

#[ensures(forall(|x: u32| identity(x) == x))]
fn test2() {}

#[ensures(forall(|x: u32| identity(x) == x + 1))]
fn test2() {}

fn main() {}
