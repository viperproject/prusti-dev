// compile-flags: -Zprint-desugared-specs -Zprint-typeckd-specs -Zskip-verify -Zhide-uuids
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"

#![feature(register_tool)]
#![register_tool(prusti)]

use prusti_contracts::*;

#[after_expiry_if(a => a, a)]
fn test1() {}

#[after_expiry_if(a, a)]
fn test2() {}

#[after_expiry(a)]
fn test3() {}

#[after_expiry(a => a)]
fn test4() {}

#[after_expiry(
    match x {
        1 => 1,
        2 => 2
    }
)]
fn test5() {}

fn main() {}
