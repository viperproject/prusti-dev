#![feature(register_tool)]
#![register_tool(prusti)]

extern crate prusti_contracts_internal;

#[prusti::requires::something(true)]
fn test1() {}

#[prusti::ensures2(true)]
fn test2() {}

fn main() {}
