#![feature(register_tool)]
#![register_tool(prusti)]

#[prusti::requires(true)]
pub fn test1(result: u32) -> u32 { result }

fn main() {}
