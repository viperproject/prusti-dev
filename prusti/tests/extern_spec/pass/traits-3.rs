#![feature(register_tool)]
#![register_tool(prusti)]

extern crate prusti_contracts;
use prusti_contracts::*;

/// This example currently fails

pub trait Max {
    #[ensures(result == 3)]
    fn max(&mut self) -> i32 { 3 }
}

pub struct Test {}

impl Max for Test {
    fn max(&mut self) -> i32 { 5 }
}

#[extern_spec]
impl Point {
    #[ensures(result == 5)]
    fn max(&mut self) -> i32;
}

fn main() {
    let mut p = Point {};
    let x = p.max();
    assert!(x == 5)
}
