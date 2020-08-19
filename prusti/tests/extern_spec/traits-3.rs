#![feature(register_tool)]
#![register_tool(prusti)]

extern crate prusti_contracts;
use prusti_contracts::*;

/// This example currently fails

pub trait Max {
    #[ensures(result == 3)]
    fn max(&mut self) -> i32 { 3 }
}

pub struct Point(pub i32, pub i32);

impl Max for Point {
    fn max(&mut self) -> i32 {
        if self.0 < self.1 {
            self.0
        } else {
            self.1
        }
    }
}

#[extern_spec]
impl Point {
    #[ensures(true)]
    fn max(&mut self) -> i32;
}

fn main() {
    let mut ts = Point(3, 2);
    let x = ts.max();
    assert!(x == 3)
}
