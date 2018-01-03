// This test checks that specifications are type-checked.

extern crate prusti_contracts;

#[ensures="x != true"]  //~ ERROR mismatched types
pub fn first_1(x: i32, y: i32) -> i32 {
    if x != true {     //~ ERROR mismatched types
    }
    x
}

pub fn test_error_reporting(x: i32) -> bool {
    x     //~ ERROR mismatched types
}

fn main() {}

// TODO: Test parser errors.
