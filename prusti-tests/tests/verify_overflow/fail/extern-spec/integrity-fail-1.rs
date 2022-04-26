// The extern spec below introduces a specification for TestStruct::max
// but not for Max::max (implemented on TestStruct)
// We do not consider the extern spec TestStruct::max for calls to Max::max

extern crate prusti_contracts;
use prusti_contracts::*;

pub trait Max {
    fn max(a: i32, b: i32) -> i32;
}

struct TestStruct {}

impl Max for TestStruct {
    fn max(a: i32, b: i32) -> i32 {
        if a < b {
            b
        } else {
            a
        }
    }
}

#[extern_spec]
impl TestStruct {
    #[pure]
    #[ensures(result >= a && result >= b)]
    #[ensures(result == a || result == b)]
    fn max(a: i32, b: i32) -> i32; //~ ERROR: Invalid external specification
}

fn main() {
    let x = TestStruct::max(1, 2);
    assert!(x == 2)
}
