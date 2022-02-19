// The extern spec below introduces a specification for Max::max implemented on TestStruct
// Even though there is a TestStruct::max method, the extern spec is invalid because it is defined
// for Max::max

extern crate prusti_contracts;
use prusti_contracts::*;

pub trait Max {
    fn max(a: i32, b: i32) -> i32;
}

struct TestStruct {}

impl TestStruct {
    fn max(a: i32, b: i32) -> i32 {
        if a < b {
            b
        } else {
            a
        }
    }
}

#[extern_spec]
impl Max for TestStruct {
    #[pure]
    #[ensures(result >= a && result >= b)]
    #[ensures(result == a || result == b)]
    fn max(a: i32, b: i32) -> i32; //~ ERROR: the trait bound `TestStruct: Max` is not satisfied
}

fn main() {
    let x = TestStruct::max(1, 2);
    assert!(x == 2)
}
