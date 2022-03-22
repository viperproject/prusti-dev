// The function TestStruct::max shadows Max::max (also implemented on TestStruct)
// In main, when calling the max function, TestStruct::max is executed
// The external spec is defined on TestStruct::max, verification succeeds

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
    fn max(a: i32, b: i32) -> i32;
}

#[extern_spec]
impl Max for TestStruct {
    #[pure]
    #[ensures(result >= a && result >= b)]
    #[ensures(result == a || result == b)]
    fn max(a: i32, b: i32) -> i32;
}

fn main() {
    let x = TestStruct::max(1, 2);
    let y = <TestStruct as Max>::max(1, 2);
    assert!(x == 2);
    assert!(y == 2);
}
