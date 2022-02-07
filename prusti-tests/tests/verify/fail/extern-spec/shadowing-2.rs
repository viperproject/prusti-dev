// The function TestStruct::max shadows Max::max (also implemented on TestStruct)
// In main, when calling the max function, Max::max is executed
// The external spec is defined on TestStruct::max, verification fails

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

fn main() {
    let x = <TestStruct as Max>::max(1, 2);
    assert!(x == 2) //~ ERROR: the asserted expression might not hold
}
