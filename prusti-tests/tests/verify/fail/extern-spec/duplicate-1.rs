extern crate prusti_contracts; //~ ERROR already specified function
use prusti_contracts::*;

// FIXME: the error happens on line 23, but is reported from line 1

struct TestStruct {}

impl TestStruct {
    #[pure]
    #[ensures(result >= a && result >= b)]
    #[ensures(result == a || result == b)]
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
    let x = TestStruct::max(1, 2);
    assert!(x == 2)
}
