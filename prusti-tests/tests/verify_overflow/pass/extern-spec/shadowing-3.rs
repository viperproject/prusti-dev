extern crate prusti_contracts;
use prusti_contracts::*;

trait TestTrait { fn foo() -> i32; }
struct TestStruct {}

impl TestStruct {
    fn foo() -> i32 {
        42
    }
}

impl TestTrait for TestStruct {
    fn foo() -> i32 {
        24
    }
}

#[extern_spec]
impl TestStruct {
    #[ensures(result == 42)]
    fn foo() -> i32;
}

#[extern_spec]
impl TestTrait for TestStruct {
    #[ensures(result == 24)]
    fn foo() -> i32;
}

fn main() {
    let x = TestStruct::foo();
    let y = <TestStruct as TestTrait>::foo();
    assert!(x == 42);
    assert!(y == 24);
}
