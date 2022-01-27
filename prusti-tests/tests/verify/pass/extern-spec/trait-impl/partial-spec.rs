extern crate prusti_contracts;
use prusti_contracts::*;

trait MyTrait {
    fn foo(&self, x: i32) -> i32;
    fn bar(&self, x: i32) -> i32;
}

struct MyStruct;
impl MyTrait for MyStruct {
    fn foo(&self, x: i32) -> i32 {
        x + 10
    }

    fn bar(&self, _x: i32) -> i32 {
        42
    }
}

#[extern_spec]
impl MyTrait for MyStruct {
    #[requires(x > 10)]
    #[ensures(result == x + 10)]
    fn foo(&self, x: i32) -> i32;
}

fn main(){
    let s = MyStruct {};
    let r = s.foo(20);
    assert!(r == 30);
}