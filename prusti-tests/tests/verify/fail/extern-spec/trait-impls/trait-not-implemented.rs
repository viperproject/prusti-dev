extern crate prusti_contracts;
use prusti_contracts::*;

trait MyTrait {
    fn foo(&self, x: i32) -> i32;
    fn bar(&self);
}

struct MyStruct;

#[extern_spec]
impl MyTrait for MyStruct {
    #[requires(x > 10)]
    #[ensures(result == x + 10)]
    fn foo(&self, x: i32) -> i32; //~ ERROR: the trait bound `MyStruct: MyTrait` is not satisfied [E0277]

    fn bar(&self); //~ ERROR: the trait bound `MyStruct: MyTrait` is not satisfied [E0277]
}

fn main() {

}