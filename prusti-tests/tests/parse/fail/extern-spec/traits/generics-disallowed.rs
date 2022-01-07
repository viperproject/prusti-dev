extern crate prusti_contracts;
use prusti_contracts::*;

trait MyTrait<T> {
    fn foo(&self) -> T;
}

#[extern_spec]
trait MyTrait<i32> { //~ ERROR: Generics in external trait specs are not supported
    #[ensures(true)]
    fn foo(&self) -> i32;
}

#[extern_spec]
trait MyTrait<T> { //~ ERROR: Generics in external trait specs are not supported
#[ensures(true)]
fn foo(&self) -> T;
}

fn main() {
}