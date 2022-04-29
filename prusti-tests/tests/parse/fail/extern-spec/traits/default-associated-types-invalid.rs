extern crate prusti_contracts;
use prusti_contracts::*;

trait MyTrait {
    type Item;
    fn foo(&self) -> Option<Self::Item>;
}


#[extern_spec]
trait MyTrait {
    type Item = i32; //~ ERROR: Associated types in external trait specs should not be declared

    #[ensures(result == 42)]
    fn foo(&self) -> Option<Self::Item>;
}

fn main() {
}