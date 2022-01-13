extern crate prusti_contracts;
use prusti_contracts::*;

trait MyTrait {
    type Item;
    fn foo(&self) -> Option<Self::Item>;
}


#[extern_spec]
trait MyTrait {
    type Item = i32; //~ ERROR: Defaults for an associated types in external trait specs are invalid

    #[ensures(result == 42)]
    fn foo(&self) -> Option<Self::Item>;
}

fn main() {
}