extern crate prusti_contracts;
use prusti_contracts::*;

trait MyTrait {
    fn foo(&self) -> i32 {
        42
    }
}


#[extern_spec]
trait MyTrait {
    #[ensures(result == 42)]
    fn foo(&self) -> i32 { //~ ERROR: Default methods in external trait specs are invalid
        43
    }
}

fn main() {
}