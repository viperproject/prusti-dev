extern crate prusti_contracts;
use prusti_contracts::*;

trait MyTrait<T> {
    fn foo(&self) -> T;
}

#[extern_spec]
trait MyTrait<i32> { //~ ERROR: Type parameters in external trait specs must be annotated with exactly one of #[generic] or #[concrete]
    #[ensures(true)]
    fn foo(&self) -> i32;
}

#[extern_spec]
trait MyTrait<T> { //~ ERROR: Type parameters in external trait specs must be annotated with exactly one of #[generic] or #[concrete]
#[ensures(true)]
fn foo(&self) -> T;
}

fn main() {
}