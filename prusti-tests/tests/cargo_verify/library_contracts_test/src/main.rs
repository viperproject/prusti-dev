extern crate prusti_contracts;
extern crate library_contracts_lib;

use library_contracts_lib::Opt;

// Demonstrating library contracts: the following specification is imported
// and thus the #[extern_spec] block is not needed

/*
use prusti_contracts::*;
#[extern_spec]
impl<T> Opt<T> {
    #[ensures(matches!(*self, Opt::OSome(_)) == result)]
    fn is_some(&self) -> bool;
}
*/

fn main() {
    let a = Opt::OSome(42);
    let b = Opt::ONone::<i32>;

    assert!(a.is_some() == true);
    assert!(b.is_some() == false);
}
