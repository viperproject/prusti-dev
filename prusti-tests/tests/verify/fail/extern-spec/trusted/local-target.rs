//! `extern_spec` is only for items defined in *other* crates. Providing one for
//! a crate-local item is an error: specify it directly on its definition.

use prusti_contracts::*;

trait LocalTrait {
    fn m(&self) -> i32;
}

#[extern_spec]
trait LocalTrait {
    #[trusted]
    #[ensures(result == 0)]
    fn m(&self) -> i32; //~ ERROR: which is defined in this crate
}

fn main() {}
