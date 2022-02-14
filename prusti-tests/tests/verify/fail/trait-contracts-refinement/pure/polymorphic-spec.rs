extern crate prusti_contracts;
use prusti_contracts::*;

trait Trait {
    #[pure]
    fn foo(&self) -> i32 { 1 }
}

struct Struct;

#[refine_trait_spec]
impl Trait for Struct {
    #[pure]
    fn foo(&self) -> i32 {
        5
    }
}

#[requires(_arg.foo() == _x)]
fn verify<T: Trait>(_arg: T, _x: i32) {

}

fn main() {
    let s = Struct {};
    verify(s, 4); //~ ERROR: precondition might not hold
}