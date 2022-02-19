extern crate prusti_contracts;
use prusti_contracts::*;

trait Trait {
    #[pure]
    fn foo(&self) -> i32 { 1 }
}

struct Struct1;
struct Struct2;

#[refine_trait_spec]
impl Trait for Struct1 {
    #[pure]
    fn foo(&self) -> i32 {
        5
    }
}

#[refine_trait_spec]
impl Trait for Struct2 {
    #[pure]
    fn foo(&self) -> i32 {
        4
    }
}


#[requires(_arg.foo() == _x)]
fn verify<T: Trait>(_arg: T, _x: i32) {

}

fn main() {
    let s1 = Struct1 {};
    let s2 = Struct2 {};
    verify(s1, 5);
    verify(s2, 4);
}