extern crate prusti_contracts;
use prusti_contracts::*;

trait Foo {
    #[pure]
    #[ensures(result > 0)]
    fn foo(_a: i32) -> i32;
}

struct Dummy { }

#[refine_trait_spec]
impl Foo for Dummy {
    #[pure]
    fn foo(_a: i32) -> i32 {
        5
    }
}

fn main() {
    let val = Dummy::foo(3);
    assert!(val == 5);
}
