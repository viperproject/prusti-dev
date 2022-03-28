extern crate prusti_contracts;
use prusti_contracts::*;

pub trait Trait {
    fn foo(&mut self) -> i32 { 3 }
}

pub struct Test {}

impl Trait for Test {
    fn foo(&mut self) -> i32 { 5 }
}

#[extern_spec]
impl Trait for Test {
    #[ensures(result == 5)]
    fn foo(&mut self) -> i32;
}

fn main() {
    let mut t = Test {};
    assert!(t.foo() == 5)
}
