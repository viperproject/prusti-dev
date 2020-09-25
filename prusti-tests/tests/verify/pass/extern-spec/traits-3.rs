extern crate prusti_contracts;
use prusti_contracts::*;

// ignore-test This fails when encoding the postcondition of the trait method.

pub trait Trait {
    #[ensures(result == 3)]
    fn foo(&mut self) -> i32 { 3 }
}

pub struct Test {}

impl Trait for Test {
    fn foo(&mut self) -> i32 { 5 }
}

#[extern_spec]
impl Test {
    #[ensures(result == 5)]
    fn foo(&mut self) -> i32;
}

fn main() {
    let mut t = Test {};
    assert!(t.foo() == 5)
}
