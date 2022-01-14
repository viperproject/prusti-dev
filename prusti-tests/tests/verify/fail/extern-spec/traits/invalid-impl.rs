extern crate prusti_contracts;
use prusti_contracts::*;

trait MyTrait<T> {
    fn get_value(&self) -> T;
}

#[extern_spec]
trait MyTrait<#[concrete] i32 > {
    #[ensures(result == 42)] //~ ERROR: postcondition might not hold.
    fn get_value(&self) -> i32;
}

struct Impl;
impl MyTrait<i32> for Impl {
    fn get_value(&self) -> i32 {
        43
    }
}


fn main() {
    let s = Impl{};
    assert!(MyTrait::<i32>::get_value(&s) == 42);
}